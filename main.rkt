#lang racket
(provide normalize-type)
(require "./minimize-DFA/main.rkt")

(define (base-type? T) (memv T '(Unit Bool Char Int Float)))
(define (recursive-type-var? x)
  (and (symbol? x) (not (or (base-type? x) (eqv? x 'Dyn)))))

(define (normalize-type type)
  (dfa->type
   (minimize
    (type->dfa type))))


(define (dfa->type dfa)

  (match-define (DFA Q Σ δ q0 F) dfa)
  ;(displayln dfa)

  (define ((build-type visited) q)
    (cond
      [(hash-has-key? visited q)
       (hash-ref visited q)]
      [(δ q 'Dyn)
       'Dyn]
      [else
       (define x (gensym 'x))
       `(Rec ,x ,((build-pretype (hash-set visited q x)) q))]))

  (define ((build-pretype visited) q)
    (match-let ([`(,constructor) (filter (lambda (A) (δ q A)) (set->list Σ))])
      (let ([q (δ q constructor)])
        (match constructor
          [`,B #:when (base-type? B) B]
          [`(-> ,n)
           (let ([As (for/list ([i (in-range n)])
                       ((build-type visited) (δ q `(dom ,i))))]
                 [B ((build-type visited) (δ q 'cod))])
             `(,@As -> ,B))]
          [`Ref
           (let ([A ((build-type visited) (δ q 'ref))])
             `(Ref ,A))]
          [`Vect
           (let ([A ((build-type visited) (δ q 'vect))])
             `(Vect ,A))]
          [`(Tuple ,n)
           (let ([As (for/list ([i (in-range n)])
                       ((build-type visited) (δ q `(proj ,i))))])
             `(Tuple ,@As))]))))

  ((build-type (hash)) q0))


(define (type->dfa type)
  (let* ([Q (type->states type)]
         [graph (build-graph Q type)])
    (DFA (sort (set->list Q) < #:key length)
         (type->Σ type)
         (lambda (p A)
           (hash-ref (hash-ref graph p (hash)) A #f))
         '()
         (set-add Q '()))))


;; Type to alphabet
(define (type->Σ T)

  (define (walk-pretype P)
    (match P
      [`,B
       #:when (base-type? B)
       (set B)]
      [`(,As ... -> ,B)
       (let ([As (map walk-type As)]
             [B (walk-type B)]
             [n (length As)])
         (set-union
          (set `(-> ,n))
          (for/set ([i (in-range n)])
            `(dom ,i))
          (set 'cod)
          (apply set-union B As)))]
      [`(Ref ,T)
       (let ([T (walk-type T)])
         (set-union (set 'Ref 'ref) T))]
      [`(Vect ,T)
       (let ([T (walk-type T)])
         (set-union (set 'Vect 'vect) T))]
      [`(Tuple ,@Ts)
       (let ([Ts (map walk-type Ts)]
             [n (length Ts)])
         (set-union
          (set `(Tuple ,n))
          (for/set ([i (in-range n)])
            `(proj ,i))
          (apply set-union (set) Ts)))]))

  (define (walk-type T)
    (match T
      [`Dyn
       (set 'Dyn)]
      [`,x
       #:when (recursive-type-var? x)
       (set)]
      [`(Rec ,x ,P)
       #:when (recursive-type-var? x)
       (let ([P (walk-pretype P)])
         P)]))

  (walk-type T))


;; Every state is a list of type constructors.
(define (type->states T)
  
  (define ((walk-pretype path) P)
    (match P
      [`,B
       #:when (base-type? B)
       (let ([path (cons B path)])
         (set path))]
      [`(,As ... -> ,B)
       (let* ([path (cons `(-> ,(length As)) path)]
              [As (for/list ([A As]
                             [i (in-naturals)])
                    ((walk-type (cons `(dom ,i) path)) A))]
              [B ((walk-type (cons 'cod path)) B)])
         (set-union (set path)
                    (apply set-union B As)))]
      [`(Ref ,T)
       (let* ([path (cons 'Ref path)]
              [T ((walk-type (cons 'ref path)) T)])
         (set-union (set path)
                    T))]
      [`(Vect ,T)
       (let* ([path (cons 'Vect path)]
              [T ((walk-type (cons 'vect path)) T)])
         (set-union (set path)
                    T))]
      [`(Tuple ,@Ts)
       (let* ([path (cons `(Tuple ,(length Ts)) path)]
              [Ts (for/list ([T Ts]
                             [i (in-naturals)])
                    ((walk-type (cons `(proj ,i) path)) T))])
         (set-union (set path)
                    (apply set-union (set) Ts)))]))

  (define ((walk-type path) T)
    (match T
      [`Dyn
       (set path (cons 'Dyn path))]
      [`,x
       #:when (recursive-type-var? x)
       (set)]
      [`(Rec ,x ,P)
       #:when (recursive-type-var? x)
       (set-add ((walk-pretype path) P) path)]))

  ((walk-type '()) T))


;; build the connection between states
(define (build-graph Q T)
  (define graph
    (for/hash ([q Q])
      (values q (make-hash))))

  (define (link! path1 s path2)
    (hash-set! (hash-ref graph path1) s path2))

  (define (natural-link! path s)
    (link! path s (cons s path)))

  (define ((walk-pretype env path) P)
    (match P
      [`,B
       #:when (base-type? B)
       (natural-link! path B)]
      [`(,As ... -> ,B)
       (natural-link! path `(-> ,(length As)))
       (let* ([path (cons `(-> ,(length As)) path)]
              [As (for/list ([A As]
                             [i (in-naturals)])
                    ((walk-type env (cons `(dom ,i) path)) A))]
              [B ((walk-type env (cons 'cod path)) B)])
         (void))]
      [`(Ref ,T)
       (natural-link! path `Ref)
       (let* ([path (cons 'Ref path)]
              [T ((walk-type env (cons 'ref path)) T)])
         (void))]
      [`(Vect ,T)
       (natural-link! path `Vect)
       (let* ([path (cons 'Vect path)]
              [T ((walk-type env (cons 'vect path)) T)])
         (void))]
      [`(Tuple ,@Ts)
       (natural-link! path `(Tuple ,(length Ts)))
       (let* ([path (cons `(Tuple ,(length Ts)) path)]
              [Ts (for/list ([T Ts]
                             [i (in-naturals)])
                    ((walk-type env (cons `(proj ,i) path)) T))])
         (void))]))

  (define ((walk-type env path) T)
    (match T
      [`Dyn
       (unless (null? path)
         (link! (cdr path) (car path) path))
       (natural-link! path 'Dyn)]
      [`,x
       #:when (recursive-type-var? x)
       (link! (cdr path) (car path) (hash-ref env x))]
      [`(Rec ,x ,P)
       #:when (recursive-type-var? x)
       (unless (null? path)
         (link! (cdr path) (car path) path))
       ((walk-pretype (hash-set env x path) path) P)]))

  ((walk-type (hash) '()) T)

  graph)
