#lang racket
(require pict)
(provide DFA minimize dfa->pict)
#|

DFA definition is borrowed from wikipedia:


A deterministic finite automaton M {\displaystyle M} M is a 5-tuple,
( Q , Σ , δ , q 0 , F ), consisting of 
- a finite set of states Q
- a finite set of input symbols called the alphabet Σ
- a transition function δ : Q × Σ → Q
- an initial or start state q0 ∈ Q
- a set of accept states F ⊆ Q

|#


(struct DFA (Q Σ δ q0 F)
  #:transparent)


(define (minimize dfa)
  (minimize-dfa (DFA-Q dfa)
                (DFA-Σ dfa)
                (DFA-δ dfa)
                (DFA-q0 dfa)
                (DFA-F dfa)))


(define (iter-to-fix f v)
  (let ([u (f v)])
    (if (equal? u v) v
        (iter-to-fix f u))))


(define ((mark Q Σ δ) diff)
  (for*/fold ([diff diff])
             ([p Q]
              [q Q]
              [A Σ])
    (if (or (set-member? diff (set p q))
            (and (not (δ p A)) (not (δ q A)))
            (and (δ p A) (δ q A)
                 (not (set-member? diff (set (δ p A) (δ q A))))))
        diff
        (set-add diff (set p q)))))


(define (minimize-dfa Q Σ δ q0 F)
  (define diff0
    (for*/fold ([diff (set)])
               ([p Q]
                [q Q])
      (if (xor (set-member? F p) (set-member? F q))
          (set-add diff (set p q))
          diff)))
  (define diff1 (iter-to-fix (mark Q Σ δ) diff0))
  (define Q=>Q^ (make-Q=>Q^ Q diff1))
  (define Q^ (remove-duplicates	(hash-values Q=>Q^)))
  (DFA (let ([q0^ (hash-ref Q=>Q^ q0)])
         (cons q0^ (remove q0^ Q^)))  ;; move q0^ to the first cdr
       Σ
       (lambda (p^ A)
         (for/first ([p p^]
                     #:when (δ p A))
           (hash-ref Q=>Q^ (δ p A))))
       (hash-ref Q=>Q^ q0)
       (for/set ([p^ Q^]
                 #:when (for/or ([p p^])
                          (set-member? F p)))
         p^)))


(define (make-Q=>Q^ Q diff)
  (for*/fold ([Q=>Q^ (hash)])
             ([p Q]
              [q Q])
    (if (set-member? diff (set p q))
        Q=>Q^
        (hash-update
         Q=>Q^
         p
         (lambda (qs)
           (set-add qs q))
         (set)))))


(define (dfa->pict dfa)
  (match-let ([(DFA Q Σ δ q0 F) dfa])
    (let ([p=>pp (for/hash ([p Q])
                   (let ([pp (cc-superimpose
                              (if (set-member? F p)
                                  (cc-superimpose (circle 50)
                                                  (circle 40))
                                  (circle 50))
                              (text (format "~a" (index-of Q p))))])
                     (values p pp)))])
      (displayln p=>pp)
      (let ([big (put-pps (integer-sqrt (set-count Q))
                          ;; always put initial state at the top-left corner
                          (for/list ([p Q])
                            (hash-ref p=>pp p)))])
        (for*/fold ([big big])
                   ([p Q]
                    [a Σ])
          (let ([?q (δ p a)])
            (if ?q
                (if #f big
                    (pin-arrow-line
                     10 big
                     (hash-ref p=>pp p) (list-ref (list lc-find rc-find ct-find cb-find)
                                                  (random 4))
                     (hash-ref p=>pp ?q) (list-ref (list lc-find rc-find ct-find cb-find)
                                                   (random 4))
                     #:label (text (format "~a" a))
                     #:solid? #f))
                big)))))))

(define (put-pps n pps)
  (let loop ([ppss (let loop ([pps pps])
                     (cond
                       [(null? pps) '()]
                       [else
                        (let-values ([(l1 l2) (split-at pps n)])
                          (cons l1 (loop l2)))]))])
    (cond
      [(null? ppss) (blank)]
      [else (vl-append 50
                       (apply hc-append 50 (append (car ppss) (list (blank))))
                       (loop (cdr ppss)))])))


#;
(begin
  
  (define dfa-1
    (DFA (set 'A)
         (set 0)
         (lambda (q A) 'A)
         'A
         (set 'A)))

  (define dfa-2
    (DFA (set 'A 'B)
         (set 0)
         (lambda (q A)
           (case q
             [(A) 'B]
             [else #f]))
         'A
         (set 'B)))

  (dfa->pict dfa-1)
  (dfa->pict dfa-2)

  (define dfa-3
    (DFA '(a b c d e f)
         (set 0 1)
         (lambda (q A)
           (match `(,q ,A)
             ['(a 0) 'b]
             ['(a 1) 'c]
             ['(b 0) 'a]
             ['(b 1) 'd]
             ['(c 0) 'e]
             ['(c 1) 'f]
             ['(d 0) 'e]
             ['(d 1) 'f]
             [`(e 0) 'e]
             ['(e 1) 'f]
             [`(f ,x) 'f]))
         'a
         (list->set '(c d e))))

  (dfa->pict dfa-3)

  (define dfa-4 (minimize dfa-3))
  (dfa->pict dfa-4))