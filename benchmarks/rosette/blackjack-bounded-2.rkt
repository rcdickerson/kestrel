#lang rosette/safe

(require rosette/lib/synthax)

;; Work with 32-bit ints.
(define int32? (bitvector 32))
(define (int32 i)
  (bv i int32?))

(define (play choice handValue1)
  (if (bvslt handValue1 (int32 21))
      (begin
        (define c1 (choice handValue1))
        (assert (and (bvsgt c1 (int32 0) (bvsle c1 (int32 10)))))
        (define handValue2 (bvadd handValue1 c1))
        (if (bvslt handValue2 (int32 21))
            (begin
              (define c2 (choice handValue2))
              (assert (and (bvsgt c2 (int32 0) (bvsle c2 (int32 10)))))
              (define handValue3 (bvadd handValue2 c2))
              (if (bvslt handValue3 (int32 21))
                  (begin
                    (define c3 (choice handValue3))
                    (assert (and (bvsgt c3 (int32 0) (bvsle c3 (int32 10)))))
                    (define handValue4 (bvadd handValue3 c3))
                    (if (bvslt handValue4 (int32 21))
                        (assert false)
                        (handValue4)))
                  (handValue3)))
            (handValue2)))
      (handValue1)))

(define (check-choice choice handValue1)
  (assume (bvsle (int32 2) handValue1))
  (assume (bvsle handValue1 (int32 20)))
  (define handValue2 (play choice handValue1))
  (assert (bveq handValue2 (int32 21))))

;; Synthesis grammar.
(define-grammar (choice-grammar hand-value)
  [expr
   (choose (aexp) (if (bexp) (aexp) (aexp)))]
  [bexp
   (choose (bvsle (aexp) (aexp)) ((b-bop-b) (bexp) (bexp)) (bvnot (bexp)))]
  [b-bop-b
   (choose bvand bvor)]
  [b-bop-a
   (choose bvsle bvslt bveq)]
  [aexp
   (choose hand-value (?? int32?)
           ((a-bop) (aexp) (aexp)))]
  [a-bop
   (choose bvadd bvsub)]
  )

 (define-symbolic hand-value int32?)
 (define (bv-choice hand-value)
   (choice-grammar hand-value #:depth 2))

;; Synthesize a choice funciton.
(define sol
    (synthesize
     #:forall    (list hand-value)
     #:guarantee (check-choice bv-choice hand-value)))
(print-forms sol)

;; Output:
;;
;; > time racket blackjack-bounded-2.rkt
;;
;; sat-model: contract violation
;;   expected: sat?
;;   given: (unsat)
;;   context...:
;;    sat-model
;;    /opt/homebrew/opt/minimal-racket/share/racket/pkgs/rosette/rosette/lib/synthax.rkt:243:0: generate-forms
;;    /opt/homebrew/opt/minimal-racket/share/racket/pkgs/rosette/rosette/lib/synthax.rkt:296:0: print-forms
;;    body of "/Users/rob/code/kestrel/benchmarks/rosette/blackjack-bounded-2.rkt"
