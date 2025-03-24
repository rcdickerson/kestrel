#lang rosette/safe

(require rosette/lib/synthax)

;; Work with 32-bit ints.
(define int32? (bitvector 32))
(define (int32 i)
  (bv i int32?))

;; BMC constraints on the choice function.
(define (check-choice choice handValue)
  (assume (bvsle (int32 2) handValue))
  (assume (bvsle handValue (int32 20)))

  (define c1 (choice handValue))
  ; Exec'ed loop.
  (assert (or (not (bvslt handValue (int32 21)))
              (bvsgt c1 (int32 0))))
  (assert (or (not (bvslt handValue (int32 21)))
              (bvsle c1 (int32 10))))
  (assert (or (not (bvslt handValue (int32 21)))
              (or (not (bvsle handValue (int32 11))) (bveq c1 (int32 10)))))
  (assert (or (not (bvslt handValue (int32 21)))
              (or (not (bvsgt handValue (int32 11))) (bveq c1 (bvsub (int32 21) handValue)))))
  ; Did not exec loop.
  (assert (or (bvslt handValue (int32 21))
              (bveq handValue (int32 21))))

  (define handValue2 (bvadd handValue c1))
  (define c2 (choice handValue2))
  ; Exec'ed loop.
  (assert (or (not (bvslt handValue2 (int32 21)))
              (bvsgt c2 (int32 0))))
  (assert (or (not (bvslt handValue2 (int32 21)))
              (bvsle c2 (int32 10))))
  (assert (or (not (bvslt handValue2 (int32 21)))
              (or (not (bvsle handValue2 (int32 11))) (bveq c2 (int32 10)))))
  (assert (or (not (bvslt handValue2 (int32 21)))
              (or (not (bvsgt handValue2 (int32 11))) (bveq c2 (bvsub (int32 21) handValue2)))))
  ; Did not exec loop.
  (assert (or (bvslt handValue2 (int32 21))
              (bveq handValue2 (int32 21))))

  (define handValue3 (bvadd handValue2 c2))
  (define c3 (choice handValue3))
  ; Exec'ed loop.
  (assert (or (not (bvslt handValue3 (int32 21)))
              (bvsgt c3 (int32 0))))
  (assert (or (not (bvslt handValue3 (int32 21)))
              (bvsle c3 (int32 10))))
  (assert (or (not (bvslt handValue3 (int32 21)))
              (or (not (bvsle handValue3 (int32 11))) (bveq c3 (int32 10)))))
  (assert (or (not (bvslt handValue3 (int32 21)))
              (or (not (bvsgt handValue3 (int32 11))) (bveq c3 (bvsub (int32 21) handValue3)))))
  ; Did not exec loop.
  (assert (or (bvslt handValue3 (int32 21))
              (bveq handValue3 (int32 21))))
  )

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
;; > time racket blackjack-bounded.rkt
;;
;; /Users/rob/code/kestrel/benchmarks/rosette/blackjack.rkt:80:1
;; (define (bv-choice hand-value)
;;   (if (bvsle hand-value (bv #x0000000a 32))
;;     (bvsub (bv #x00800044 32) (bv #x0080003a 32))
;;     (bvsub (bv #x00000015 32) hand-value)))
;; racket blackjack.rkt  0.55s user 0.09s system 83% cpu 0.776 total
