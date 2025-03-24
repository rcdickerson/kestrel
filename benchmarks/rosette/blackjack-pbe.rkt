#lang rosette/safe

(require rosette/lib/synthax)

;; Work with 32-bit ints.
(define int32? (bitvector 32))
(define (int32 i)
  (bv i int32?))

;; Choice I/O examples.
(define (choice-examples choice)
  (assert (bveq (int32 10) (choice (int32 2))))
  (assert (bveq (int32 10) (choice (int32 10))))
  (assert (bveq (int32 7)  (choice (int32 14))))
  (assert (bveq (int32 1)  (choice (int32 20)))))

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

;; Synthesize a choice function.
(define sol
    (synthesize
     #:forall    (list hand-value)
     #:guarantee (choice-examples bv-choice)))
(print-forms sol)

;; Output:
;;
;; > time racket blackjack-pbe.rkt
;;
;; /Users/rob/code/kestrel/benchmarks/rosette/blackjack-pbe.rkt:35:0
;; (define (bv-choice hand-value)
;;   (if (bvsle (bv #x0000000b 32) hand-value)
;;     (bvsub (bv #x00000015 32) hand-value)
;;     (bvsub (bv #x0000000a 32) (bv #x00000000 32))))
;; racket blackjack-pbe.rkt  0.35s user 0.07s system 93% cpu 0.443 total
