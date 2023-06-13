(set-info :original "./results/chc/bytecode/antonopoulos/unaligned/loop-tiling.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@_4 (Int Int Int Int Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@.preheader1 (Int (Array Int Int) Int Int Int Int (Array Int Int) Int ))
(declare-rel main@_8 (Int (Array Int Int) Int Int Int Int Int (Array Int Int) Int ))
(declare-rel main@.lr.ph (Int Int (Array Int Int) Int (Array Int Int) Int ))
(declare-rel main@_20 (Int Int Int (Array Int Int) Int (Array Int Int) Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_32_0 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%_22_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@%.02.i4_2 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%.0.i6_2 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_4_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.0.i6_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.0.i6_1 Int )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%_6_0 Int )
(declare-var main@_4_1 Bool )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%.01.i5_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%.01.i5_1 Int )
(declare-var main@_8_0 Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%.02.i4_0 Int )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%.02.i4_1 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_10_0 Int )
(declare-var main@_12_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%.01.i5_2 Int )
(declare-var main@_8_1 Bool )
(declare-var main@.preheader.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.03.i8_0 Int )
(declare-var main@%.03.i8_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@_20_0 Bool )
(declare-var main@%.04.i37_0 Int )
(declare-var main@%.04.i37_1 Int )
(declare-var main@%_21_0 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%.03.i8_2 Int )
(declare-var main@_23_0 Bool )
(declare-var main@_20_1 Bool )
(declare-var main@%.04.i37_2 Int )
(declare-var |tuple(main@.preheader_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@_23_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm7_0 main@%sm8_0))
(rule (=> (and (main@entry main@%sm7_0 main@%sm8_0)
         true
         (= main@%sm_0 main@%sm8_0)
         (= main@%sm4_0 main@%sm7_0)
         (= main@%_0_0 (= main@%loop.bound_0 9))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (= main@%_3_0 (= main@%loop.bound3_0 99))
         main@%_3_0
         true
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound2_0
                     main@%loop.bound1_0
                     main@%loop.bound3_0
                     main@%sm4_0
                     main@%sm_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm4_0
                          main@%sm_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound2_0
                     main@%loop.bound1_0
                     main@%loop.bound3_0
                     main@%sm4_0
                     main@%sm_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm4_0
                          main@%sm_0)
         true
         (=> main@_4_0 (and main@_4_0 main@empty.loop_0))
         (=> (and main@_4_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_4_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_0 main@%sm_0))
         (=> (and main@_4_0 main@empty.loop_0) (= main@%.0.i6_0 0))
         (=> (and main@_4_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@_4_0 main@empty.loop_0) (= main@%.0.i6_1 main@%.0.i6_0))
         main@_4_0)
    (main@_4 @a_1_0
             @a_2_0
             main@%loop.bound_0
             main@%loop.bound2_0
             main@%loop.bound1_0
             main@%.0.i6_1
             main@%shadow.mem.0.0_1
             main@%loop.bound3_0
             main@%sm4_0)))
(rule (let ((a!1 (and (main@_4 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound2_0
                         main@%loop.bound1_0
                         main@%.0.i6_0
                         main@%shadow.mem.0.0_0
                         main@%loop.bound3_0
                         main@%sm4_0)
                true
                (= main@%_5_0 (+ @a_1_0 (* 0 400) (* main@%.0.i6_0 4)))
                (or (<= @a_1_0 0) (> main@%_5_0 0))
                (> @a_1_0 0)
                (= main@%sm5_0 (store main@%shadow.mem.0.0_0 main@%_5_0 0))
                (= main@%_6_0 (+ main@%.0.i6_0 1))
                (= main@%_7_0 (< main@%.0.i6_0 main@%loop.bound3_0))
                (=> main@_4_1 (and main@_4_1 main@_4_0))
                (=> (and main@_4_1 main@_4_0) main@%_7_0)
                (=> (and main@_4_1 main@_4_0)
                    (= main@%shadow.mem.0.0_1 main@%sm5_0))
                (=> (and main@_4_1 main@_4_0) (= main@%.0.i6_1 main@%_6_0))
                (=> (and main@_4_1 main@_4_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@_4_1 main@_4_0) (= main@%.0.i6_2 main@%.0.i6_1))
                main@_4_1)))
  (=> a!1
      (main@_4 @a_1_0
               @a_2_0
               main@%loop.bound_0
               main@%loop.bound2_0
               main@%loop.bound1_0
               main@%.0.i6_2
               main@%shadow.mem.0.0_2
               main@%loop.bound3_0
               main@%sm4_0))))
(rule (let ((a!1 (and (main@_4 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound2_0
                         main@%loop.bound1_0
                         main@%.0.i6_0
                         main@%shadow.mem.0.0_0
                         main@%loop.bound3_0
                         main@%sm4_0)
                true
                (= main@%_5_0 (+ @a_1_0 (* 0 400) (* main@%.0.i6_0 4)))
                (or (<= @a_1_0 0) (> main@%_5_0 0))
                (> @a_1_0 0)
                (= main@%sm5_0 (store main@%shadow.mem.0.0_0 main@%_5_0 0))
                (= main@%_6_0 (+ main@%.0.i6_0 1))
                (= main@%_7_0 (< main@%.0.i6_0 main@%loop.bound3_0))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_4_0))
                (=> (and main@.preheader1_0 main@_4_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@_4_0)
                    (= main@%shadow.mem.4.0_0 main@%sm4_0))
                (=> (and main@.preheader1_0 main@_4_0) (= main@%.01.i5_0 0))
                (=> (and main@.preheader1_0 main@_4_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader1_0 main@_4_0)
                    (= main@%.01.i5_1 main@%.01.i5_0))
                main@.preheader1_0)))
  (=> a!1
      (main@.preheader1 @a_1_0
                        main@%sm5_0
                        @a_2_0
                        main@%loop.bound_0
                        main@%.01.i5_1
                        main@%loop.bound2_0
                        main@%shadow.mem.4.0_1
                        main@%loop.bound1_0))))
(rule (=> (and (main@.preheader1 @a_1_0
                           main@%sm5_0
                           @a_2_0
                           main@%loop.bound_0
                           main@%.01.i5_0
                           main@%loop.bound2_0
                           main@%shadow.mem.4.0_0
                           main@%loop.bound1_0)
         true
         (=> main@_8_0 (and main@_8_0 main@.preheader1_0))
         (=> (and main@_8_0 main@.preheader1_0)
             (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
         (=> (and main@_8_0 main@.preheader1_0) (= main@%.02.i4_0 0))
         (=> (and main@_8_0 main@.preheader1_0)
             (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
         (=> (and main@_8_0 main@.preheader1_0)
             (= main@%.02.i4_1 main@%.02.i4_0))
         main@_8_0)
    (main@_8 @a_1_0
             main@%sm5_0
             @a_2_0
             main@%loop.bound_0
             main@%.01.i5_0
             main@%loop.bound2_0
             main@%.02.i4_1
             main@%shadow.mem.4.1_1
             main@%loop.bound1_0)))
(rule (let ((a!1 (and (main@_8 @a_1_0
                         main@%sm5_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%.01.i5_0
                         main@%loop.bound2_0
                         main@%.02.i4_0
                         main@%shadow.mem.4.1_0
                         main@%loop.bound1_0)
                true
                (= main@%_9_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i5_0 40)
                      (* main@%.02.i4_0 4)))
                (or (<= @a_2_0 0) (> main@%_9_0 0))
                (> @a_2_0 0)
                (= main@%sm6_0 (store main@%shadow.mem.4.1_0 main@%_9_0 0))
                (= main@%_10_0 (+ main@%.02.i4_0 1))
                (= main@%_11_0 (< main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@_12_0 (and main@_12_0 main@_8_0))
                (=> (and main@_12_0 main@_8_0) (not main@%_11_0))
                (=> main@_12_0 (= main@%_13_0 (+ main@%.01.i5_0 1)))
                (=> main@_12_0
                    (= main@%_14_0 (< main@%.01.i5_0 main@%loop.bound2_0)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_12_0))
                (=> (and main@.preheader1_0 main@_12_0) main@%_14_0)
                (=> (and main@.preheader1_0 main@_12_0)
                    (= main@%shadow.mem.4.0_0 main@%sm6_0))
                (=> (and main@.preheader1_0 main@_12_0)
                    (= main@%.01.i5_1 main@%_13_0))
                (=> (and main@.preheader1_0 main@_12_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader1_0 main@_12_0)
                    (= main@%.01.i5_2 main@%.01.i5_1))
                main@.preheader1_0)))
  (=> a!1
      (main@.preheader1 @a_1_0
                        main@%sm5_0
                        @a_2_0
                        main@%loop.bound_0
                        main@%.01.i5_2
                        main@%loop.bound2_0
                        main@%shadow.mem.4.0_1
                        main@%loop.bound1_0))))
(rule (let ((a!1 (and (main@_8 @a_1_0
                         main@%sm5_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%.01.i5_0
                         main@%loop.bound2_0
                         main@%.02.i4_0
                         main@%shadow.mem.4.1_0
                         main@%loop.bound1_0)
                true
                (= main@%_9_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i5_0 40)
                      (* main@%.02.i4_0 4)))
                (or (<= @a_2_0 0) (> main@%_9_0 0))
                (> @a_2_0 0)
                (= main@%sm6_0 (store main@%shadow.mem.4.1_0 main@%_9_0 0))
                (= main@%_10_0 (+ main@%.02.i4_0 1))
                (= main@%_11_0 (< main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@_8_1 (and main@_8_1 main@_8_0))
                (=> (and main@_8_1 main@_8_0) main@%_11_0)
                (=> (and main@_8_1 main@_8_0)
                    (= main@%shadow.mem.4.1_1 main@%sm6_0))
                (=> (and main@_8_1 main@_8_0) (= main@%.02.i4_1 main@%_10_0))
                (=> (and main@_8_1 main@_8_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> (and main@_8_1 main@_8_0) (= main@%.02.i4_2 main@%.02.i4_1))
                main@_8_1)))
  (=> a!1
      (main@_8 @a_1_0
               main@%sm5_0
               @a_2_0
               main@%loop.bound_0
               main@%.01.i5_0
               main@%loop.bound2_0
               main@%.02.i4_2
               main@%shadow.mem.4.1_2
               main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_9_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.01.i5_0 40)
                 (* main@%.02.i4_0 4))))
      (a!2 (=> main@.preheader.preheader_0
               (= main@%_15_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_17_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_8 @a_1_0
                         main@%sm5_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%.01.i5_0
                         main@%loop.bound2_0
                         main@%.02.i4_0
                         main@%shadow.mem.4.1_0
                         main@%loop.bound1_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_9_0 0))
                (> @a_2_0 0)
                (= main@%sm6_0 (store main@%shadow.mem.4.1_0 main@%_9_0 0))
                (= main@%_10_0 (+ main@%.02.i4_0 1))
                (= main@%_11_0 (< main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@_12_0 (and main@_12_0 main@_8_0))
                (=> (and main@_12_0 main@_8_0) (not main@%_11_0))
                (=> main@_12_0 (= main@%_13_0 (+ main@%.01.i5_0 1)))
                (=> main@_12_0
                    (= main@%_14_0 (< main@%.01.i5_0 main@%loop.bound2_0)))
                (=> main@.preheader.preheader_0
                    (and main@.preheader.preheader_0 main@_12_0))
                (=> (and main@.preheader.preheader_0 main@_12_0)
                    (not main@%_14_0))
                true
                a!2
                (=> main@.preheader.preheader_0
                    (or (<= @a_1_0 0) (> main@%_15_0 0)))
                (=> main@.preheader.preheader_0
                    (= main@%_16_0 (select main@%sm5_0 main@%_15_0)))
                (=> main@.preheader.preheader_0 a!3)
                (=> main@.preheader.preheader_0
                    (or (<= @a_2_0 0) (> main@%_17_0 0)))
                (=> main@.preheader.preheader_0
                    (= main@%_18_0 (select main@%sm6_0 main@%_17_0)))
                (=> main@.preheader.preheader_0
                    (= main@%_19_0 (= main@%_16_0 main@%_18_0)))
                (=> main@.lr.ph_0
                    (and main@.lr.ph_0 main@.preheader.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader.preheader_0) main@%_19_0)
                (=> (and main@.lr.ph_0 main@.preheader.preheader_0)
                    (= main@%.03.i8_0 0))
                (=> (and main@.lr.ph_0 main@.preheader.preheader_0)
                    (= main@%.03.i8_1 main@%.03.i8_0))
                main@.lr.ph_0)))
  (=> a!4
      (main@.lr.ph main@%.03.i8_1
                   @a_1_0
                   main@%sm5_0
                   @a_2_0
                   main@%sm6_0
                   main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_9_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.01.i5_0 40)
                 (* main@%.02.i4_0 4))))
      (a!2 (=> main@.preheader.preheader_0
               (= main@%_15_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_17_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_8 @a_1_0
                         main@%sm5_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%.01.i5_0
                         main@%loop.bound2_0
                         main@%.02.i4_0
                         main@%shadow.mem.4.1_0
                         main@%loop.bound1_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_9_0 0))
                (> @a_2_0 0)
                (= main@%sm6_0 (store main@%shadow.mem.4.1_0 main@%_9_0 0))
                (= main@%_10_0 (+ main@%.02.i4_0 1))
                (= main@%_11_0 (< main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@_12_0 (and main@_12_0 main@_8_0))
                (=> (and main@_12_0 main@_8_0) (not main@%_11_0))
                (=> main@_12_0 (= main@%_13_0 (+ main@%.01.i5_0 1)))
                (=> main@_12_0
                    (= main@%_14_0 (< main@%.01.i5_0 main@%loop.bound2_0)))
                (=> main@.preheader.preheader_0
                    (and main@.preheader.preheader_0 main@_12_0))
                (=> (and main@.preheader.preheader_0 main@_12_0)
                    (not main@%_14_0))
                true
                a!2
                (=> main@.preheader.preheader_0
                    (or (<= @a_1_0 0) (> main@%_15_0 0)))
                (=> main@.preheader.preheader_0
                    (= main@%_16_0 (select main@%sm5_0 main@%_15_0)))
                (=> main@.preheader.preheader_0 a!3)
                (=> main@.preheader.preheader_0
                    (or (<= @a_2_0 0) (> main@%_17_0 0)))
                (=> main@.preheader.preheader_0
                    (= main@%_18_0 (select main@%sm6_0 main@%_17_0)))
                (=> main@.preheader.preheader_0
                    (= main@%_19_0 (= main@%_16_0 main@%_18_0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader.preheader_0)
                    (not main@%_19_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!4 main@verifier.error.split))))
(rule (=> (and (main@.lr.ph main@%.03.i8_0
                      @a_1_0
                      main@%sm5_0
                      @a_2_0
                      main@%sm6_0
                      main@%loop.bound_0)
         true
         (=> main@_20_0 (and main@_20_0 main@.lr.ph_0))
         (=> (and main@_20_0 main@.lr.ph_0) (= main@%.04.i37_0 0))
         (=> (and main@_20_0 main@.lr.ph_0) (= main@%.04.i37_1 main@%.04.i37_0))
         main@_20_0)
    (main@_20 main@%.04.i37_1
              main@%.03.i8_0
              @a_1_0
              main@%sm5_0
              @a_2_0
              main@%sm6_0
              main@%loop.bound_0)))
(rule (let ((a!1 (=> main@.preheader_0
               (= main@%_34_0 (+ @a_1_0 (* 0 400) (* main@%_33_0 4)))))
      (a!2 (=> main@.preheader_0
               (= main@%_36_0 (+ @a_2_0 (* 0 400) (* main@%_31_0 40) (* 0 4))))))
(let ((a!3 (and (main@_20 main@%.04.i37_0
                          main@%.03.i8_0
                          @a_1_0
                          main@%sm5_0
                          @a_2_0
                          main@%sm6_0
                          main@%loop.bound_0)
                true
                (= main@%_21_0 (+ main@%.04.i37_0 1))
                (= main@%_22_0 (< main@%.04.i37_0 main@%loop.bound_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@_20_0))
                (=> (and main@.preheader_0 main@_20_0) (not main@%_22_0))
                (=> main@.preheader_0 (= main@%_31_0 (+ main@%.03.i8_0 1)))
                (=> main@.preheader_0 (= main@%_32_0 (< main@%.03.i8_0 9)))
                (=> main@.preheader_0 main@%_32_0)
                (=> main@.preheader_0 (= main@%_33_0 (* main@%_31_0 10)))
                a!1
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0
                    (= main@%_35_0 (select main@%sm5_0 main@%_34_0)))
                a!2
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_36_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%_37_0 (select main@%sm6_0 main@%_36_0)))
                (=> main@.preheader_0
                    (= main@%_38_0 (= main@%_35_0 main@%_37_0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_38_0)
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.03.i8_1 main@%_31_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.03.i8_2 main@%.03.i8_1))
                main@.lr.ph_0)))
  (=> a!3
      (main@.lr.ph main@%.03.i8_2
                   @a_1_0
                   main@%sm5_0
                   @a_2_0
                   main@%sm6_0
                   main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@_23_0
               (= main@%_26_0 (+ @a_1_0 (* 0 400) (* main@%_25_0 4)))))
      (a!2 (=> main@_23_0
               (= main@%_28_0
                  (+ @a_2_0 (* 0 400) (* main@%.03.i8_0 40) (* main@%_21_0 4))))))
(let ((a!3 (and (main@_20 main@%.04.i37_0
                          main@%.03.i8_0
                          @a_1_0
                          main@%sm5_0
                          @a_2_0
                          main@%sm6_0
                          main@%loop.bound_0)
                true
                (= main@%_21_0 (+ main@%.04.i37_0 1))
                (= main@%_22_0 (< main@%.04.i37_0 main@%loop.bound_0))
                (=> main@_23_0 (and main@_23_0 main@_20_0))
                (=> (and main@_23_0 main@_20_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.04.i37_0 11)))
                a!1
                (=> main@_23_0 (or (<= @a_1_0 0) (> main@%_26_0 0)))
                (=> main@_23_0 (> @a_1_0 0))
                (=> main@_23_0 (= main@%_27_0 (select main@%sm5_0 main@%_26_0)))
                a!2
                (=> main@_23_0 (or (<= @a_2_0 0) (> main@%_28_0 0)))
                (=> main@_23_0 (> @a_2_0 0))
                (=> main@_23_0 (= main@%_29_0 (select main@%sm6_0 main@%_28_0)))
                (=> main@_23_0 (= main@%_30_0 (= main@%_27_0 main@%_29_0)))
                (=> main@_20_1 (and main@_20_1 main@_23_0))
                (=> (and main@_20_1 main@_23_0) main@%_30_0)
                (=> (and main@_20_1 main@_23_0) (= main@%.04.i37_1 main@%_21_0))
                (=> (and main@_20_1 main@_23_0)
                    (= main@%.04.i37_2 main@%.04.i37_1))
                main@_20_1)))
  (=> a!3
      (main@_20 main@%.04.i37_2
                main@%.03.i8_0
                @a_1_0
                main@%sm5_0
                @a_2_0
                main@%sm6_0
                main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_34_0 (+ (+ @a_1_0 (* 0 400)) (* main@%_33_0 4))))
      (a!2 (= main@%_36_0 (+ (+ @a_2_0 (* 0 400)) (* main@%_31_0 40) (* 0 4))))
      (a!3 (= main@%_26_0 (+ (+ @a_1_0 (* 0 400)) (* main@%_25_0 4))))
      (a!4 (= main@%_28_0
              (+ (+ @a_2_0 (* 0 400)) (* main@%.03.i8_0 40) (* main@%_21_0 4)))))
(let ((a!5 (and (main@_20 main@%.04.i37_0
                          main@%.03.i8_0
                          @a_1_0
                          main@%sm5_0
                          @a_2_0
                          main@%sm6_0
                          main@%loop.bound_0)
                true
                (= main@%_21_0 (+ main@%.04.i37_0 1))
                (= main@%_22_0 (< main@%.04.i37_0 main@%loop.bound_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@_20_0))
                (=> (and main@.preheader_0 main@_20_0) (not main@%_22_0))
                (=> main@.preheader_0 (= main@%_31_0 (+ main@%.03.i8_0 1)))
                (=> main@.preheader_0 (= main@%_32_0 (< main@%.03.i8_0 9)))
                (=> main@.preheader_0 main@%_32_0)
                (=> main@.preheader_0 (= main@%_33_0 (* main@%_31_0 10)))
                (=> main@.preheader_0 a!1)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0
                    (= main@%_35_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.preheader_0 a!2)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_36_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%_37_0 (select main@%sm6_0 main@%_36_0)))
                (=> main@.preheader_0
                    (= main@%_38_0 (= main@%_35_0 main@%_37_0)))
                (=> main@_23_0 (and main@_23_0 main@_20_0))
                (=> (and main@_23_0 main@_20_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.04.i37_0 11)))
                (=> main@_23_0 a!3)
                (=> main@_23_0 (or (<= @a_1_0 0) (> main@%_26_0 0)))
                (=> main@_23_0 (> @a_1_0 0))
                (=> main@_23_0 (= main@%_27_0 (select main@%sm5_0 main@%_26_0)))
                (=> main@_23_0 a!4)
                (=> main@_23_0 (or (<= @a_2_0 0) (> main@%_28_0 0)))
                (=> main@_23_0 (> @a_2_0 0))
                (=> main@_23_0 (= main@%_29_0 (select main@%sm6_0 main@%_28_0)))
                (=> main@_23_0 (= main@%_30_0 (= main@%_27_0 main@%_29_0)))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> |tuple(main@_23_0, main@verifier.error_0)| main@_23_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.preheader_0, main@verifier.error_0)|
                        |tuple(main@_23_0, main@verifier.error_0)|))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%_38_0))
                (=> |tuple(main@_23_0, main@verifier.error_0)|
                    (not main@%_30_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(query main@verifier.error.split)

