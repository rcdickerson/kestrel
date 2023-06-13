(set-info :original "./results/chc/bytecode/barthe/count-loops/loop-unswitching.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int (Array Int Int) (Array Int Int) Int ))
(declare-rel main@_3 (Int Int Int Int (Array Int Int) Int (Array Int Int) Int ))
(declare-rel main@.preheader2 (Int Int Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@.preheader1 (Int (Array Int Int) Int Int (Array Int Int) Int ))
(declare-rel main@.preheader (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_17_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%.04.i_2 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%.02.i3_2 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%.01.i4_2 Int )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i5_2 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @b_1_0 Int )
(declare-var @b_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_3_0 Bool )
(declare-var main@%.0.i5_0 Int )
(declare-var main@%.0.i5_1 Int )
(declare-var main@%_9_0 Int )
(declare-var main@_3_1 Bool )
(declare-var main@.preheader2_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.01.i4_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.01.i4_1 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_12_0 Int )
(declare-var main@.preheader2_1 Bool )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%.02.i3_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%.02.i3_1 Int )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%_15_0 Int )
(declare-var main@.preheader1_1 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.04.i_0 Int )
(declare-var main@%.04.i_1 Int )
(declare-var main@%_23_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm6_0 main@%sm7_0))
(rule (=> (and (main@entry main@%sm6_0 main@%sm7_0)
         true
         (= main@%sm_0 main@%sm6_0)
         (= main@%sm3_0 main@%sm7_0)
         (= main@%_0_0 (= main@%loop.bound_0 9))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         true
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @b_1_0
                     @b_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%sm3_0
                     main@%sm_0
                     main@%loop.bound2_0)))
(rule (=> (and (main@empty.loop @b_1_0
                          @b_2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%sm3_0
                          main@%sm_0
                          main@%loop.bound2_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop @b_1_0
                     @b_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%sm3_0
                     main@%sm_0
                     main@%loop.bound2_0)))
(rule (=> (and (main@empty.loop @b_1_0
                          @b_2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%sm3_0
                          main@%sm_0
                          main@%loop.bound2_0)
         true
         (=> main@_3_0 (and main@_3_0 main@empty.loop_0))
         (=> (and main@_3_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i5_0 0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i5_1 main@%.0.i5_0))
         main@_3_0)
    (main@_3 @b_1_0
             @b_2_0
             main@%loop.bound_0
             main@%loop.bound1_0
             main@%sm3_0
             main@%.0.i5_1
             main@%sm_0
             main@%loop.bound2_0)))
(rule (let ((a!1 (and (main@_3 @b_1_0
                         @b_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%sm3_0
                         main@%.0.i5_0
                         main@%sm_0
                         main@%loop.bound2_0)
                true
                (= main@%_4_0 (+ @b_1_0 (* 0 40) (* main@%.0.i5_0 4)))
                (or (<= @b_1_0 0) (> main@%_4_0 0))
                (> @b_1_0 0)
                (= main@%_5_0 (select main@%sm_0 main@%_4_0))
                (= main@%_6_0 (+ @b_2_0 (* 0 40) (* main@%.0.i5_0 4)))
                (or (<= @b_2_0 0) (> main@%_6_0 0))
                (> @b_2_0 0)
                (= main@%_7_0 (select main@%sm3_0 main@%_6_0))
                (= main@%_8_0 (= main@%_5_0 main@%_7_0))
                main@%_8_0
                (= main@%_9_0 (+ main@%.0.i5_0 1))
                (= main@%_10_0 (< main@%.0.i5_0 main@%loop.bound2_0))
                (=> main@_3_1 (and main@_3_1 main@_3_0))
                (=> (and main@_3_1 main@_3_0) main@%_10_0)
                (=> (and main@_3_1 main@_3_0) (= main@%.0.i5_1 main@%_9_0))
                (=> (and main@_3_1 main@_3_0) (= main@%.0.i5_2 main@%.0.i5_1))
                main@_3_1)))
  (=> a!1
      (main@_3 @b_1_0
               @b_2_0
               main@%loop.bound_0
               main@%loop.bound1_0
               main@%sm3_0
               main@%.0.i5_2
               main@%sm_0
               main@%loop.bound2_0))))
(rule (let ((a!1 (and (main@_3 @b_1_0
                         @b_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%sm3_0
                         main@%.0.i5_0
                         main@%sm_0
                         main@%loop.bound2_0)
                true
                (= main@%_4_0 (+ @b_1_0 (* 0 40) (* main@%.0.i5_0 4)))
                (or (<= @b_1_0 0) (> main@%_4_0 0))
                (> @b_1_0 0)
                (= main@%_5_0 (select main@%sm_0 main@%_4_0))
                (= main@%_6_0 (+ @b_2_0 (* 0 40) (* main@%.0.i5_0 4)))
                (or (<= @b_2_0 0) (> main@%_6_0 0))
                (> @b_2_0 0)
                (= main@%_7_0 (select main@%sm3_0 main@%_6_0))
                (= main@%_8_0 (= main@%_5_0 main@%_7_0))
                main@%_8_0
                (= main@%_9_0 (+ main@%.0.i5_0 1))
                (= main@%_10_0 (< main@%.0.i5_0 main@%loop.bound2_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@_3_0))
                (=> (and main@.preheader2_0 main@_3_0) (not main@%_10_0))
                (=> (and main@.preheader2_0 main@_3_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@.preheader2_0 main@_3_0) (= main@%.01.i4_0 0))
                (=> (and main@.preheader2_0 main@_3_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader2_0 main@_3_0)
                    (= main@%.01.i4_1 main@%.01.i4_0))
                main@.preheader2_0)))
  (=> a!1
      (main@.preheader2 @b_1_0
                        @b_2_0
                        main@%loop.bound_0
                        main@%.01.i4_1
                        main@%shadow.mem.0.0_1
                        main@%loop.bound1_0
                        main@%sm3_0))))
(rule (let ((a!1 (and (main@.preheader2 @b_1_0
                                  @b_2_0
                                  main@%loop.bound_0
                                  main@%.01.i4_0
                                  main@%shadow.mem.0.0_0
                                  main@%loop.bound1_0
                                  main@%sm3_0)
                true
                (= main@%_11_0 (+ @b_1_0 (* 0 40) (* main@%.01.i4_0 4)))
                (or (<= @b_1_0 0) (> main@%_11_0 0))
                (> @b_1_0 0)
                (= main@%sm4_0 (store main@%shadow.mem.0.0_0 main@%_11_0 0))
                (= main@%_12_0 (+ main@%.01.i4_0 1))
                (= main@%_13_0 (< main@%.01.i4_0 main@%loop.bound1_0))
                (=> main@.preheader2_1
                    (and main@.preheader2_1 main@.preheader2_0))
                (=> (and main@.preheader2_1 main@.preheader2_0) main@%_13_0)
                (=> (and main@.preheader2_1 main@.preheader2_0)
                    (= main@%shadow.mem.0.0_1 main@%sm4_0))
                (=> (and main@.preheader2_1 main@.preheader2_0)
                    (= main@%.01.i4_1 main@%_12_0))
                (=> (and main@.preheader2_1 main@.preheader2_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@.preheader2_1 main@.preheader2_0)
                    (= main@%.01.i4_2 main@%.01.i4_1))
                main@.preheader2_1)))
  (=> a!1
      (main@.preheader2 @b_1_0
                        @b_2_0
                        main@%loop.bound_0
                        main@%.01.i4_2
                        main@%shadow.mem.0.0_2
                        main@%loop.bound1_0
                        main@%sm3_0))))
(rule (let ((a!1 (and (main@.preheader2 @b_1_0
                                  @b_2_0
                                  main@%loop.bound_0
                                  main@%.01.i4_0
                                  main@%shadow.mem.0.0_0
                                  main@%loop.bound1_0
                                  main@%sm3_0)
                true
                (= main@%_11_0 (+ @b_1_0 (* 0 40) (* main@%.01.i4_0 4)))
                (or (<= @b_1_0 0) (> main@%_11_0 0))
                (> @b_1_0 0)
                (= main@%sm4_0 (store main@%shadow.mem.0.0_0 main@%_11_0 0))
                (= main@%_12_0 (+ main@%.01.i4_0 1))
                (= main@%_13_0 (< main@%.01.i4_0 main@%loop.bound1_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_13_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.0_0 main@%sm3_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.02.i3_0 0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.02.i3_1 main@%.02.i3_0))
                main@.preheader1_0)))
  (=> a!1
      (main@.preheader1 @b_1_0
                        main@%sm4_0
                        @b_2_0
                        main@%.02.i3_1
                        main@%shadow.mem.4.0_1
                        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@.preheader1 @b_1_0
                                  main@%sm4_0
                                  @b_2_0
                                  main@%.02.i3_0
                                  main@%shadow.mem.4.0_0
                                  main@%loop.bound_0)
                true
                (= main@%_14_0 (+ @b_2_0 (* 0 40) (* main@%.02.i3_0 4)))
                (or (<= @b_2_0 0) (> main@%_14_0 0))
                (> @b_2_0 0)
                (= main@%sm5_0 (store main@%shadow.mem.4.0_0 main@%_14_0 0))
                (= main@%_15_0 (+ main@%.02.i3_0 1))
                (= main@%_16_0 (< main@%.02.i3_0 main@%loop.bound_0))
                (=> main@.preheader1_1
                    (and main@.preheader1_1 main@.preheader1_0))
                (=> (and main@.preheader1_1 main@.preheader1_0) main@%_16_0)
                (=> (and main@.preheader1_1 main@.preheader1_0)
                    (= main@%shadow.mem.4.0_1 main@%sm5_0))
                (=> (and main@.preheader1_1 main@.preheader1_0)
                    (= main@%.02.i3_1 main@%_15_0))
                (=> (and main@.preheader1_1 main@.preheader1_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1_1 main@.preheader1_0)
                    (= main@%.02.i3_2 main@%.02.i3_1))
                main@.preheader1_1)))
  (=> a!1
      (main@.preheader1 @b_1_0
                        main@%sm4_0
                        @b_2_0
                        main@%.02.i3_2
                        main@%shadow.mem.4.0_2
                        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@.preheader1 @b_1_0
                                  main@%sm4_0
                                  @b_2_0
                                  main@%.02.i3_0
                                  main@%shadow.mem.4.0_0
                                  main@%loop.bound_0)
                true
                (= main@%_14_0 (+ @b_2_0 (* 0 40) (* main@%.02.i3_0 4)))
                (or (<= @b_2_0 0) (> main@%_14_0 0))
                (> @b_2_0 0)
                (= main@%sm5_0 (store main@%shadow.mem.4.0_0 main@%_14_0 0))
                (= main@%_15_0 (+ main@%.02.i3_0 1))
                (= main@%_16_0 (< main@%.02.i3_0 main@%loop.bound_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.04.i_0 0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.04.i_1 main@%.04.i_0))
                main@.preheader_0)))
  (=> a!1 (main@.preheader main@%.04.i_1 @b_1_0 main@%sm4_0 @b_2_0 main@%sm5_0))))
(rule (let ((a!1 (and (main@.preheader main@%.04.i_0
                                 @b_1_0
                                 main@%sm4_0
                                 @b_2_0
                                 main@%sm5_0)
                true
                (= main@%_17_0 (< main@%.04.i_0 10))
                main@%_17_0
                (= main@%_18_0 (+ @b_1_0 (* 0 40) (* main@%.04.i_0 4)))
                (or (<= @b_1_0 0) (> main@%_18_0 0))
                (> @b_1_0 0)
                (= main@%_19_0 (select main@%sm4_0 main@%_18_0))
                (= main@%_20_0 (+ @b_2_0 (* 0 40) (* main@%.04.i_0 4)))
                (or (<= @b_2_0 0) (> main@%_20_0 0))
                (> @b_2_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (= main@%_19_0 main@%_21_0))
                (= main@%_23_0 (+ main@%.04.i_0 1))
                (=> main@.preheader_1 (and main@.preheader_1 main@.preheader_0))
                (=> (and main@.preheader_1 main@.preheader_0) main@%_22_0)
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.04.i_1 main@%_23_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.04.i_2 main@%.04.i_1))
                main@.preheader_1)))
  (=> a!1 (main@.preheader main@%.04.i_2 @b_1_0 main@%sm4_0 @b_2_0 main@%sm5_0))))
(rule (let ((a!1 (and (main@.preheader main@%.04.i_0
                                 @b_1_0
                                 main@%sm4_0
                                 @b_2_0
                                 main@%sm5_0)
                true
                (= main@%_17_0 (< main@%.04.i_0 10))
                main@%_17_0
                (= main@%_18_0 (+ @b_1_0 (* 0 40) (* main@%.04.i_0 4)))
                (or (<= @b_1_0 0) (> main@%_18_0 0))
                (> @b_1_0 0)
                (= main@%_19_0 (select main@%sm4_0 main@%_18_0))
                (= main@%_20_0 (+ @b_2_0 (* 0 40) (* main@%.04.i_0 4)))
                (or (<= @b_2_0 0) (> main@%_20_0 0))
                (> @b_2_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (= main@%_19_0 main@%_21_0))
                (= main@%_23_0 (+ main@%.04.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

