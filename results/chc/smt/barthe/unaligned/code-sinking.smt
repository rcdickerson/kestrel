(set-info :original "./results/chc/bytecode/barthe/unaligned/code-sinking.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@_2 (Int Int (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel main@._crit_edge (Int Int (Array Int Int) (Array Int Int) Int Int Int Int ))
(declare-rel main@.preheader (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_44_0 Bool )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%_49_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%.pre13_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%.pre16_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%spec.select4_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%.pre16.1_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%spec.select4.1_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%.pre16.2_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%spec.select4.2_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%.pre16.3_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%spec.select4.3_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%.pre16.4_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%spec.select4.4_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%.pre16.5_0 Int )
(declare-var main@%_33_0 Bool )
(declare-var main@%spec.select4.5_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%.pre16.6_0 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%spec.select4.6_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%.pre16.7_0 Int )
(declare-var main@%_37_0 Bool )
(declare-var main@%spec.select4.7_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%.pre16.8_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%spec.select4.8_0 Int )
(declare-var main@%spec.select3_0 Int )
(declare-var main@%spec.select3.1_0 Int )
(declare-var main@%spec.select3.2_0 Int )
(declare-var main@%spec.select3.3_0 Int )
(declare-var main@%spec.select3.4_0 Int )
(declare-var main@%spec.select3.5_0 Int )
(declare-var main@%spec.select3.6_0 Int )
(declare-var main@%spec.select3.7_0 Int )
(declare-var main@%spec.select3.8_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%.pre16.9_0 Int )
(declare-var main@%_41_0 Bool )
(declare-var main@%spec.select3.9_0 Int )
(declare-var main@%spec.select4.9_0 Int )
(declare-var main@%_42_0 Int )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%_43_0 Int )
(declare-var main@%.05.i_2 Int )
(declare-var main@%.phi.trans.insert_0 Int )
(declare-var main@%.pre_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_16_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_13_2 Int )
(declare-var main@%spec.select225_2 Int )
(declare-var main@%spec.select24_2 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i11_2 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_2_0 Bool )
(declare-var main@%.0.i11_0 Int )
(declare-var main@%.0.i11_1 Int )
(declare-var main@%_8_0 Int )
(declare-var main@_2_1 Bool )
(declare-var main@_10_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%spec.select225_0 Int )
(declare-var main@%spec.select24_0 Int )
(declare-var main@%_13_1 Int )
(declare-var main@%spec.select225_1 Int )
(declare-var main@%spec.select24_1 Int )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select2_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@._crit_edge_1 Bool )
(declare-var main@._crit_edge14_0 Bool )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.05.i_0 Int )
(declare-var main@%.05.i_1 Int )
(declare-var main@%_50_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm7_0 main@%sm8_0))
(rule (=> (and (main@entry main@%sm7_0 main@%sm8_0)
         true
         (= main@%sm_0 main@%sm8_0)
         (= main@%sm2_0 main@%sm7_0)
         (= main@%_0_0 (= main@%loop.bound_0 10))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%sm_0
                     main@%sm2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%sm2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%sm_0
                     main@%sm2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%sm2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0)
         true
         (=> main@_2_0 (and main@_2_0 main@empty.loop_0))
         (=> (and main@_2_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_2_0 main@empty.loop_0) (= main@%.0.i11_0 0))
         (=> (and main@_2_0 main@empty.loop_0)
             (= main@%.0.i11_1 main@%.0.i11_0))
         main@_2_0)
    (main@_2 @a_1_0
             @a_2_0
             main@%sm_0
             main@%sm2_0
             main@%loop.bound_0
             main@%.0.i11_1
             main@%loop.bound1_0)))
(rule (let ((a!1 (and (main@_2 @a_1_0
                         @a_2_0
                         main@%sm_0
                         main@%sm2_0
                         main@%loop.bound_0
                         main@%.0.i11_0
                         main@%loop.bound1_0)
                true
                (= main@%_3_0 (+ @a_1_0 (* 0 44) (* main@%.0.i11_0 4)))
                (or (<= @a_1_0 0) (> main@%_3_0 0))
                (> @a_1_0 0)
                (= main@%_4_0 (select main@%sm_0 main@%_3_0))
                (= main@%_5_0 (+ @a_2_0 (* 0 44) (* main@%.0.i11_0 4)))
                (or (<= @a_2_0 0) (> main@%_5_0 0))
                (> @a_2_0 0)
                (= main@%_6_0 (select main@%sm2_0 main@%_5_0))
                (= main@%_7_0 (= main@%_4_0 main@%_6_0))
                main@%_7_0
                (= main@%_8_0 (+ main@%.0.i11_0 1))
                (= main@%_9_0 (< main@%.0.i11_0 main@%loop.bound1_0))
                (=> main@_2_1 (and main@_2_1 main@_2_0))
                (=> (and main@_2_1 main@_2_0) main@%_9_0)
                (=> (and main@_2_1 main@_2_0) (= main@%.0.i11_1 main@%_8_0))
                (=> (and main@_2_1 main@_2_0) (= main@%.0.i11_2 main@%.0.i11_1))
                main@_2_1)))
  (=> a!1
      (main@_2 @a_1_0
               @a_2_0
               main@%sm_0
               main@%sm2_0
               main@%loop.bound_0
               main@%.0.i11_2
               main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_3_0 (+ (+ @a_1_0 (* 0 44)) (* main@%.0.i11_0 4))))
      (a!2 (= main@%_11_0 (+ (+ @a_1_0 (* 0 44)) (* 0 4)))))
(let ((a!3 (and (main@_2 @a_1_0
                         @a_2_0
                         main@%sm_0
                         main@%sm2_0
                         main@%loop.bound_0
                         main@%.0.i11_0
                         main@%loop.bound1_0)
                true
                a!1
                (or (<= @a_1_0 0) (> main@%_3_0 0))
                (> @a_1_0 0)
                (= main@%_4_0 (select main@%sm_0 main@%_3_0))
                (= main@%_5_0 (+ @a_2_0 (* 0 44) (* main@%.0.i11_0 4)))
                (or (<= @a_2_0 0) (> main@%_5_0 0))
                (> @a_2_0 0)
                (= main@%_6_0 (select main@%sm2_0 main@%_5_0))
                (= main@%_7_0 (= main@%_4_0 main@%_6_0))
                main@%_7_0
                (= main@%_8_0 (+ main@%.0.i11_0 1))
                (= main@%_9_0 (< main@%.0.i11_0 main@%loop.bound1_0))
                (=> main@_10_0 (and main@_10_0 main@_2_0))
                (=> (and main@_10_0 main@_2_0) (not main@%_9_0))
                (=> main@_10_0 a!2)
                (=> main@_10_0 (or (<= @a_1_0 0) (> main@%_11_0 0)))
                (=> main@_10_0 (= main@%_12_0 (select main@%sm_0 main@%_11_0)))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@_10_0))
                (=> (and main@._crit_edge_0 main@_10_0) (= main@%_13_0 1))
                (=> (and main@._crit_edge_0 main@_10_0)
                    (= main@%spec.select225_0 main@%_12_0))
                (=> (and main@._crit_edge_0 main@_10_0)
                    (= main@%spec.select24_0 0))
                (=> (and main@._crit_edge_0 main@_10_0)
                    (= main@%_13_1 main@%_13_0))
                (=> (and main@._crit_edge_0 main@_10_0)
                    (= main@%spec.select225_1 main@%spec.select225_0))
                (=> (and main@._crit_edge_0 main@_10_0)
                    (= main@%spec.select24_1 main@%spec.select24_0))
                main@._crit_edge_0)))
  (=> a!3
      (main@._crit_edge @a_1_0
                        @a_2_0
                        main@%sm_0
                        main@%sm2_0
                        main@%_13_1
                        main@%spec.select225_1
                        main@%spec.select24_1
                        main@%loop.bound_0)))))
(rule (let ((a!1 (and (main@._crit_edge @a_1_0
                                  @a_2_0
                                  main@%sm_0
                                  main@%sm2_0
                                  main@%_13_0
                                  main@%spec.select225_0
                                  main@%spec.select24_0
                                  main@%loop.bound_0)
                true
                (= main@%.phi.trans.insert_0
                   (+ @a_1_0 (* 0 44) (* main@%_13_0 4)))
                (or (<= @a_1_0 0) (> main@%.phi.trans.insert_0 0))
                (> @a_1_0 0)
                (= main@%.pre_0 (select main@%sm_0 main@%.phi.trans.insert_0))
                (= main@%_14_0 (< main@%spec.select225_0 main@%.pre_0))
                (= main@%spec.select_0
                   (ite main@%_14_0 main@%_13_0 main@%spec.select24_0))
                (= main@%spec.select2_0
                   (ite main@%_14_0 main@%.pre_0 main@%spec.select225_0))
                (= main@%_15_0 (+ main@%_13_0 1))
                (= main@%_16_0 (< main@%_13_0 main@%loop.bound_0))
                (=> main@._crit_edge_1
                    (and main@._crit_edge_1 main@._crit_edge_0))
                (=> (and main@._crit_edge_1 main@._crit_edge_0) main@%_16_0)
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%_13_1 main@%_15_0))
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%spec.select225_1 main@%spec.select2_0))
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%spec.select24_1 main@%spec.select_0))
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%_13_2 main@%_13_1))
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%spec.select225_2 main@%spec.select225_1))
                (=> (and main@._crit_edge_1 main@._crit_edge_0)
                    (= main@%spec.select24_2 main@%spec.select24_1))
                main@._crit_edge_1)))
  (=> a!1
      (main@._crit_edge @a_1_0
                        @a_2_0
                        main@%sm_0
                        main@%sm2_0
                        main@%_13_2
                        main@%spec.select225_2
                        main@%spec.select24_2
                        main@%loop.bound_0))))
(rule (let ((a!1 (= main@%.phi.trans.insert_0
              (+ (+ @a_1_0 (* 0 44)) (* main@%_13_0 4))))
      (a!2 (= main@%_17_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!3 (= main@%_19_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!4 (= main@%_20_0 (+ (+ @a_1_0 (* 0 44)) (* main@%spec.select_0 4))))
      (a!5 (= main@%_21_0 (+ (+ @a_2_0 (* 0 44)) (* 0 4))))
      (a!6 (= main@%_22_0 (+ (+ @a_2_0 (* 0 44)) (* 1 4))))
      (a!7 (= main@%_24_0 (+ (+ @a_2_0 (* 0 44)) (* 2 4))))
      (a!8 (= main@%_26_0 (+ (+ @a_2_0 (* 0 44)) (* 3 4))))
      (a!9 (= main@%_28_0 (+ (+ @a_2_0 (* 0 44)) (* 4 4))))
      (a!10 (= main@%_30_0 (+ (+ @a_2_0 (* 0 44)) (* 5 4))))
      (a!11 (= main@%_32_0 (+ (+ @a_2_0 (* 0 44)) (* 6 4))))
      (a!12 (= main@%_34_0 (+ (+ @a_2_0 (* 0 44)) (* 7 4))))
      (a!13 (= main@%_36_0 (+ (+ @a_2_0 (* 0 44)) (* 8 4))))
      (a!14 (= main@%_38_0 (+ (+ @a_2_0 (* 0 44)) (* 9 4))))
      (a!15 (= main@%_40_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!16 (= main@%_42_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!17 (= main@%_43_0 (+ (+ @a_2_0 (* 0 44)) (* main@%spec.select3.9_0 4)))))
(let ((a!18 (and (main@._crit_edge @a_1_0
                                   @a_2_0
                                   main@%sm_0
                                   main@%sm2_0
                                   main@%_13_0
                                   main@%spec.select225_0
                                   main@%spec.select24_0
                                   main@%loop.bound_0)
                 true
                 a!1
                 (or (<= @a_1_0 0) (> main@%.phi.trans.insert_0 0))
                 (> @a_1_0 0)
                 (= main@%.pre_0 (select main@%sm_0 main@%.phi.trans.insert_0))
                 (= main@%_14_0 (< main@%spec.select225_0 main@%.pre_0))
                 (= main@%spec.select_0
                    (ite main@%_14_0 main@%_13_0 main@%spec.select24_0))
                 (= main@%spec.select2_0
                    (ite main@%_14_0 main@%.pre_0 main@%spec.select225_0))
                 (= main@%_15_0 (+ main@%_13_0 1))
                 (= main@%_16_0 (< main@%_13_0 main@%loop.bound_0))
                 (=> main@._crit_edge14_0
                     (and main@._crit_edge14_0 main@._crit_edge_0))
                 (=> (and main@._crit_edge14_0 main@._crit_edge_0)
                     (not main@%_16_0))
                 (=> main@._crit_edge14_0 a!2)
                 (=> main@._crit_edge14_0 (or (<= @a_1_0 0) (> main@%_17_0 0)))
                 (=> main@._crit_edge14_0 (> @a_1_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%_18_0 (select main@%sm_0 main@%_17_0)))
                 (=> main@._crit_edge14_0 a!3)
                 (=> main@._crit_edge14_0 (or (<= @a_1_0 0) (> main@%_19_0 0)))
                 (=> main@._crit_edge14_0 (> @a_1_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%sm3_0
                        (store main@%sm_0 main@%_19_0 main@%spec.select2_0)))
                 (=> main@._crit_edge14_0 a!4)
                 (=> main@._crit_edge14_0 (or (<= @a_1_0 0) (> main@%_20_0 0)))
                 (=> main@._crit_edge14_0 (> @a_1_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%sm4_0 (store main@%sm3_0 main@%_20_0 main@%_18_0)))
                 (=> main@._crit_edge14_0 a!5)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_21_0 0)))
                 (=> main@._crit_edge14_0
                     (= main@%.pre13_0 (select main@%sm2_0 main@%_21_0)))
                 (=> main@._crit_edge14_0 a!6)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_22_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16_0 (select main@%sm2_0 main@%_22_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_23_0 (< main@%.pre13_0 main@%.pre16_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4_0
                        (ite main@%_23_0 main@%.pre16_0 main@%.pre13_0)))
                 (=> main@._crit_edge14_0 a!7)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_24_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.1_0 (select main@%sm2_0 main@%_24_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_25_0 (< main@%spec.select4_0 main@%.pre16.1_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.1_0
                        (ite main@%_25_0 main@%.pre16.1_0 main@%spec.select4_0)))
                 (=> main@._crit_edge14_0 a!8)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_26_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.2_0 (select main@%sm2_0 main@%_26_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_27_0 (< main@%spec.select4.1_0 main@%.pre16.2_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.2_0
                        (ite main@%_27_0
                             main@%.pre16.2_0
                             main@%spec.select4.1_0)))
                 (=> main@._crit_edge14_0 a!9)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_28_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.3_0 (select main@%sm2_0 main@%_28_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_29_0 (< main@%spec.select4.2_0 main@%.pre16.3_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.3_0
                        (ite main@%_29_0
                             main@%.pre16.3_0
                             main@%spec.select4.2_0)))
                 (=> main@._crit_edge14_0 a!10)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_30_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.4_0 (select main@%sm2_0 main@%_30_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_31_0 (< main@%spec.select4.3_0 main@%.pre16.4_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.4_0
                        (ite main@%_31_0
                             main@%.pre16.4_0
                             main@%spec.select4.3_0)))
                 (=> main@._crit_edge14_0 a!11)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_32_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.5_0 (select main@%sm2_0 main@%_32_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_33_0 (< main@%spec.select4.4_0 main@%.pre16.5_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.5_0
                        (ite main@%_33_0
                             main@%.pre16.5_0
                             main@%spec.select4.4_0)))
                 (=> main@._crit_edge14_0 a!12)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_34_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.6_0 (select main@%sm2_0 main@%_34_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_35_0 (< main@%spec.select4.5_0 main@%.pre16.6_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.6_0
                        (ite main@%_35_0
                             main@%.pre16.6_0
                             main@%spec.select4.5_0)))
                 (=> main@._crit_edge14_0 a!13)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_36_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.7_0 (select main@%sm2_0 main@%_36_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_37_0 (< main@%spec.select4.6_0 main@%.pre16.7_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.7_0
                        (ite main@%_37_0
                             main@%.pre16.7_0
                             main@%spec.select4.6_0)))
                 (=> main@._crit_edge14_0 a!14)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_38_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.8_0 (select main@%sm2_0 main@%_38_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_39_0 (< main@%spec.select4.7_0 main@%.pre16.8_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.8_0
                        (ite main@%_39_0
                             main@%.pre16.8_0
                             main@%spec.select4.7_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3_0 (ite main@%_23_0 1 0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.1_0
                        (ite main@%_25_0 2 main@%spec.select3_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.2_0
                        (ite main@%_27_0 3 main@%spec.select3.1_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.3_0
                        (ite main@%_29_0 4 main@%spec.select3.2_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.4_0
                        (ite main@%_31_0 5 main@%spec.select3.3_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.5_0
                        (ite main@%_33_0 6 main@%spec.select3.4_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.6_0
                        (ite main@%_35_0 7 main@%spec.select3.5_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.7_0
                        (ite main@%_37_0 8 main@%spec.select3.6_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.8_0
                        (ite main@%_39_0 9 main@%spec.select3.7_0)))
                 (=> main@._crit_edge14_0 a!15)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_40_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%.pre16.9_0 (select main@%sm2_0 main@%_40_0)))
                 (=> main@._crit_edge14_0
                     (= main@%_41_0 (< main@%spec.select4.8_0 main@%.pre16.9_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select3.9_0
                        (ite main@%_41_0 10 main@%spec.select3.8_0)))
                 (=> main@._crit_edge14_0
                     (= main@%spec.select4.9_0
                        (ite main@%_41_0
                             main@%.pre16.9_0
                             main@%spec.select4.8_0)))
                 (=> main@._crit_edge14_0 a!16)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_42_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%sm5_0
                        (store main@%sm2_0 main@%_42_0 main@%spec.select4.9_0)))
                 (=> main@._crit_edge14_0 a!17)
                 (=> main@._crit_edge14_0 (or (<= @a_2_0 0) (> main@%_43_0 0)))
                 (=> main@._crit_edge14_0 (> @a_2_0 0))
                 (=> main@._crit_edge14_0
                     (= main@%sm6_0
                        (store main@%sm5_0 main@%_43_0 main@%.pre16.9_0)))
                 (=> main@.preheader_0
                     (and main@.preheader_0 main@._crit_edge14_0))
                 (=> (and main@.preheader_0 main@._crit_edge14_0)
                     (= main@%.05.i_0 0))
                 (=> (and main@.preheader_0 main@._crit_edge14_0)
                     (= main@%.05.i_1 main@%.05.i_0))
                 main@.preheader_0)))
  (=> a!18
      (main@.preheader main@%.05.i_1 @a_1_0 main@%sm4_0 @a_2_0 main@%sm6_0)))))
(rule (let ((a!1 (and (main@.preheader main@%.05.i_0
                                 @a_1_0
                                 main@%sm4_0
                                 @a_2_0
                                 main@%sm6_0)
                true
                (= main@%_44_0 (< main@%.05.i_0 10))
                main@%_44_0
                (= main@%_45_0 (+ @a_1_0 (* 0 44) (* main@%.05.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_45_0 0))
                (> @a_1_0 0)
                (= main@%_46_0 (select main@%sm4_0 main@%_45_0))
                (= main@%_47_0 (+ @a_2_0 (* 0 44) (* main@%.05.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_47_0 0))
                (> @a_2_0 0)
                (= main@%_48_0 (select main@%sm6_0 main@%_47_0))
                (= main@%_49_0 (= main@%_46_0 main@%_48_0))
                (= main@%_50_0 (+ main@%.05.i_0 1))
                (=> main@.preheader_1 (and main@.preheader_1 main@.preheader_0))
                (=> (and main@.preheader_1 main@.preheader_0) main@%_49_0)
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.05.i_1 main@%_50_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.05.i_2 main@%.05.i_1))
                main@.preheader_1)))
  (=> a!1 (main@.preheader main@%.05.i_2 @a_1_0 main@%sm4_0 @a_2_0 main@%sm6_0))))
(rule (let ((a!1 (and (main@.preheader main@%.05.i_0
                                 @a_1_0
                                 main@%sm4_0
                                 @a_2_0
                                 main@%sm6_0)
                true
                (= main@%_44_0 (< main@%.05.i_0 10))
                main@%_44_0
                (= main@%_45_0 (+ @a_1_0 (* 0 44) (* main@%.05.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_45_0 0))
                (> @a_1_0 0)
                (= main@%_46_0 (select main@%sm4_0 main@%_45_0))
                (= main@%_47_0 (+ @a_2_0 (* 0 44) (* main@%.05.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_47_0 0))
                (> @a_2_0 0)
                (= main@%_48_0 (select main@%sm6_0 main@%_47_0))
                (= main@%_49_0 (= main@%_46_0 main@%_48_0))
                (= main@%_50_0 (+ main@%.05.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_49_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

