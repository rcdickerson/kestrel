(set-info :original "./results/chc/bytecode/barthe/sa/code-sinking.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int (Array Int Int) (Array Int Int) Int ))
(declare-rel main@_1 (Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@_60 (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_61_0 Bool )
(declare-var main@%_62_0 Int )
(declare-var main@%_63_0 Int )
(declare-var main@%_64_0 Int )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%.pre30_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%.pre_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%.pre32_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%spec.select4_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%.212.i_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%.pre.1_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%.pre32.1_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%spec.select4.1_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%.212.i.1_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%.pre.2_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%.pre32.2_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%spec.select4.2_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%.212.i.2_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%.pre.3_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%.pre32.3_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%spec.select4.3_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%.212.i.3_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%.pre.4_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%.pre32.4_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%spec.select4.4_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%.212.i.4_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%.pre.5_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%.pre32.5_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%spec.select4.5_0 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%.212.i.5_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%.pre.6_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%.pre32.6_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%spec.select4.6_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%.212.i.6_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%.pre.7_0 Int )
(declare-var main@%_41_0 Int )
(declare-var main@%.pre32.7_0 Int )
(declare-var main@%_42_0 Bool )
(declare-var main@%spec.select4.7_0 Int )
(declare-var main@%_43_0 Bool )
(declare-var main@%.212.i.7_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%.pre.8_0 Int )
(declare-var main@%_45_0 Int )
(declare-var main@%.pre32.8_0 Int )
(declare-var main@%_46_0 Bool )
(declare-var main@%spec.select4.8_0 Int )
(declare-var main@%_47_0 Bool )
(declare-var main@%.212.i.8_0 Int )
(declare-var main@%.215.i_0 Int )
(declare-var main@%.215.i.1_0 Int )
(declare-var main@%.215.i.2_0 Int )
(declare-var main@%.215.i.3_0 Int )
(declare-var main@%.215.i.4_0 Int )
(declare-var main@%.215.i.5_0 Int )
(declare-var main@%.215.i.6_0 Int )
(declare-var main@%.215.i.7_0 Int )
(declare-var main@%.215.i.8_0 Int )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select.1_0 Int )
(declare-var main@%spec.select.2_0 Int )
(declare-var main@%spec.select.3_0 Int )
(declare-var main@%spec.select.4_0 Int )
(declare-var main@%spec.select.5_0 Int )
(declare-var main@%spec.select.6_0 Int )
(declare-var main@%spec.select.7_0 Int )
(declare-var main@%spec.select.8_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%.pre.9_0 Int )
(declare-var main@%_49_0 Int )
(declare-var main@%.pre32.9_0 Int )
(declare-var main@%_50_0 Bool )
(declare-var main@%spec.select.9_0 Int )
(declare-var main@%spec.select4.9_0 Int )
(declare-var main@%_51_0 Bool )
(declare-var main@%.215.i.9_0 Int )
(declare-var main@%.212.i.9_0 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@%sm2_0 (Array Int Int) )
(declare-var main@%_55_0 Int )
(declare-var main@%_56_0 Int )
(declare-var main@%_57_0 Int )
(declare-var main@%_58_0 Int )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%_59_0 Int )
(declare-var main@%.016.i_2 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i25_2 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm1_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_1_0 Bool )
(declare-var main@%.0.i25_0 Int )
(declare-var main@%.0.i25_1 Int )
(declare-var main@%_7_0 Int )
(declare-var main@_1_1 Bool )
(declare-var main@._crit_edge28_0 Bool )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@_60_0 Bool )
(declare-var main@%.016.i_0 Int )
(declare-var main@%.016.i_1 Int )
(declare-var main@%_67_0 Int )
(declare-var main@_60_1 Bool )
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
         (= main@%sm1_0 main@%sm7_0)
         (= main@%_0_0 (= main@%loop.bound_0 9))
         main@%_0_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0 @a_2_0 main@%sm_0 main@%sm1_0 main@%loop.bound_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%sm1_0
                          main@%loop.bound_0)
         true
         (=> main@empty.loop.body_0
             (and main@empty.loop.body_0 main@empty.loop_0))
         (=> (and main@empty.loop.body_0 main@empty.loop_0)
             main@%nd.loop.cond_0)
         (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
         main@empty.loop_1)
    (main@empty.loop @a_1_0 @a_2_0 main@%sm_0 main@%sm1_0 main@%loop.bound_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%sm1_0
                          main@%loop.bound_0)
         true
         (=> main@_1_0 (and main@_1_0 main@empty.loop_0))
         (=> (and main@_1_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_1_0 main@empty.loop_0) (= main@%.0.i25_0 0))
         (=> (and main@_1_0 main@empty.loop_0)
             (= main@%.0.i25_1 main@%.0.i25_0))
         main@_1_0)
    (main@_1 @a_1_0
             @a_2_0
             main@%sm_0
             main@%sm1_0
             main@%.0.i25_1
             main@%loop.bound_0)))
(rule (let ((a!1 (and (main@_1 @a_1_0
                         @a_2_0
                         main@%sm_0
                         main@%sm1_0
                         main@%.0.i25_0
                         main@%loop.bound_0)
                true
                (= main@%_2_0 (+ @a_1_0 (* 0 44) (* main@%.0.i25_0 4)))
                (or (<= @a_1_0 0) (> main@%_2_0 0))
                (> @a_1_0 0)
                (= main@%_3_0 (select main@%sm_0 main@%_2_0))
                (= main@%_4_0 (+ @a_2_0 (* 0 44) (* main@%.0.i25_0 4)))
                (or (<= @a_2_0 0) (> main@%_4_0 0))
                (> @a_2_0 0)
                (= main@%_5_0 (select main@%sm1_0 main@%_4_0))
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (+ main@%.0.i25_0 1))
                (= main@%_8_0 (< main@%.0.i25_0 main@%loop.bound_0))
                (=> main@_1_1 (and main@_1_1 main@_1_0))
                (=> (and main@_1_1 main@_1_0) main@%_8_0)
                (=> (and main@_1_1 main@_1_0) (= main@%.0.i25_1 main@%_7_0))
                (=> (and main@_1_1 main@_1_0) (= main@%.0.i25_2 main@%.0.i25_1))
                main@_1_1)))
  (=> a!1
      (main@_1 @a_1_0
               @a_2_0
               main@%sm_0
               main@%sm1_0
               main@%.0.i25_2
               main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_2_0 (+ (+ @a_1_0 (* 0 44)) (* main@%.0.i25_0 4))))
      (a!2 (= main@%_4_0 (+ (+ @a_2_0 (* 0 44)) (* main@%.0.i25_0 4))))
      (a!3 (= main@%_9_0 (+ (+ @a_1_0 (* 0 44)) (* 0 4))))
      (a!4 (= main@%_11_0 (+ (+ @a_2_0 (* 0 44)) (* 0 4))))
      (a!5 (= main@%_12_0 (+ (+ @a_1_0 (* 0 44)) (* 1 4))))
      (a!6 (= main@%_13_0 (+ (+ @a_2_0 (* 0 44)) (* 1 4))))
      (a!7 (= main@%_16_0 (+ (+ @a_1_0 (* 0 44)) (* 2 4))))
      (a!8 (= main@%_17_0 (+ (+ @a_2_0 (* 0 44)) (* 2 4))))
      (a!9 (= main@%_20_0 (+ (+ @a_1_0 (* 0 44)) (* 3 4))))
      (a!10 (= main@%_21_0 (+ (+ @a_2_0 (* 0 44)) (* 3 4))))
      (a!11 (= main@%_24_0 (+ (+ @a_1_0 (* 0 44)) (* 4 4))))
      (a!12 (= main@%_25_0 (+ (+ @a_2_0 (* 0 44)) (* 4 4))))
      (a!13 (= main@%_28_0 (+ (+ @a_1_0 (* 0 44)) (* 5 4))))
      (a!14 (= main@%_29_0 (+ (+ @a_2_0 (* 0 44)) (* 5 4))))
      (a!15 (= main@%_32_0 (+ (+ @a_1_0 (* 0 44)) (* 6 4))))
      (a!16 (= main@%_33_0 (+ (+ @a_2_0 (* 0 44)) (* 6 4))))
      (a!17 (= main@%_36_0 (+ (+ @a_1_0 (* 0 44)) (* 7 4))))
      (a!18 (= main@%_37_0 (+ (+ @a_2_0 (* 0 44)) (* 7 4))))
      (a!19 (= main@%_40_0 (+ (+ @a_1_0 (* 0 44)) (* 8 4))))
      (a!20 (= main@%_41_0 (+ (+ @a_2_0 (* 0 44)) (* 8 4))))
      (a!21 (= main@%_44_0 (+ (+ @a_1_0 (* 0 44)) (* 9 4))))
      (a!22 (= main@%_45_0 (+ (+ @a_2_0 (* 0 44)) (* 9 4))))
      (a!23 (= main@%_48_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!24 (= main@%_49_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!25 (= main@%_52_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!26 (= main@%_54_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!27 (= main@%_55_0 (+ (+ @a_2_0 (* 0 44)) (* main@%.215.i.9_0 4))))
      (a!28 (= main@%_56_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!29 (= main@%_58_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!30 (= main@%_59_0 (+ (+ @a_1_0 (* 0 44)) (* main@%spec.select.9_0 4)))))
(let ((a!31 (and (main@_1 @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%sm1_0
                          main@%.0.i25_0
                          main@%loop.bound_0)
                 true
                 a!1
                 (or (<= @a_1_0 0) (> main@%_2_0 0))
                 (> @a_1_0 0)
                 (= main@%_3_0 (select main@%sm_0 main@%_2_0))
                 a!2
                 (or (<= @a_2_0 0) (> main@%_4_0 0))
                 (> @a_2_0 0)
                 (= main@%_5_0 (select main@%sm1_0 main@%_4_0))
                 (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                 main@%_6_0
                 (= main@%_7_0 (+ main@%.0.i25_0 1))
                 (= main@%_8_0 (< main@%.0.i25_0 main@%loop.bound_0))
                 (=> main@._crit_edge28_0 (and main@._crit_edge28_0 main@_1_0))
                 (=> (and main@._crit_edge28_0 main@_1_0) (not main@%_8_0))
                 (=> main@._crit_edge28_0 a!3)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_9_0 0)))
                 (=> main@._crit_edge28_0
                     (= main@%_10_0 (select main@%sm_0 main@%_9_0)))
                 (=> main@._crit_edge28_0 a!4)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_11_0 0)))
                 (=> main@._crit_edge28_0
                     (= main@%.pre30_0 (select main@%sm1_0 main@%_11_0)))
                 (=> main@._crit_edge28_0 a!5)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_12_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre_0 (select main@%sm_0 main@%_12_0)))
                 (=> main@._crit_edge28_0 a!6)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_13_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32_0 (select main@%sm1_0 main@%_13_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_14_0 (< main@%_10_0 main@%.pre_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4_0
                        (ite main@%_14_0 main@%.pre_0 main@%_10_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_15_0 (< main@%.pre30_0 main@%.pre32_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i_0
                        (ite main@%_15_0 main@%.pre32_0 main@%.pre30_0)))
                 (=> main@._crit_edge28_0 a!7)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_16_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.1_0 (select main@%sm_0 main@%_16_0)))
                 (=> main@._crit_edge28_0 a!8)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_17_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.1_0 (select main@%sm1_0 main@%_17_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_18_0 (< main@%spec.select4_0 main@%.pre.1_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.1_0
                        (ite main@%_18_0 main@%.pre.1_0 main@%spec.select4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_19_0 (< main@%.212.i_0 main@%.pre32.1_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.1_0
                        (ite main@%_19_0 main@%.pre32.1_0 main@%.212.i_0)))
                 (=> main@._crit_edge28_0 a!9)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_20_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.2_0 (select main@%sm_0 main@%_20_0)))
                 (=> main@._crit_edge28_0 a!10)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_21_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.2_0 (select main@%sm1_0 main@%_21_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_22_0 (< main@%spec.select4.1_0 main@%.pre.2_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.2_0
                        (ite main@%_22_0 main@%.pre.2_0 main@%spec.select4.1_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_23_0 (< main@%.212.i.1_0 main@%.pre32.2_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.2_0
                        (ite main@%_23_0 main@%.pre32.2_0 main@%.212.i.1_0)))
                 (=> main@._crit_edge28_0 a!11)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_24_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.3_0 (select main@%sm_0 main@%_24_0)))
                 (=> main@._crit_edge28_0 a!12)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_25_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.3_0 (select main@%sm1_0 main@%_25_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_26_0 (< main@%spec.select4.2_0 main@%.pre.3_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.3_0
                        (ite main@%_26_0 main@%.pre.3_0 main@%spec.select4.2_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_27_0 (< main@%.212.i.2_0 main@%.pre32.3_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.3_0
                        (ite main@%_27_0 main@%.pre32.3_0 main@%.212.i.2_0)))
                 (=> main@._crit_edge28_0 a!13)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_28_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.4_0 (select main@%sm_0 main@%_28_0)))
                 (=> main@._crit_edge28_0 a!14)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_29_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.4_0 (select main@%sm1_0 main@%_29_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_30_0 (< main@%spec.select4.3_0 main@%.pre.4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.4_0
                        (ite main@%_30_0 main@%.pre.4_0 main@%spec.select4.3_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_31_0 (< main@%.212.i.3_0 main@%.pre32.4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.4_0
                        (ite main@%_31_0 main@%.pre32.4_0 main@%.212.i.3_0)))
                 (=> main@._crit_edge28_0 a!15)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_32_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.5_0 (select main@%sm_0 main@%_32_0)))
                 (=> main@._crit_edge28_0 a!16)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_33_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.5_0 (select main@%sm1_0 main@%_33_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_34_0 (< main@%spec.select4.4_0 main@%.pre.5_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.5_0
                        (ite main@%_34_0 main@%.pre.5_0 main@%spec.select4.4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_35_0 (< main@%.212.i.4_0 main@%.pre32.5_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.5_0
                        (ite main@%_35_0 main@%.pre32.5_0 main@%.212.i.4_0)))
                 (=> main@._crit_edge28_0 a!17)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_36_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.6_0 (select main@%sm_0 main@%_36_0)))
                 (=> main@._crit_edge28_0 a!18)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_37_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.6_0 (select main@%sm1_0 main@%_37_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_38_0 (< main@%spec.select4.5_0 main@%.pre.6_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.6_0
                        (ite main@%_38_0 main@%.pre.6_0 main@%spec.select4.5_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_39_0 (< main@%.212.i.5_0 main@%.pre32.6_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.6_0
                        (ite main@%_39_0 main@%.pre32.6_0 main@%.212.i.5_0)))
                 (=> main@._crit_edge28_0 a!19)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_40_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.7_0 (select main@%sm_0 main@%_40_0)))
                 (=> main@._crit_edge28_0 a!20)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_41_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.7_0 (select main@%sm1_0 main@%_41_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_42_0 (< main@%spec.select4.6_0 main@%.pre.7_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.7_0
                        (ite main@%_42_0 main@%.pre.7_0 main@%spec.select4.6_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_43_0 (< main@%.212.i.6_0 main@%.pre32.7_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.7_0
                        (ite main@%_43_0 main@%.pre32.7_0 main@%.212.i.6_0)))
                 (=> main@._crit_edge28_0 a!21)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_44_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.8_0 (select main@%sm_0 main@%_44_0)))
                 (=> main@._crit_edge28_0 a!22)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_45_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.8_0 (select main@%sm1_0 main@%_45_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_46_0 (< main@%spec.select4.7_0 main@%.pre.8_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.8_0
                        (ite main@%_46_0 main@%.pre.8_0 main@%spec.select4.7_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_47_0 (< main@%.212.i.7_0 main@%.pre32.8_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.8_0
                        (ite main@%_47_0 main@%.pre32.8_0 main@%.212.i.7_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i_0 (ite main@%_15_0 1 0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.1_0 (ite main@%_19_0 2 main@%.215.i_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.2_0 (ite main@%_23_0 3 main@%.215.i.1_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.3_0 (ite main@%_27_0 4 main@%.215.i.2_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.4_0 (ite main@%_31_0 5 main@%.215.i.3_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.5_0 (ite main@%_35_0 6 main@%.215.i.4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.6_0 (ite main@%_39_0 7 main@%.215.i.5_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.7_0 (ite main@%_43_0 8 main@%.215.i.6_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.8_0 (ite main@%_47_0 9 main@%.215.i.7_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select_0 (ite main@%_14_0 1 0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.1_0
                        (ite main@%_18_0 2 main@%spec.select_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.2_0
                        (ite main@%_22_0 3 main@%spec.select.1_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.3_0
                        (ite main@%_26_0 4 main@%spec.select.2_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.4_0
                        (ite main@%_30_0 5 main@%spec.select.3_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.5_0
                        (ite main@%_34_0 6 main@%spec.select.4_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.6_0
                        (ite main@%_38_0 7 main@%spec.select.5_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.7_0
                        (ite main@%_42_0 8 main@%spec.select.6_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.8_0
                        (ite main@%_46_0 9 main@%spec.select.7_0)))
                 (=> main@._crit_edge28_0 a!23)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_48_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre.9_0 (select main@%sm_0 main@%_48_0)))
                 (=> main@._crit_edge28_0 a!24)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_49_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%.pre32.9_0 (select main@%sm1_0 main@%_49_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_50_0 (< main@%spec.select4.8_0 main@%.pre.9_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select.9_0
                        (ite main@%_50_0 10 main@%spec.select.8_0)))
                 (=> main@._crit_edge28_0
                     (= main@%spec.select4.9_0
                        (ite main@%_50_0 main@%.pre.9_0 main@%spec.select4.8_0)))
                 (=> main@._crit_edge28_0
                     (= main@%_51_0 (< main@%.212.i.8_0 main@%.pre32.9_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.215.i.9_0 (ite main@%_51_0 10 main@%.215.i.8_0)))
                 (=> main@._crit_edge28_0
                     (= main@%.212.i.9_0
                        (ite main@%_51_0 main@%.pre32.9_0 main@%.212.i.8_0)))
                 (=> main@._crit_edge28_0 a!25)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_52_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%_53_0 (select main@%sm1_0 main@%_52_0)))
                 (=> main@._crit_edge28_0 a!26)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_54_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%sm2_0
                        (store main@%sm1_0 main@%_54_0 main@%.212.i.9_0)))
                 (=> main@._crit_edge28_0 a!27)
                 (=> main@._crit_edge28_0 (or (<= @a_2_0 0) (> main@%_55_0 0)))
                 (=> main@._crit_edge28_0 (> @a_2_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%sm3_0 (store main@%sm2_0 main@%_55_0 main@%_53_0)))
                 (=> main@._crit_edge28_0 a!28)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_56_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%_57_0 (select main@%sm_0 main@%_56_0)))
                 (=> main@._crit_edge28_0 a!29)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_58_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%sm4_0
                        (store main@%sm_0 main@%_58_0 main@%spec.select4.9_0)))
                 (=> main@._crit_edge28_0 a!30)
                 (=> main@._crit_edge28_0 (or (<= @a_1_0 0) (> main@%_59_0 0)))
                 (=> main@._crit_edge28_0 (> @a_1_0 0))
                 (=> main@._crit_edge28_0
                     (= main@%sm5_0 (store main@%sm4_0 main@%_59_0 main@%_57_0)))
                 (=> main@_60_0 (and main@_60_0 main@._crit_edge28_0))
                 (=> (and main@_60_0 main@._crit_edge28_0) (= main@%.016.i_0 0))
                 (=> (and main@_60_0 main@._crit_edge28_0)
                     (= main@%.016.i_1 main@%.016.i_0))
                 main@_60_0)))
  (=> a!31 (main@_60 main@%.016.i_1 @a_1_0 main@%sm5_0 @a_2_0 main@%sm3_0)))))
(rule (let ((a!1 (and (main@_60 main@%.016.i_0 @a_1_0 main@%sm5_0 @a_2_0 main@%sm3_0)
                true
                (= main@%_61_0 (< main@%.016.i_0 10))
                main@%_61_0
                (= main@%_62_0 (+ @a_1_0 (* 0 44) (* main@%.016.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_62_0 0))
                (> @a_1_0 0)
                (= main@%_63_0 (select main@%sm5_0 main@%_62_0))
                (= main@%_64_0 (+ @a_2_0 (* 0 44) (* main@%.016.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_64_0 0))
                (> @a_2_0 0)
                (= main@%_65_0 (select main@%sm3_0 main@%_64_0))
                (= main@%_66_0 (= main@%_63_0 main@%_65_0))
                (= main@%_67_0 (+ main@%.016.i_0 1))
                (=> main@_60_1 (and main@_60_1 main@_60_0))
                (=> (and main@_60_1 main@_60_0) main@%_66_0)
                (=> (and main@_60_1 main@_60_0) (= main@%.016.i_1 main@%_67_0))
                (=> (and main@_60_1 main@_60_0)
                    (= main@%.016.i_2 main@%.016.i_1))
                main@_60_1)))
  (=> a!1 (main@_60 main@%.016.i_2 @a_1_0 main@%sm5_0 @a_2_0 main@%sm3_0))))
(rule (let ((a!1 (and (main@_60 main@%.016.i_0 @a_1_0 main@%sm5_0 @a_2_0 main@%sm3_0)
                true
                (= main@%_61_0 (< main@%.016.i_0 10))
                main@%_61_0
                (= main@%_62_0 (+ @a_1_0 (* 0 44) (* main@%.016.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_62_0 0))
                (> @a_1_0 0)
                (= main@%_63_0 (select main@%sm5_0 main@%_62_0))
                (= main@%_64_0 (+ @a_2_0 (* 0 44) (* main@%.016.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_64_0 0))
                (> @a_2_0 0)
                (= main@%_65_0 (select main@%sm3_0 main@%_64_0))
                (= main@%_66_0 (= main@%_63_0 main@%_65_0))
                (= main@%_67_0 (+ main@%.016.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_60_0))
                (=> (and main@verifier.error_0 main@_60_0) (not main@%_66_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

