(set-info :original "./results/chc/bytecode/barthe/count-loops/code-sinking.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) Int ))
(declare-rel main@_6 (Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) Int Int ))
(declare-rel main@.lr.ph19 (Int Int (Array Int Int) (Array Int Int) Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@_68 (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_69_0 Bool )
(declare-var main@%_70_0 Int )
(declare-var main@%_71_0 Int )
(declare-var main@%_72_0 Int )
(declare-var main@%_73_0 Int )
(declare-var main@%_74_0 Bool )
(declare-var main@%_64_0 Int )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Int )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%_67_0 Int )
(declare-var main@%.017.i_2 Int )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_56_0 Int )
(declare-var main@%_49_0 Int )
(declare-var main@%_50_0 Int )
(declare-var main@%_51_0 Bool )
(declare-var main@%_52_0 Bool )
(declare-var main@%_58_0 Bool )
(declare-var main@%_46_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Bool )
(declare-var main@%spec.select11.us79_2 Int )
(declare-var main@%spec.select10.us78_2 Int )
(declare-var main@%.210.i15.us77_2 Int )
(declare-var main@%_45_0 Bool )
(declare-var main@%_59_0 Int )
(declare-var main@%_60_0 Int )
(declare-var main@%_61_0 Bool )
(declare-var main@%_63_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%.pre_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%spec.select5_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%.213.i_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%.pre.1_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%spec.select5.1_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%.213.i.1_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%.pre.2_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%spec.select5.2_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Bool )
(declare-var main@%.213.i.2_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%.pre.3_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%spec.select5.3_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Bool )
(declare-var main@%.213.i.3_0 Int )
(declare-var main@%.216.i_0 Int )
(declare-var main@%.216.i.1_0 Int )
(declare-var main@%.216.i.2_0 Int )
(declare-var main@%.216.i.3_0 Int )
(declare-var main@%spec.select_0 Int )
(declare-var main@%spec.select.1_0 Int )
(declare-var main@%spec.select.2_0 Int )
(declare-var main@%spec.select.3_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%.pre.4_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%_40_0 Int )
(declare-var main@%_41_0 Int )
(declare-var main@%_42_0 Bool )
(declare-var main@%.216.i.4_0 Int )
(declare-var main@%.213.i.4_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%_44_0 Int )
(declare-var main@%.2.i18_2 Int )
(declare-var main@%.24.i17_2 Int )
(declare-var main@%.17.i16_2 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%_13_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i30_2 Int )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@%sm12_0 (Array Int Int) )
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
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_6_0 Bool )
(declare-var main@%.0.i30_0 Int )
(declare-var main@%.0.i30_1 Int )
(declare-var main@%_12_0 Int )
(declare-var main@_6_1 Bool )
(declare-var main@._crit_edge32_0 Bool )
(declare-var main@%spec.select.4_0 Int )
(declare-var main@%spec.select5.4_0 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@.lr.ph19_0 Bool )
(declare-var main@%.2.i18_0 Int )
(declare-var main@%.24.i17_0 Int )
(declare-var main@%.17.i16_0 Int )
(declare-var main@%.2.i18_1 Int )
(declare-var main@%.24.i17_1 Int )
(declare-var main@%.17.i16_1 Int )
(declare-var main@%spec.select8_0 Int )
(declare-var main@%spec.select9_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@.lr.ph19_1 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@.lr.ph.split.us.preheader_0 Bool )
(declare-var main@%spec.select10.us75_0 Int )
(declare-var main@%spec.select11.us76_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%spec.select11.us79_0 Int )
(declare-var main@%spec.select10.us78_0 Int )
(declare-var main@%.210.i15.us77_0 Int )
(declare-var main@%spec.select11.us79_1 Int )
(declare-var main@%spec.select10.us78_1 Int )
(declare-var main@%.210.i15.us77_1 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@_68_0 Bool )
(declare-var main@%.017.i_0 Int )
(declare-var main@%.017.i_1 Int )
(declare-var main@%_57_0 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%spec.select10.us_0 Int )
(declare-var main@%spec.select11.us_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@.thread40_0 Bool )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var |tuple(main@.lr.ph_0, main@._crit_edge_0)| Bool )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%_75_0 Int )
(declare-var main@_68_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm11_0 main@%sm12_0))
(rule (=> (and (main@entry main@%sm11_0 main@%sm12_0)
         true
         (= main@%sm_0 main@%sm12_0)
         (= main@%sm4_0 main@%sm11_0)
         (= main@%_0_0 (= main@%loop.bound_0 10))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 10))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 10))
         main@%_2_0
         (= main@%_3_0 (= main@%loop.bound3_0 9))
         main@%_3_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%sm_0
                     main@%loop.bound1_0
                     main@%loop.bound_0
                     main@%_5_0
                     main@%_4_0
                     main@%loop.bound2_0
                     main@%sm4_0
                     main@%loop.bound3_0)))
(rule (let ((a!1 (main@empty.loop @a_1_0
                            @a_2_0
                            main@%sm_0
                            main@%loop.bound1_0
                            main@%loop.bound_0
                            main@%_5_0
                            main@%_4_0
                            main@%loop.bound2_0
                            main@%sm4_0
                            main@%loop.bound3_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%loop.bound1_0
                          main@%loop.bound_0
                          main@%_5_0
                          main@%_4_0
                          main@%loop.bound2_0
                          main@%sm4_0
                          main@%loop.bound3_0)
         true
         (=> main@_6_0 (and main@_6_0 main@empty.loop_0))
         (=> (and main@_6_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_6_0 main@empty.loop_0) (= main@%.0.i30_0 0))
         (=> (and main@_6_0 main@empty.loop_0)
             (= main@%.0.i30_1 main@%.0.i30_0))
         main@_6_0)
    (main@_6 @a_1_0
             @a_2_0
             main@%sm_0
             main@%loop.bound1_0
             main@%loop.bound_0
             main@%_5_0
             main@%_4_0
             main@%loop.bound2_0
             main@%sm4_0
             main@%.0.i30_1
             main@%loop.bound3_0)))
(rule (let ((a!1 (and (main@_6 @a_1_0
                         @a_2_0
                         main@%sm_0
                         main@%loop.bound1_0
                         main@%loop.bound_0
                         main@%_5_0
                         main@%_4_0
                         main@%loop.bound2_0
                         main@%sm4_0
                         main@%.0.i30_0
                         main@%loop.bound3_0)
                true
                (= main@%_7_0 (+ @a_1_0 (* 0 44) (* main@%.0.i30_0 4)))
                (or (<= @a_1_0 0) (> main@%_7_0 0))
                (> @a_1_0 0)
                (= main@%_8_0 (select main@%sm_0 main@%_7_0))
                (= main@%_9_0 (+ @a_2_0 (* 0 44) (* main@%.0.i30_0 4)))
                (or (<= @a_2_0 0) (> main@%_9_0 0))
                (> @a_2_0 0)
                (= main@%_10_0 (select main@%sm4_0 main@%_9_0))
                (= main@%_11_0 (= main@%_8_0 main@%_10_0))
                main@%_11_0
                (= main@%_12_0 (+ main@%.0.i30_0 1))
                (= main@%_13_0 (< main@%.0.i30_0 main@%loop.bound3_0))
                (=> main@_6_1 (and main@_6_1 main@_6_0))
                (=> (and main@_6_1 main@_6_0) main@%_13_0)
                (=> (and main@_6_1 main@_6_0) (= main@%.0.i30_1 main@%_12_0))
                (=> (and main@_6_1 main@_6_0) (= main@%.0.i30_2 main@%.0.i30_1))
                main@_6_1)))
  (=> a!1
      (main@_6 @a_1_0
               @a_2_0
               main@%sm_0
               main@%loop.bound1_0
               main@%loop.bound_0
               main@%_5_0
               main@%_4_0
               main@%loop.bound2_0
               main@%sm4_0
               main@%.0.i30_2
               main@%loop.bound3_0))))
(rule (let ((a!1 (= main@%_7_0 (+ (+ @a_1_0 (* 0 44)) (* main@%.0.i30_0 4))))
      (a!2 (= main@%_9_0 (+ (+ @a_2_0 (* 0 44)) (* main@%.0.i30_0 4))))
      (a!3 (= main@%_14_0 (+ (+ @a_1_0 (* 0 44)) (* 0 4))))
      (a!4 (= main@%_16_0 (+ (+ @a_2_0 (* 0 44)) (* 0 4))))
      (a!5 (= main@%_18_0 (+ (+ @a_1_0 (* 0 44)) (* 1 4))))
      (a!6 (= main@%_20_0 (+ (+ @a_2_0 (* 0 44)) (* 2 4))))
      (a!7 (= main@%_23_0 (+ (+ @a_1_0 (* 0 44)) (* 2 4))))
      (a!8 (= main@%_25_0 (+ (+ @a_2_0 (* 0 44)) (* 4 4))))
      (a!9 (= main@%_28_0 (+ (+ @a_1_0 (* 0 44)) (* 3 4))))
      (a!10 (= main@%_30_0 (+ (+ @a_2_0 (* 0 44)) (* 6 4))))
      (a!11 (= main@%_33_0 (+ (+ @a_1_0 (* 0 44)) (* 4 4))))
      (a!12 (= main@%_35_0 (+ (+ @a_2_0 (* 0 44)) (* 8 4))))
      (a!13 (= main@%_38_0 (+ (+ @a_1_0 (* 0 44)) (* 5 4))))
      (a!14 (= main@%_40_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!15 (= main@%_43_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!16 (= main@%_44_0 (+ (+ @a_2_0 (* 0 44)) (* main@%.216.i.4_0 4)))))
(let ((a!17 (and (main@_6 @a_1_0
                          @a_2_0
                          main@%sm_0
                          main@%loop.bound1_0
                          main@%loop.bound_0
                          main@%_5_0
                          main@%_4_0
                          main@%loop.bound2_0
                          main@%sm4_0
                          main@%.0.i30_0
                          main@%loop.bound3_0)
                 true
                 a!1
                 (or (<= @a_1_0 0) (> main@%_7_0 0))
                 (> @a_1_0 0)
                 (= main@%_8_0 (select main@%sm_0 main@%_7_0))
                 a!2
                 (or (<= @a_2_0 0) (> main@%_9_0 0))
                 (> @a_2_0 0)
                 (= main@%_10_0 (select main@%sm4_0 main@%_9_0))
                 (= main@%_11_0 (= main@%_8_0 main@%_10_0))
                 main@%_11_0
                 (= main@%_12_0 (+ main@%.0.i30_0 1))
                 (= main@%_13_0 (< main@%.0.i30_0 main@%loop.bound3_0))
                 (=> main@._crit_edge32_0 (and main@._crit_edge32_0 main@_6_0))
                 (=> (and main@._crit_edge32_0 main@_6_0) (not main@%_13_0))
                 (=> main@._crit_edge32_0 a!3)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_14_0 0)))
                 (=> main@._crit_edge32_0
                     (= main@%_15_0 (select main@%sm_0 main@%_14_0)))
                 (=> main@._crit_edge32_0 a!4)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_16_0 0)))
                 (=> main@._crit_edge32_0
                     (= main@%_17_0 (select main@%sm4_0 main@%_16_0)))
                 (=> main@._crit_edge32_0 a!5)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_18_0 0)))
                 (=> main@._crit_edge32_0 (> @a_1_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%.pre_0 (select main@%sm_0 main@%_18_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_19_0 (< main@%_15_0 main@%.pre_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select5_0
                        (ite main@%_19_0 main@%.pre_0 main@%_15_0)))
                 (=> main@._crit_edge32_0 a!6)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_20_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%_21_0 (select main@%sm4_0 main@%_20_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_22_0 (< main@%_17_0 main@%_21_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.213.i_0
                        (ite main@%_22_0 main@%_21_0 main@%_17_0)))
                 (=> main@._crit_edge32_0 a!7)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_23_0 0)))
                 (=> main@._crit_edge32_0 (> @a_1_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%.pre.1_0 (select main@%sm_0 main@%_23_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_24_0 (< main@%spec.select5_0 main@%.pre.1_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select5.1_0
                        (ite main@%_24_0 main@%.pre.1_0 main@%spec.select5_0)))
                 (=> main@._crit_edge32_0 a!8)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_25_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%_26_0 (select main@%sm4_0 main@%_25_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_27_0 (< main@%.213.i_0 main@%_26_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.213.i.1_0
                        (ite main@%_27_0 main@%_26_0 main@%.213.i_0)))
                 (=> main@._crit_edge32_0 a!9)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_28_0 0)))
                 (=> main@._crit_edge32_0 (> @a_1_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%.pre.2_0 (select main@%sm_0 main@%_28_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_29_0 (< main@%spec.select5.1_0 main@%.pre.2_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select5.2_0
                        (ite main@%_29_0 main@%.pre.2_0 main@%spec.select5.1_0)))
                 (=> main@._crit_edge32_0 a!10)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_30_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%_31_0 (select main@%sm4_0 main@%_30_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_32_0 (< main@%.213.i.1_0 main@%_31_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.213.i.2_0
                        (ite main@%_32_0 main@%_31_0 main@%.213.i.1_0)))
                 (=> main@._crit_edge32_0 a!11)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_33_0 0)))
                 (=> main@._crit_edge32_0 (> @a_1_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%.pre.3_0 (select main@%sm_0 main@%_33_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_34_0 (< main@%spec.select5.2_0 main@%.pre.3_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select5.3_0
                        (ite main@%_34_0 main@%.pre.3_0 main@%spec.select5.2_0)))
                 (=> main@._crit_edge32_0 a!12)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_35_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%_36_0 (select main@%sm4_0 main@%_35_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_37_0 (< main@%.213.i.2_0 main@%_36_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.213.i.3_0
                        (ite main@%_37_0 main@%_36_0 main@%.213.i.2_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.216.i_0 (ite main@%_22_0 2 0)))
                 (=> main@._crit_edge32_0
                     (= main@%.216.i.1_0 (ite main@%_27_0 4 main@%.216.i_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.216.i.2_0 (ite main@%_32_0 6 main@%.216.i.1_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.216.i.3_0 (ite main@%_37_0 8 main@%.216.i.2_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select_0 (ite main@%_19_0 1 0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select.1_0
                        (ite main@%_24_0 2 main@%spec.select_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select.2_0
                        (ite main@%_29_0 3 main@%spec.select.1_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select.3_0
                        (ite main@%_34_0 4 main@%spec.select.2_0)))
                 (=> main@._crit_edge32_0 a!13)
                 (=> main@._crit_edge32_0 (or (<= @a_1_0 0) (> main@%_38_0 0)))
                 (=> main@._crit_edge32_0 (> @a_1_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%.pre.4_0 (select main@%sm_0 main@%_38_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_39_0 (< main@%spec.select5.3_0 main@%.pre.4_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select.4_0
                        (ite main@%_39_0 5 main@%spec.select.3_0)))
                 (=> main@._crit_edge32_0
                     (= main@%spec.select5.4_0
                        (ite main@%_39_0 main@%.pre.4_0 main@%spec.select5.3_0)))
                 (=> main@._crit_edge32_0 a!14)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_40_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%_41_0 (select main@%sm4_0 main@%_40_0)))
                 (=> main@._crit_edge32_0
                     (= main@%_42_0 (< main@%.213.i.3_0 main@%_41_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.216.i.4_0 (ite main@%_42_0 10 main@%.216.i.3_0)))
                 (=> main@._crit_edge32_0
                     (= main@%.213.i.4_0
                        (ite main@%_42_0 main@%_41_0 main@%.213.i.3_0)))
                 (=> main@._crit_edge32_0 a!15)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_43_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%sm5_0
                        (store main@%sm4_0 main@%_43_0 main@%.213.i.4_0)))
                 (=> main@._crit_edge32_0 a!16)
                 (=> main@._crit_edge32_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                 (=> main@._crit_edge32_0 (> @a_2_0 0))
                 (=> main@._crit_edge32_0
                     (= main@%sm6_0 (store main@%sm5_0 main@%_44_0 main@%_41_0)))
                 (=> main@.lr.ph19_0 (and main@.lr.ph19_0 main@._crit_edge32_0))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.2.i18_0 main@%spec.select5.4_0))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.24.i17_0 main@%spec.select.4_0))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.17.i16_0 6))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.2.i18_1 main@%.2.i18_0))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.24.i17_1 main@%.24.i17_0))
                 (=> (and main@.lr.ph19_0 main@._crit_edge32_0)
                     (= main@%.17.i16_1 main@%.17.i16_0))
                 main@.lr.ph19_0)))
  (=> a!17
      (main@.lr.ph19 @a_1_0
                     @a_2_0
                     main@%sm_0
                     main@%sm6_0
                     main@%loop.bound1_0
                     main@%loop.bound_0
                     main@%_5_0
                     main@%_4_0
                     main@%.17.i16_1
                     main@%.2.i18_1
                     main@%.24.i17_1
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (and (main@.lr.ph19 @a_1_0
                               @a_2_0
                               main@%sm_0
                               main@%sm6_0
                               main@%loop.bound1_0
                               main@%loop.bound_0
                               main@%_5_0
                               main@%_4_0
                               main@%.17.i16_0
                               main@%.2.i18_0
                               main@%.24.i17_0
                               main@%loop.bound2_0)
                true
                (= main@%_59_0 (+ @a_1_0 (* 0 44) (* main@%.17.i16_0 4)))
                (or (<= @a_1_0 0) (> main@%_59_0 0))
                (> @a_1_0 0)
                (= main@%_60_0 (select main@%sm_0 main@%_59_0))
                (= main@%_61_0 (< main@%.2.i18_0 main@%_60_0))
                (= main@%spec.select8_0
                   (ite main@%_61_0 main@%.17.i16_0 main@%.24.i17_0))
                (= main@%spec.select9_0
                   (ite main@%_61_0 main@%_60_0 main@%.2.i18_0))
                (= main@%_62_0 (+ main@%.17.i16_0 1))
                (= main@%_63_0 (< main@%.17.i16_0 main@%loop.bound2_0))
                (=> main@.lr.ph19_1 (and main@.lr.ph19_1 main@.lr.ph19_0))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0) main@%_63_0)
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.2.i18_1 main@%spec.select9_0))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.24.i17_1 main@%spec.select8_0))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.17.i16_1 main@%_62_0))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.2.i18_2 main@%.2.i18_1))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.24.i17_2 main@%.24.i17_1))
                (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
                    (= main@%.17.i16_2 main@%.17.i16_1))
                main@.lr.ph19_1)))
  (=> a!1
      (main@.lr.ph19 @a_1_0
                     @a_2_0
                     main@%sm_0
                     main@%sm6_0
                     main@%loop.bound1_0
                     main@%loop.bound_0
                     main@%_5_0
                     main@%_4_0
                     main@%.17.i16_2
                     main@%.2.i18_2
                     main@%.24.i17_2
                     main@%loop.bound2_0))))
(rule (let ((a!1 (=> main@.lr.ph.split.us.preheader_0
               (= main@%_46_0 (+ @a_2_0 (* 1 44) (* 0 4))))))
(let ((a!2 (and (main@.lr.ph19 @a_1_0
                               @a_2_0
                               main@%sm_0
                               main@%sm6_0
                               main@%loop.bound1_0
                               main@%loop.bound_0
                               main@%_5_0
                               main@%_4_0
                               main@%.17.i16_0
                               main@%.2.i18_0
                               main@%.24.i17_0
                               main@%loop.bound2_0)
                true
                (= main@%_59_0 (+ @a_1_0 (* 0 44) (* main@%.17.i16_0 4)))
                (or (<= @a_1_0 0) (> main@%_59_0 0))
                (> @a_1_0 0)
                (= main@%_60_0 (select main@%sm_0 main@%_59_0))
                (= main@%_61_0 (< main@%.2.i18_0 main@%_60_0))
                (= main@%spec.select8_0
                   (ite main@%_61_0 main@%.17.i16_0 main@%.24.i17_0))
                (= main@%spec.select9_0
                   (ite main@%_61_0 main@%_60_0 main@%.2.i18_0))
                (= main@%_62_0 (+ main@%.17.i16_0 1))
                (= main@%_63_0 (< main@%.17.i16_0 main@%loop.bound2_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph19_0))
                (=> (and main@.preheader_0 main@.lr.ph19_0) (not main@%_63_0))
                (=> main@.preheader_0 (= main@%_45_0 (and true false)))
                (=> main@.lr.ph.split.us.preheader_0
                    (and main@.lr.ph.split.us.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us.preheader_0 main@.preheader_0)
                    main@%_45_0)
                a!1
                (=> main@.lr.ph.split.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_46_0 0)))
                (=> main@.lr.ph.split.us.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph.split.us.preheader_0
                    (= main@%_47_0 (select main@%sm6_0 main@%_46_0)))
                (=> main@.lr.ph.split.us.preheader_0
                    (= main@%_48_0 (< main@%_5_0 main@%_47_0)))
                (=> main@.lr.ph.split.us.preheader_0
                    (= main@%spec.select10.us75_0
                       (ite main@%_48_0 main@%_47_0 main@%_5_0)))
                (=> main@.lr.ph.split.us.preheader_0
                    (= main@%spec.select11.us76_0
                       (ite main@%_48_0 11 main@%_4_0)))
                (=> main@.lr.ph_0
                    (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%spec.select11.us79_0 main@%spec.select11.us76_0))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%spec.select10.us78_0 main@%spec.select10.us75_0))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%.210.i15.us77_0 11))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%spec.select11.us79_1 main@%spec.select11.us79_0))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%spec.select10.us78_1 main@%spec.select10.us78_0))
                (=> (and main@.lr.ph_0 main@.lr.ph.split.us.preheader_0)
                    (= main@%.210.i15.us77_1 main@%.210.i15.us77_0))
                main@.lr.ph_0)))
  (=> a!2
      (main@.lr.ph @a_1_0
                   @a_2_0
                   main@%sm_0
                   main@%spec.select9_0
                   main@%spec.select8_0
                   main@%sm6_0
                   main@%spec.select10.us78_1
                   main@%spec.select11.us79_1
                   main@%loop.bound1_0
                   main@%.210.i15.us77_1
                   main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_59_0 (+ (+ @a_1_0 (* 0 44)) (* main@%.17.i16_0 4))))
      (a!2 (= main@%_64_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!3 (= main@%_66_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!4 (= main@%_67_0 (+ (+ @a_1_0 (* 0 44)) (* main@%spec.select8_0 4)))))
(let ((a!5 (and (main@.lr.ph19 @a_1_0
                               @a_2_0
                               main@%sm_0
                               main@%sm6_0
                               main@%loop.bound1_0
                               main@%loop.bound_0
                               main@%_5_0
                               main@%_4_0
                               main@%.17.i16_0
                               main@%.2.i18_0
                               main@%.24.i17_0
                               main@%loop.bound2_0)
                true
                a!1
                (or (<= @a_1_0 0) (> main@%_59_0 0))
                (> @a_1_0 0)
                (= main@%_60_0 (select main@%sm_0 main@%_59_0))
                (= main@%_61_0 (< main@%.2.i18_0 main@%_60_0))
                (= main@%spec.select8_0
                   (ite main@%_61_0 main@%.17.i16_0 main@%.24.i17_0))
                (= main@%spec.select9_0
                   (ite main@%_61_0 main@%_60_0 main@%.2.i18_0))
                (= main@%_62_0 (+ main@%.17.i16_0 1))
                (= main@%_63_0 (< main@%.17.i16_0 main@%loop.bound2_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph19_0))
                (=> (and main@.preheader_0 main@.lr.ph19_0) (not main@%_63_0))
                (=> main@.preheader_0 (= main@%_45_0 (and true false)))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (not main@%_45_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.0_0 main@%sm6_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> main@._crit_edge_0 a!2)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_64_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%_65_0 (select main@%sm_0 main@%_64_0)))
                (=> main@._crit_edge_0 a!3)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_66_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm9_0
                       (store main@%sm_0 main@%_66_0 main@%spec.select9_0)))
                (=> main@._crit_edge_0 a!4)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm10_0 (store main@%sm9_0 main@%_67_0 main@%_65_0)))
                (=> main@_68_0 (and main@_68_0 main@._crit_edge_0))
                (=> (and main@_68_0 main@._crit_edge_0) (= main@%.017.i_0 0))
                (=> (and main@_68_0 main@._crit_edge_0)
                    (= main@%.017.i_1 main@%.017.i_0))
                main@_68_0)))
  (=> a!5
      (main@_68 main@%.017.i_1
                @a_1_0
                main@%sm10_0
                @a_2_0
                main@%shadow.mem.4.0_1)))))
(rule (let ((a!1 (=> main@.lr.ph.split.us_0
               (= main@%_49_0 (+ @a_2_0 (* 0 44) (* main@%_57_0 4))))))
(let ((a!2 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%sm_0
                             main@%spec.select9_0
                             main@%spec.select8_0
                             main@%sm6_0
                             main@%spec.select10.us78_0
                             main@%spec.select11.us79_0
                             main@%loop.bound1_0
                             main@%.210.i15.us77_0
                             main@%loop.bound_0)
                true
                (= main@%_57_0 (+ main@%.210.i15.us77_0 1))
                (= main@%_58_0 (< main@%.210.i15.us77_0 main@%loop.bound_0))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_58_0)
                a!1
                (=> main@.lr.ph.split.us_0 (or (<= @a_2_0 0) (> main@%_49_0 0)))
                (=> main@.lr.ph.split.us_0 (> @a_2_0 0))
                (=> main@.lr.ph.split.us_0
                    (= main@%_50_0 (select main@%sm6_0 main@%_49_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%_51_0 (< main@%spec.select10.us78_0 main@%_50_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%spec.select10.us_0
                       (ite main@%_51_0 main@%_50_0 main@%spec.select10.us78_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%spec.select11.us_0
                       (ite main@%_51_0 main@%_57_0 main@%spec.select11.us79_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%_52_0 (= main@%_57_0 main@%loop.bound1_0)))
                (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph.split.us_0))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (not main@%_52_0))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%spec.select11.us79_1 main@%spec.select11.us_0))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%spec.select10.us78_1 main@%spec.select10.us_0))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%.210.i15.us77_1 main@%_57_0))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%spec.select11.us79_2 main@%spec.select11.us79_1))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%spec.select10.us78_2 main@%spec.select10.us78_1))
                (=> (and main@.lr.ph_1 main@.lr.ph.split.us_0)
                    (= main@%.210.i15.us77_2 main@%.210.i15.us77_1))
                main@.lr.ph_1)))
  (=> a!2
      (main@.lr.ph @a_1_0
                   @a_2_0
                   main@%sm_0
                   main@%spec.select9_0
                   main@%spec.select8_0
                   main@%sm6_0
                   main@%spec.select10.us78_2
                   main@%spec.select11.us79_2
                   main@%loop.bound1_0
                   main@%.210.i15.us77_2
                   main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_49_0 (+ (+ @a_2_0 (* 0 44)) (* main@%_57_0 4))))
      (a!2 (= main@%_53_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!3 (= main@%_55_0 (+ (+ @a_2_0 (* 0 44)) (* 10 4))))
      (a!4 (= main@%_56_0
              (+ (+ @a_2_0 (* 0 44)) (* main@%spec.select11.us_0 4))))
      (a!5 (= main@%_64_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!6 (= main@%_66_0 (+ (+ @a_1_0 (* 0 44)) (* 10 4))))
      (a!7 (= main@%_67_0 (+ (+ @a_1_0 (* 0 44)) (* main@%spec.select8_0 4)))))
(let ((a!8 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%sm_0
                             main@%spec.select9_0
                             main@%spec.select8_0
                             main@%sm6_0
                             main@%spec.select10.us78_0
                             main@%spec.select11.us79_0
                             main@%loop.bound1_0
                             main@%.210.i15.us77_0
                             main@%loop.bound_0)
                true
                (= main@%_57_0 (+ main@%.210.i15.us77_0 1))
                (= main@%_58_0 (< main@%.210.i15.us77_0 main@%loop.bound_0))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.lr.ph_0))
                (=> (and main@.lr.ph.split.us_0 main@.lr.ph_0) main@%_58_0)
                (=> main@.lr.ph.split.us_0 a!1)
                (=> main@.lr.ph.split.us_0 (or (<= @a_2_0 0) (> main@%_49_0 0)))
                (=> main@.lr.ph.split.us_0 (> @a_2_0 0))
                (=> main@.lr.ph.split.us_0
                    (= main@%_50_0 (select main@%sm6_0 main@%_49_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%_51_0 (< main@%spec.select10.us78_0 main@%_50_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%spec.select10.us_0
                       (ite main@%_51_0 main@%_50_0 main@%spec.select10.us78_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%spec.select11.us_0
                       (ite main@%_51_0 main@%_57_0 main@%spec.select11.us79_0)))
                (=> main@.lr.ph.split.us_0
                    (= main@%_52_0 (= main@%_57_0 main@%loop.bound1_0)))
                (=> main@.thread40_0
                    (and main@.thread40_0 main@.lr.ph.split.us_0))
                (=> (and main@.thread40_0 main@.lr.ph.split.us_0) main@%_52_0)
                (=> main@.thread40_0 a!2)
                (=> main@.thread40_0 (or (<= @a_2_0 0) (> main@%_53_0 0)))
                (=> main@.thread40_0 (> @a_2_0 0))
                (=> main@.thread40_0
                    (= main@%_54_0 (select main@%sm6_0 main@%_53_0)))
                (=> main@.thread40_0 a!3)
                (=> main@.thread40_0 (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@.thread40_0 (> @a_2_0 0))
                (=> main@.thread40_0
                    (= main@%sm7_0
                       (store main@%sm6_0 main@%_55_0 main@%spec.select10.us_0)))
                (=> main@.thread40_0 a!4)
                (=> main@.thread40_0 (or (<= @a_2_0 0) (> main@%_56_0 0)))
                (=> main@.thread40_0 (> @a_2_0 0))
                (=> main@.thread40_0
                    (= main@%sm8_0 (store main@%sm7_0 main@%_56_0 main@%_54_0)))
                (=> |tuple(main@.lr.ph_0, main@._crit_edge_0)| main@.lr.ph_0)
                (=> main@._crit_edge_0
                    (or |tuple(main@.lr.ph_0, main@._crit_edge_0)|
                        (and main@._crit_edge_0 main@.thread40_0)))
                (=> |tuple(main@.lr.ph_0, main@._crit_edge_0)|
                    (not main@%_58_0))
                (=> |tuple(main@.lr.ph_0, main@._crit_edge_0)|
                    (= main@%shadow.mem.4.0_0 main@%sm6_0))
                (=> (and main@._crit_edge_0 main@.thread40_0)
                    (= main@%shadow.mem.4.0_1 main@%sm8_0))
                (=> |tuple(main@.lr.ph_0, main@._crit_edge_0)|
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_0))
                (=> (and main@._crit_edge_0 main@.thread40_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> main@._crit_edge_0 a!5)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_64_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%_65_0 (select main@%sm_0 main@%_64_0)))
                (=> main@._crit_edge_0 a!6)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_66_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm9_0
                       (store main@%sm_0 main@%_66_0 main@%spec.select9_0)))
                (=> main@._crit_edge_0 a!7)
                (=> main@._crit_edge_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@._crit_edge_0 (> @a_1_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm10_0 (store main@%sm9_0 main@%_67_0 main@%_65_0)))
                (=> main@_68_0 (and main@_68_0 main@._crit_edge_0))
                (=> (and main@_68_0 main@._crit_edge_0) (= main@%.017.i_0 0))
                (=> (and main@_68_0 main@._crit_edge_0)
                    (= main@%.017.i_1 main@%.017.i_0))
                main@_68_0)))
  (=> a!8
      (main@_68 main@%.017.i_1
                @a_1_0
                main@%sm10_0
                @a_2_0
                main@%shadow.mem.4.0_2)))))
(rule (let ((a!1 (and (main@_68 main@%.017.i_0
                          @a_1_0
                          main@%sm10_0
                          @a_2_0
                          main@%shadow.mem.4.0_0)
                true
                (= main@%_69_0 (< main@%.017.i_0 10))
                main@%_69_0
                (= main@%_70_0 (+ @a_1_0 (* 0 44) (* main@%.017.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_70_0 0))
                (> @a_1_0 0)
                (= main@%_71_0 (select main@%sm10_0 main@%_70_0))
                (= main@%_72_0 (+ @a_2_0 (* 0 44) (* main@%.017.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_72_0 0))
                (> @a_2_0 0)
                (= main@%_73_0 (select main@%shadow.mem.4.0_0 main@%_72_0))
                (= main@%_74_0 (= main@%_71_0 main@%_73_0))
                (= main@%_75_0 (+ main@%.017.i_0 1))
                (=> main@_68_1 (and main@_68_1 main@_68_0))
                (=> (and main@_68_1 main@_68_0) main@%_74_0)
                (=> (and main@_68_1 main@_68_0) (= main@%.017.i_1 main@%_75_0))
                (=> (and main@_68_1 main@_68_0)
                    (= main@%.017.i_2 main@%.017.i_1))
                main@_68_1)))
  (=> a!1
      (main@_68 main@%.017.i_2
                @a_1_0
                main@%sm10_0
                @a_2_0
                main@%shadow.mem.4.0_0))))
(rule (let ((a!1 (and (main@_68 main@%.017.i_0
                          @a_1_0
                          main@%sm10_0
                          @a_2_0
                          main@%shadow.mem.4.0_0)
                true
                (= main@%_69_0 (< main@%.017.i_0 10))
                main@%_69_0
                (= main@%_70_0 (+ @a_1_0 (* 0 44) (* main@%.017.i_0 4)))
                (or (<= @a_1_0 0) (> main@%_70_0 0))
                (> @a_1_0 0)
                (= main@%_71_0 (select main@%sm10_0 main@%_70_0))
                (= main@%_72_0 (+ @a_2_0 (* 0 44) (* main@%.017.i_0 4)))
                (or (<= @a_2_0 0) (> main@%_72_0 0))
                (> @a_2_0 0)
                (= main@%_73_0 (select main@%shadow.mem.4.0_0 main@%_72_0))
                (= main@%_74_0 (= main@%_71_0 main@%_73_0))
                (= main@%_75_0 (+ main@%.017.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_68_0))
                (=> (and main@verifier.error_0 main@_68_0) (not main@%_74_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

