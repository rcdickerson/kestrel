(set-info :original "./results/chc/bytecode/barthe/unaligned/loop-pipelining.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) Int Int (Array Int Int) (Array Int Int) (Array Int Int) ))
(declare-rel main@_3 (Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) ))
(declare-rel main@.preheader (Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) (Array Int Int) Int (Array Int Int) (Array Int Int) (Array Int Int) Int ))
(declare-rel main@_49 (Int Int (Array Int Int) Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int (Array Int Int) (Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel main@.lr.ph15 (Int (Array Int Int) Int (Array Int Int) Int Int (Array Int Int) Int (Array Int Int) Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%.phi.trans.insert_0 Int )
(declare-var main@%.pre_0 Int )
(declare-var main@%_87_0 Int )
(declare-var main@%_88_0 Int )
(declare-var main@%_89_0 Bool )
(declare-var main@%_81_0 Bool )
(declare-var main@%_82_0 Int )
(declare-var main@%_83_0 Int )
(declare-var main@%_84_0 Int )
(declare-var main@%_85_0 Int )
(declare-var main@%_86_0 Bool )
(declare-var main@%_90_0 Int )
(declare-var main@%_91_0 Int )
(declare-var main@%_92_0 Int )
(declare-var main@%_93_0 Int )
(declare-var main@%_94_0 Bool )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Int )
(declare-var main@%_67_0 Int )
(declare-var main@%sm17_0 (Array Int Int) )
(declare-var main@%_68_0 Int )
(declare-var main@%_69_0 Int )
(declare-var main@%_70_0 Int )
(declare-var main@%_71_0 Int )
(declare-var main@%_72_0 Int )
(declare-var main@%_73_0 Int )
(declare-var main@%_74_0 Int )
(declare-var main@%_75_0 Int )
(declare-var main@%_76_0 Bool )
(declare-var main@%_77_0 Int )
(declare-var main@%_78_0 Int )
(declare-var main@%_79_0 Bool )
(declare-var main@%or.cond_0 Bool )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@%_57_0 Int )
(declare-var main@%_58_0 Int )
(declare-var main@%_60_0 Int )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@%_63_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@%_41_0 Int )
(declare-var main@%_42_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%shadow.mem.12.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.20.0_2 (Array Int Int) )
(declare-var main@%_50_2 Int )
(declare-var main@%_51_2 Int )
(declare-var main@%.02.i4_2 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%_24_0 Bool )
(declare-var main@%shadow.mem.16.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%.01.i5_2 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_22_3 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%sm20_0 (Array Int Int) )
(declare-var main@%sm21_0 (Array Int Int) )
(declare-var main@%sm22_0 (Array Int Int) )
(declare-var main@%sm23_0 (Array Int Int) )
(declare-var main@%sm24_0 (Array Int Int) )
(declare-var main@%sm25_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var @b_1_0 Int )
(declare-var @b_2_0 Int )
(declare-var @c_1_0 Int )
(declare-var @c_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_3_0 Bool )
(declare-var main@%.0.i6_0 Int )
(declare-var main@%.0.i6_1 Int )
(declare-var main@_9_0 Bool )
(declare-var main@_15_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@_21_0 Bool )
(declare-var |tuple(main@_9_0, main@_21_0)| Bool )
(declare-var |tuple(main@_3_0, main@_21_0)| Bool )
(declare-var main@%_22_0 Bool )
(declare-var main@%_22_1 Bool )
(declare-var main@%_22_2 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@_3_1 Bool )
(declare-var main@%.0.i6_2 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%shadow.mem.16.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.01.i5_0 Int )
(declare-var main@%shadow.mem.16.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.01.i5_1 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@%_34_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@_36_0 Bool )
(declare-var main@%_39_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%_47_0 Int )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@_49_0 Bool )
(declare-var main@%shadow.mem.12.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.20.0_0 (Array Int Int) )
(declare-var main@%_50_0 Int )
(declare-var main@%_51_0 Int )
(declare-var main@%.02.i4_0 Int )
(declare-var main@%shadow.mem.12.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.20.0_1 (Array Int Int) )
(declare-var main@%_50_1 Int )
(declare-var main@%_51_1 Int )
(declare-var main@%.02.i4_1 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%sm14_0 (Array Int Int) )
(declare-var main@%_56_0 Int )
(declare-var main@%_59_0 Int )
(declare-var main@%sm15_0 (Array Int Int) )
(declare-var main@%sm16_0 (Array Int Int) )
(declare-var main@_49_1 Bool )
(declare-var main@_64_0 Bool )
(declare-var main@%sm18_0 (Array Int Int) )
(declare-var main@%sm19_0 (Array Int Int) )
(declare-var main@.lr.ph15_0 Bool )
(declare-var main@%.03.i114_0 Int )
(declare-var main@%.03.i114_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_95_0 Int )
(declare-var main@_80_0 Bool )
(declare-var main@..lr.ph_crit_edge_0 Bool )
(declare-var main@.lr.ph15_1 Bool )
(declare-var main@%.03.i114_2 Int )
(declare-var |tuple(main@_80_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@..lr.ph_crit_edge_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.lr.ph15_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm20_0
            main@%sm21_0
            main@%sm22_0
            main@%sm23_0
            main@%sm24_0
            main@%sm25_0))
(rule (=> (and (main@entry main@%sm20_0
                     main@%sm21_0
                     main@%sm22_0
                     main@%sm23_0
                     main@%sm24_0
                     main@%sm25_0)
         true
         (= main@%sm_0 main@%sm22_0)
         (= main@%sm3_0 main@%sm21_0)
         (= main@%sm4_0 main@%sm24_0)
         (= main@%sm5_0 main@%sm23_0)
         (= main@%sm6_0 main@%sm25_0)
         (= main@%sm7_0 main@%sm20_0)
         (= main@%_0_0 (= main@%loop.bound_0 7))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @b_2_0
                     @b_1_0
                     @a_1_0
                     @a_2_0
                     @c_1_0
                     @c_2_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%sm5_0
                     main@%sm7_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%sm6_0
                     main@%sm4_0
                     main@%sm_0)))
(rule (let ((a!1 (main@empty.loop @b_2_0
                            @b_1_0
                            @a_1_0
                            @a_2_0
                            @c_1_0
                            @c_2_0
                            main@%loop.bound_0
                            main@%sm3_0
                            main@%sm5_0
                            main@%sm7_0
                            main@%loop.bound1_0
                            main@%loop.bound2_0
                            main@%sm6_0
                            main@%sm4_0
                            main@%sm_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop @b_2_0
                          @b_1_0
                          @a_1_0
                          @a_2_0
                          @c_1_0
                          @c_2_0
                          main@%loop.bound_0
                          main@%sm3_0
                          main@%sm5_0
                          main@%sm7_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%sm6_0
                          main@%sm4_0
                          main@%sm_0)
         true
         (=> main@_3_0 (and main@_3_0 main@empty.loop_0))
         (=> (and main@_3_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i6_0 0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i6_1 main@%.0.i6_0))
         main@_3_0)
    (main@_3 @b_2_0
             @b_1_0
             @a_1_0
             @a_2_0
             @c_1_0
             @c_2_0
             main@%loop.bound_0
             main@%sm3_0
             main@%sm5_0
             main@%sm7_0
             main@%loop.bound1_0
             main@%.0.i6_1
             main@%loop.bound2_0
             main@%sm6_0
             main@%sm4_0
             main@%sm_0)))
(rule (let ((a!1 (=> main@_9_0
               (= main@%_10_0 (+ @b_1_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!2 (=> main@_9_0
               (= main@%_12_0 (+ @b_2_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!3 (=> main@_15_0
               (= main@%_16_0 (+ @c_1_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!4 (=> main@_15_0
               (= main@%_18_0 (+ @c_2_0 (* 0 40) (* main@%.0.i6_0 4))))))
(let ((a!5 (and (main@_3 @b_2_0
                         @b_1_0
                         @a_1_0
                         @a_2_0
                         @c_1_0
                         @c_2_0
                         main@%loop.bound_0
                         main@%sm3_0
                         main@%sm5_0
                         main@%sm7_0
                         main@%loop.bound1_0
                         main@%.0.i6_0
                         main@%loop.bound2_0
                         main@%sm6_0
                         main@%sm4_0
                         main@%sm_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i6_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_5_0 (select main@%sm_0 main@%_4_0))
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i6_0 4)))
                (or (<= @a_2_0 0) (> main@%_6_0 0))
                (> @a_2_0 0)
                (= main@%_7_0 (select main@%sm3_0 main@%_6_0))
                (= main@%_8_0 (= main@%_5_0 main@%_7_0))
                (=> main@_9_0 (and main@_9_0 main@_3_0))
                (=> (and main@_9_0 main@_3_0) main@%_8_0)
                a!1
                (=> main@_9_0 (or (<= @b_1_0 0) (> main@%_10_0 0)))
                (=> main@_9_0 (> @b_1_0 0))
                (=> main@_9_0 (= main@%_11_0 (select main@%sm4_0 main@%_10_0)))
                a!2
                (=> main@_9_0 (or (<= @b_2_0 0) (> main@%_12_0 0)))
                (=> main@_9_0 (> @b_2_0 0))
                (=> main@_9_0 (= main@%_13_0 (select main@%sm5_0 main@%_12_0)))
                (=> main@_9_0 (= main@%_14_0 (= main@%_11_0 main@%_13_0)))
                (=> main@_15_0 (and main@_15_0 main@_9_0))
                (=> (and main@_15_0 main@_9_0) main@%_14_0)
                a!3
                (=> main@_15_0 (or (<= @c_1_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @c_1_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm6_0 main@%_16_0)))
                a!4
                (=> main@_15_0 (or (<= @c_2_0 0) (> main@%_18_0 0)))
                (=> main@_15_0 (> @c_2_0 0))
                (=> main@_15_0 (= main@%_19_0 (select main@%sm7_0 main@%_18_0)))
                (=> main@_15_0 (= main@%_20_0 (= main@%_17_0 main@%_19_0)))
                (=> |tuple(main@_9_0, main@_21_0)| main@_9_0)
                (=> |tuple(main@_3_0, main@_21_0)| main@_3_0)
                (=> main@_21_0
                    (or (and main@_21_0 main@_15_0)
                        |tuple(main@_9_0, main@_21_0)|
                        |tuple(main@_3_0, main@_21_0)|))
                (=> |tuple(main@_9_0, main@_21_0)| (not main@%_14_0))
                (=> |tuple(main@_3_0, main@_21_0)| (not main@%_8_0))
                (=> (and main@_21_0 main@_15_0) (= main@%_22_0 main@%_20_0))
                (=> |tuple(main@_9_0, main@_21_0)| (= main@%_22_1 false))
                (=> |tuple(main@_3_0, main@_21_0)| (= main@%_22_2 false))
                (=> (and main@_21_0 main@_15_0) (= main@%_22_3 main@%_22_0))
                (=> |tuple(main@_9_0, main@_21_0)| (= main@%_22_3 main@%_22_1))
                (=> |tuple(main@_3_0, main@_21_0)| (= main@%_22_3 main@%_22_2))
                (=> main@_21_0 main@%_22_3)
                (=> main@_21_0 (= main@%_23_0 (+ main@%.0.i6_0 1)))
                (=> main@_21_0
                    (= main@%_24_0 (< main@%.0.i6_0 main@%loop.bound2_0)))
                (=> main@_3_1 (and main@_3_1 main@_21_0))
                (=> (and main@_3_1 main@_21_0) main@%_24_0)
                (=> (and main@_3_1 main@_21_0) (= main@%.0.i6_1 main@%_23_0))
                (=> (and main@_3_1 main@_21_0) (= main@%.0.i6_2 main@%.0.i6_1))
                main@_3_1)))
  (=> a!5
      (main@_3 @b_2_0
               @b_1_0
               @a_1_0
               @a_2_0
               @c_1_0
               @c_2_0
               main@%loop.bound_0
               main@%sm3_0
               main@%sm5_0
               main@%sm7_0
               main@%loop.bound1_0
               main@%.0.i6_2
               main@%loop.bound2_0
               main@%sm6_0
               main@%sm4_0
               main@%sm_0)))))
(rule (let ((a!1 (=> main@_9_0
               (= main@%_10_0 (+ @b_1_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!2 (=> main@_9_0
               (= main@%_12_0 (+ @b_2_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!3 (=> main@_15_0
               (= main@%_16_0 (+ @c_1_0 (* 0 40) (* main@%.0.i6_0 4)))))
      (a!4 (=> main@_15_0
               (= main@%_18_0 (+ @c_2_0 (* 0 40) (* main@%.0.i6_0 4))))))
(let ((a!5 (and (main@_3 @b_2_0
                         @b_1_0
                         @a_1_0
                         @a_2_0
                         @c_1_0
                         @c_2_0
                         main@%loop.bound_0
                         main@%sm3_0
                         main@%sm5_0
                         main@%sm7_0
                         main@%loop.bound1_0
                         main@%.0.i6_0
                         main@%loop.bound2_0
                         main@%sm6_0
                         main@%sm4_0
                         main@%sm_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i6_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_5_0 (select main@%sm_0 main@%_4_0))
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i6_0 4)))
                (or (<= @a_2_0 0) (> main@%_6_0 0))
                (> @a_2_0 0)
                (= main@%_7_0 (select main@%sm3_0 main@%_6_0))
                (= main@%_8_0 (= main@%_5_0 main@%_7_0))
                (=> main@_9_0 (and main@_9_0 main@_3_0))
                (=> (and main@_9_0 main@_3_0) main@%_8_0)
                a!1
                (=> main@_9_0 (or (<= @b_1_0 0) (> main@%_10_0 0)))
                (=> main@_9_0 (> @b_1_0 0))
                (=> main@_9_0 (= main@%_11_0 (select main@%sm4_0 main@%_10_0)))
                a!2
                (=> main@_9_0 (or (<= @b_2_0 0) (> main@%_12_0 0)))
                (=> main@_9_0 (> @b_2_0 0))
                (=> main@_9_0 (= main@%_13_0 (select main@%sm5_0 main@%_12_0)))
                (=> main@_9_0 (= main@%_14_0 (= main@%_11_0 main@%_13_0)))
                (=> main@_15_0 (and main@_15_0 main@_9_0))
                (=> (and main@_15_0 main@_9_0) main@%_14_0)
                a!3
                (=> main@_15_0 (or (<= @c_1_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @c_1_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm6_0 main@%_16_0)))
                a!4
                (=> main@_15_0 (or (<= @c_2_0 0) (> main@%_18_0 0)))
                (=> main@_15_0 (> @c_2_0 0))
                (=> main@_15_0 (= main@%_19_0 (select main@%sm7_0 main@%_18_0)))
                (=> main@_15_0 (= main@%_20_0 (= main@%_17_0 main@%_19_0)))
                (=> |tuple(main@_9_0, main@_21_0)| main@_9_0)
                (=> |tuple(main@_3_0, main@_21_0)| main@_3_0)
                (=> main@_21_0
                    (or (and main@_21_0 main@_15_0)
                        |tuple(main@_9_0, main@_21_0)|
                        |tuple(main@_3_0, main@_21_0)|))
                (=> |tuple(main@_9_0, main@_21_0)| (not main@%_14_0))
                (=> |tuple(main@_3_0, main@_21_0)| (not main@%_8_0))
                (=> (and main@_21_0 main@_15_0) (= main@%_22_0 main@%_20_0))
                (=> |tuple(main@_9_0, main@_21_0)| (= main@%_22_1 false))
                (=> |tuple(main@_3_0, main@_21_0)| (= main@%_22_2 false))
                (=> (and main@_21_0 main@_15_0) (= main@%_22_3 main@%_22_0))
                (=> |tuple(main@_9_0, main@_21_0)| (= main@%_22_3 main@%_22_1))
                (=> |tuple(main@_3_0, main@_21_0)| (= main@%_22_3 main@%_22_2))
                (=> main@_21_0 main@%_22_3)
                (=> main@_21_0 (= main@%_23_0 (+ main@%.0.i6_0 1)))
                (=> main@_21_0
                    (= main@%_24_0 (< main@%.0.i6_0 main@%loop.bound2_0)))
                (=> main@.preheader_0 (and main@.preheader_0 main@_21_0))
                (=> (and main@.preheader_0 main@_21_0) (not main@%_24_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.16.0_0 main@%sm6_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.8.0_0 main@%sm4_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@.preheader_0 main@_21_0) (= main@%.01.i5_0 0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.16.0_1 main@%shadow.mem.16.0_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.8.0_1 main@%shadow.mem.8.0_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader_0 main@_21_0)
                    (= main@%.01.i5_1 main@%.01.i5_0))
                main@.preheader_0)))
  (=> a!5
      (main@.preheader @b_2_0
                       @b_1_0
                       @a_1_0
                       @a_2_0
                       @c_1_0
                       @c_2_0
                       main@%loop.bound_0
                       main@%sm3_0
                       main@%sm5_0
                       main@%sm7_0
                       main@%.01.i5_1
                       main@%shadow.mem.0.0_1
                       main@%shadow.mem.8.0_1
                       main@%shadow.mem.16.0_1
                       main@%loop.bound1_0)))))
(rule (let ((a!1 (and (main@.preheader @b_2_0
                                 @b_1_0
                                 @a_1_0
                                 @a_2_0
                                 @c_1_0
                                 @c_2_0
                                 main@%loop.bound_0
                                 main@%sm3_0
                                 main@%sm5_0
                                 main@%sm7_0
                                 main@%.01.i5_0
                                 main@%shadow.mem.0.0_0
                                 main@%shadow.mem.8.0_0
                                 main@%shadow.mem.16.0_0
                                 main@%loop.bound1_0)
                true
                (= main@%_25_0 (+ @a_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @a_1_0 0) (> main@%_25_0 0))
                (> @a_1_0 0)
                (= main@%_26_0 (select main@%shadow.mem.0.0_0 main@%_25_0))
                (= main@%_27_0 (+ main@%_26_0 1))
                (> @a_1_0 0)
                (= main@%sm8_0
                   (store main@%shadow.mem.0.0_0 main@%_25_0 main@%_27_0))
                (= main@%_28_0 (+ @b_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @b_1_0 0) (> main@%_28_0 0))
                (> @b_1_0 0)
                (= main@%_29_0 (select main@%shadow.mem.8.0_0 main@%_28_0))
                (= main@%_30_0 (+ main@%_29_0 main@%_27_0))
                (> @b_1_0 0)
                (= main@%sm9_0
                   (store main@%shadow.mem.8.0_0 main@%_28_0 main@%_30_0))
                (= main@%_31_0 (+ @c_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @c_1_0 0) (> main@%_31_0 0))
                (> @c_1_0 0)
                (= main@%_32_0 (select main@%shadow.mem.16.0_0 main@%_31_0))
                (= main@%_33_0 (+ main@%_32_0 main@%_30_0))
                (> @c_1_0 0)
                (= main@%sm10_0
                   (store main@%shadow.mem.16.0_0 main@%_31_0 main@%_33_0))
                (= main@%_34_0 (+ main@%.01.i5_0 1))
                (= main@%_35_0 (< main@%.01.i5_0 main@%loop.bound1_0))
                (=> main@.preheader_1 (and main@.preheader_1 main@.preheader_0))
                (=> (and main@.preheader_1 main@.preheader_0) main@%_35_0)
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.16.0_1 main@%sm10_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.8.0_1 main@%sm9_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.0.0_1 main@%sm8_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.01.i5_1 main@%_34_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.16.0_2 main@%shadow.mem.16.0_1))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_1))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.01.i5_2 main@%.01.i5_1))
                main@.preheader_1)))
  (=> a!1
      (main@.preheader @b_2_0
                       @b_1_0
                       @a_1_0
                       @a_2_0
                       @c_1_0
                       @c_2_0
                       main@%loop.bound_0
                       main@%sm3_0
                       main@%sm5_0
                       main@%sm7_0
                       main@%.01.i5_2
                       main@%shadow.mem.0.0_2
                       main@%shadow.mem.8.0_2
                       main@%shadow.mem.16.0_2
                       main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_37_0 (+ (+ @a_2_0 (* 0 40)) (* 0 4))))
      (a!2 (= main@%_40_0 (+ (+ @a_2_0 (* 0 40)) (* 0 4))))
      (a!3 (=> main@_36_0 (= main@%_41_0 (+ @b_2_0 (* 0 40) (* 0 4)))))
      (a!4 (=> main@_36_0 (= main@%_44_0 (+ @b_2_0 (* 0 40) (* 0 4)))))
      (a!5 (= main@%_45_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4))))
      (a!6 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!7 (and (main@.preheader @b_2_0
                                 @b_1_0
                                 @a_1_0
                                 @a_2_0
                                 @c_1_0
                                 @c_2_0
                                 main@%loop.bound_0
                                 main@%sm3_0
                                 main@%sm5_0
                                 main@%sm7_0
                                 main@%.01.i5_0
                                 main@%shadow.mem.0.0_0
                                 main@%shadow.mem.8.0_0
                                 main@%shadow.mem.16.0_0
                                 main@%loop.bound1_0)
                true
                (= main@%_25_0 (+ @a_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @a_1_0 0) (> main@%_25_0 0))
                (> @a_1_0 0)
                (= main@%_26_0 (select main@%shadow.mem.0.0_0 main@%_25_0))
                (= main@%_27_0 (+ main@%_26_0 1))
                (> @a_1_0 0)
                (= main@%sm8_0
                   (store main@%shadow.mem.0.0_0 main@%_25_0 main@%_27_0))
                (= main@%_28_0 (+ @b_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @b_1_0 0) (> main@%_28_0 0))
                (> @b_1_0 0)
                (= main@%_29_0 (select main@%shadow.mem.8.0_0 main@%_28_0))
                (= main@%_30_0 (+ main@%_29_0 main@%_27_0))
                (> @b_1_0 0)
                (= main@%sm9_0
                   (store main@%shadow.mem.8.0_0 main@%_28_0 main@%_30_0))
                (= main@%_31_0 (+ @c_1_0 (* 0 40) (* main@%.01.i5_0 4)))
                (or (<= @c_1_0 0) (> main@%_31_0 0))
                (> @c_1_0 0)
                (= main@%_32_0 (select main@%shadow.mem.16.0_0 main@%_31_0))
                (= main@%_33_0 (+ main@%_32_0 main@%_30_0))
                (> @c_1_0 0)
                (= main@%sm10_0
                   (store main@%shadow.mem.16.0_0 main@%_31_0 main@%_33_0))
                (= main@%_34_0 (+ main@%.01.i5_0 1))
                (= main@%_35_0 (< main@%.01.i5_0 main@%loop.bound1_0))
                (=> main@_36_0 (and main@_36_0 main@.preheader_0))
                (=> (and main@_36_0 main@.preheader_0) (not main@%_35_0))
                (=> main@_36_0 a!1)
                (=> main@_36_0 (or (<= @a_2_0 0) (> main@%_37_0 0)))
                (=> main@_36_0 (= main@%_38_0 (select main@%sm3_0 main@%_37_0)))
                (=> main@_36_0 (= main@%_39_0 (+ main@%_38_0 1)))
                (=> main@_36_0 a!2)
                (=> main@_36_0 (or (<= @a_2_0 0) (> main@%_40_0 0)))
                (=> main@_36_0
                    (= main@%sm11_0 (store main@%sm3_0 main@%_40_0 main@%_39_0)))
                a!3
                (=> main@_36_0 (or (<= @b_2_0 0) (> main@%_41_0 0)))
                (=> main@_36_0 (= main@%_42_0 (select main@%sm5_0 main@%_41_0)))
                (=> main@_36_0 (= main@%_43_0 (+ main@%_42_0 main@%_39_0)))
                a!4
                (=> main@_36_0 (or (<= @b_2_0 0) (> main@%_44_0 0)))
                (=> main@_36_0
                    (= main@%sm12_0 (store main@%sm5_0 main@%_44_0 main@%_43_0)))
                (=> main@_36_0 a!5)
                (=> main@_36_0 (or (<= @a_2_0 0) (> main@%_45_0 0)))
                (=> main@_36_0 (> @a_2_0 0))
                (=> main@_36_0 (= main@%_46_0 (select main@%sm3_0 main@%_45_0)))
                (=> main@_36_0 (= main@%_47_0 (+ main@%_46_0 1)))
                (=> main@_36_0 a!6)
                (=> main@_36_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_36_0 (> @a_2_0 0))
                (=> main@_36_0
                    (= main@%sm13_0
                       (store main@%sm11_0 main@%_48_0 main@%_47_0)))
                (=> main@_49_0 (and main@_49_0 main@_36_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.12.0_0 main@%sm12_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.4.0_0 main@%sm13_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.20.0_0 main@%sm7_0))
                (=> (and main@_49_0 main@_36_0) (= main@%_50_0 main@%_43_0))
                (=> (and main@_49_0 main@_36_0) (= main@%_51_0 main@%_47_0))
                (=> (and main@_49_0 main@_36_0) (= main@%.02.i4_0 0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.12.0_1 main@%shadow.mem.12.0_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%shadow.mem.20.0_1 main@%shadow.mem.20.0_0))
                (=> (and main@_49_0 main@_36_0) (= main@%_50_1 main@%_50_0))
                (=> (and main@_49_0 main@_36_0) (= main@%_51_1 main@%_51_0))
                (=> (and main@_49_0 main@_36_0)
                    (= main@%.02.i4_1 main@%.02.i4_0))
                main@_49_0)))
  (=> a!7
      (main@_49 @b_2_0
                @b_1_0
                main@%sm9_0
                @a_1_0
                main@%sm8_0
                @a_2_0
                @c_1_0
                main@%sm10_0
                @c_2_0
                main@%_39_0
                main@%_43_0
                main@%.02.i4_1
                main@%shadow.mem.4.0_1
                main@%shadow.mem.12.0_1
                main@%_51_1
                main@%shadow.mem.20.0_1
                main@%_50_1
                main@%loop.bound_0)))))
(rule (let ((a!1 (and (main@_49 @b_2_0
                          @b_1_0
                          main@%sm9_0
                          @a_1_0
                          main@%sm8_0
                          @a_2_0
                          @c_1_0
                          main@%sm10_0
                          @c_2_0
                          main@%_39_0
                          main@%_43_0
                          main@%.02.i4_0
                          main@%shadow.mem.4.0_0
                          main@%shadow.mem.12.0_0
                          main@%_51_0
                          main@%shadow.mem.20.0_0
                          main@%_50_0
                          main@%loop.bound_0)
                true
                (= main@%_52_0 (+ main@%.02.i4_0 2))
                (= main@%_53_0 (+ @a_2_0 (* 0 40) (* main@%_52_0 4)))
                (or (<= @a_2_0 0) (> main@%_53_0 0))
                (> @a_2_0 0)
                (= main@%_54_0 (select main@%shadow.mem.4.0_0 main@%_53_0))
                (= main@%_55_0 (+ main@%_54_0 1))
                (> @a_2_0 0)
                (= main@%sm14_0
                   (store main@%shadow.mem.4.0_0 main@%_53_0 main@%_55_0))
                (= main@%_56_0 (+ main@%.02.i4_0 1))
                (= main@%_57_0 (+ @b_2_0 (* 0 40) (* main@%_56_0 4)))
                (or (<= @b_2_0 0) (> main@%_57_0 0))
                (> @b_2_0 0)
                (= main@%_58_0 (select main@%shadow.mem.12.0_0 main@%_57_0))
                (= main@%_59_0 (+ main@%_51_0 main@%_58_0))
                (> @b_2_0 0)
                (= main@%sm15_0
                   (store main@%shadow.mem.12.0_0 main@%_57_0 main@%_59_0))
                (= main@%_60_0 (+ @c_2_0 (* 0 40) (* main@%.02.i4_0 4)))
                (or (<= @c_2_0 0) (> main@%_60_0 0))
                (> @c_2_0 0)
                (= main@%_61_0 (select main@%shadow.mem.20.0_0 main@%_60_0))
                (= main@%_62_0 (+ main@%_50_0 main@%_61_0))
                (> @c_2_0 0)
                (= main@%sm16_0
                   (store main@%shadow.mem.20.0_0 main@%_60_0 main@%_62_0))
                (= main@%_63_0 (< main@%.02.i4_0 main@%loop.bound_0))
                (=> main@_49_1 (and main@_49_1 main@_49_0))
                (=> (and main@_49_1 main@_49_0) main@%_63_0)
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.12.0_1 main@%sm15_0))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.4.0_1 main@%sm14_0))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.20.0_1 main@%sm16_0))
                (=> (and main@_49_1 main@_49_0) (= main@%_50_1 main@%_59_0))
                (=> (and main@_49_1 main@_49_0) (= main@%_51_1 main@%_55_0))
                (=> (and main@_49_1 main@_49_0) (= main@%.02.i4_1 main@%_56_0))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_1))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%shadow.mem.20.0_2 main@%shadow.mem.20.0_1))
                (=> (and main@_49_1 main@_49_0) (= main@%_50_2 main@%_50_1))
                (=> (and main@_49_1 main@_49_0) (= main@%_51_2 main@%_51_1))
                (=> (and main@_49_1 main@_49_0)
                    (= main@%.02.i4_2 main@%.02.i4_1))
                main@_49_1)))
  (=> a!1
      (main@_49 @b_2_0
                @b_1_0
                main@%sm9_0
                @a_1_0
                main@%sm8_0
                @a_2_0
                @c_1_0
                main@%sm10_0
                @c_2_0
                main@%_39_0
                main@%_43_0
                main@%.02.i4_2
                main@%shadow.mem.4.0_2
                main@%shadow.mem.12.0_2
                main@%_51_2
                main@%shadow.mem.20.0_2
                main@%_50_2
                main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_57_0 (+ (+ @b_2_0 (* 0 40)) (* main@%_56_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @c_2_0 (* 0 40)) (* main@%.02.i4_0 4))))
      (a!3 (= main@%_65_0 (+ (+ @c_2_0 (* 0 40)) (* main@%_56_0 4))))
      (a!4 (= main@%_68_0 (+ (+ @b_2_0 (* 0 40)) (* main@%_52_0 4))))
      (a!5 (= main@%_71_0 (+ (+ @c_2_0 (* 0 40)) (* main@%_52_0 4))))
      (a!6 (=> main@_64_0 (= main@%_74_0 (+ @a_1_0 (* 0 40) (* 0 4)))))
      (a!7 (=> main@_64_0 (= main@%_77_0 (+ @b_1_0 (* 0 40) (* 0 4))))))
(let ((a!8 (and (main@_49 @b_2_0
                          @b_1_0
                          main@%sm9_0
                          @a_1_0
                          main@%sm8_0
                          @a_2_0
                          @c_1_0
                          main@%sm10_0
                          @c_2_0
                          main@%_39_0
                          main@%_43_0
                          main@%.02.i4_0
                          main@%shadow.mem.4.0_0
                          main@%shadow.mem.12.0_0
                          main@%_51_0
                          main@%shadow.mem.20.0_0
                          main@%_50_0
                          main@%loop.bound_0)
                true
                (= main@%_52_0 (+ main@%.02.i4_0 2))
                (= main@%_53_0 (+ @a_2_0 (* 0 40) (* main@%_52_0 4)))
                (or (<= @a_2_0 0) (> main@%_53_0 0))
                (> @a_2_0 0)
                (= main@%_54_0 (select main@%shadow.mem.4.0_0 main@%_53_0))
                (= main@%_55_0 (+ main@%_54_0 1))
                (> @a_2_0 0)
                (= main@%sm14_0
                   (store main@%shadow.mem.4.0_0 main@%_53_0 main@%_55_0))
                (= main@%_56_0 (+ main@%.02.i4_0 1))
                a!1
                (or (<= @b_2_0 0) (> main@%_57_0 0))
                (> @b_2_0 0)
                (= main@%_58_0 (select main@%shadow.mem.12.0_0 main@%_57_0))
                (= main@%_59_0 (+ main@%_51_0 main@%_58_0))
                (> @b_2_0 0)
                (= main@%sm15_0
                   (store main@%shadow.mem.12.0_0 main@%_57_0 main@%_59_0))
                a!2
                (or (<= @c_2_0 0) (> main@%_60_0 0))
                (> @c_2_0 0)
                (= main@%_61_0 (select main@%shadow.mem.20.0_0 main@%_60_0))
                (= main@%_62_0 (+ main@%_50_0 main@%_61_0))
                (> @c_2_0 0)
                (= main@%sm16_0
                   (store main@%shadow.mem.20.0_0 main@%_60_0 main@%_62_0))
                (= main@%_63_0 (< main@%.02.i4_0 main@%loop.bound_0))
                (=> main@_64_0 (and main@_64_0 main@_49_0))
                (=> (and main@_64_0 main@_49_0) (not main@%_63_0))
                (=> main@_64_0 a!3)
                (=> main@_64_0 (or (<= @c_2_0 0) (> main@%_65_0 0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%_66_0 (select main@%sm16_0 main@%_65_0)))
                (=> main@_64_0 (= main@%_67_0 (+ main@%_59_0 main@%_66_0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%sm17_0
                       (store main@%sm16_0 main@%_65_0 main@%_67_0)))
                (=> main@_64_0 a!4)
                (=> main@_64_0 (or (<= @b_2_0 0) (> main@%_68_0 0)))
                (=> main@_64_0 (> @b_2_0 0))
                (=> main@_64_0
                    (= main@%_69_0 (select main@%sm15_0 main@%_68_0)))
                (=> main@_64_0 (= main@%_70_0 (+ main@%_55_0 main@%_69_0)))
                (=> main@_64_0 (> @b_2_0 0))
                (=> main@_64_0
                    (= main@%sm18_0
                       (store main@%sm15_0 main@%_68_0 main@%_70_0)))
                (=> main@_64_0 a!5)
                (=> main@_64_0 (or (<= @c_2_0 0) (> main@%_71_0 0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%_72_0 (select main@%sm16_0 main@%_71_0)))
                (=> main@_64_0 (= main@%_73_0 (+ main@%_72_0 main@%_70_0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%sm19_0
                       (store main@%sm17_0 main@%_71_0 main@%_73_0)))
                true
                a!6
                (=> main@_64_0 (or (<= @a_1_0 0) (> main@%_74_0 0)))
                (=> main@_64_0 (= main@%_75_0 (select main@%sm8_0 main@%_74_0)))
                (=> main@_64_0 (= main@%_76_0 (= main@%_75_0 main@%_39_0)))
                a!7
                (=> main@_64_0 (or (<= @b_1_0 0) (> main@%_77_0 0)))
                (=> main@_64_0 (= main@%_78_0 (select main@%sm9_0 main@%_77_0)))
                (=> main@_64_0 (= main@%_79_0 (= main@%_78_0 main@%_43_0)))
                (=> main@_64_0
                    (= main@%or.cond_0 (ite main@%_76_0 main@%_79_0 false)))
                (=> main@.lr.ph15_0 (and main@.lr.ph15_0 main@_64_0))
                (=> (and main@.lr.ph15_0 main@_64_0) main@%or.cond_0)
                (=> (and main@.lr.ph15_0 main@_64_0) (= main@%.03.i114_0 0))
                (=> (and main@.lr.ph15_0 main@_64_0)
                    (= main@%.03.i114_1 main@%.03.i114_0))
                main@.lr.ph15_0)))
  (=> a!8
      (main@.lr.ph15 @b_2_0
                     main@%sm18_0
                     @b_1_0
                     main@%sm9_0
                     main@%.03.i114_1
                     @a_1_0
                     main@%sm8_0
                     @a_2_0
                     main@%sm14_0
                     @c_1_0
                     main@%sm10_0
                     @c_2_0
                     main@%sm19_0)))))
(rule (let ((a!1 (= main@%_57_0 (+ (+ @b_2_0 (* 0 40)) (* main@%_56_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @c_2_0 (* 0 40)) (* main@%.02.i4_0 4))))
      (a!3 (= main@%_65_0 (+ (+ @c_2_0 (* 0 40)) (* main@%_56_0 4))))
      (a!4 (= main@%_68_0 (+ (+ @b_2_0 (* 0 40)) (* main@%_52_0 4))))
      (a!5 (= main@%_71_0 (+ (+ @c_2_0 (* 0 40)) (* main@%_52_0 4))))
      (a!6 (=> main@_64_0 (= main@%_74_0 (+ @a_1_0 (* 0 40) (* 0 4)))))
      (a!7 (=> main@_64_0 (= main@%_77_0 (+ @b_1_0 (* 0 40) (* 0 4))))))
(let ((a!8 (and (main@_49 @b_2_0
                          @b_1_0
                          main@%sm9_0
                          @a_1_0
                          main@%sm8_0
                          @a_2_0
                          @c_1_0
                          main@%sm10_0
                          @c_2_0
                          main@%_39_0
                          main@%_43_0
                          main@%.02.i4_0
                          main@%shadow.mem.4.0_0
                          main@%shadow.mem.12.0_0
                          main@%_51_0
                          main@%shadow.mem.20.0_0
                          main@%_50_0
                          main@%loop.bound_0)
                true
                (= main@%_52_0 (+ main@%.02.i4_0 2))
                (= main@%_53_0 (+ @a_2_0 (* 0 40) (* main@%_52_0 4)))
                (or (<= @a_2_0 0) (> main@%_53_0 0))
                (> @a_2_0 0)
                (= main@%_54_0 (select main@%shadow.mem.4.0_0 main@%_53_0))
                (= main@%_55_0 (+ main@%_54_0 1))
                (> @a_2_0 0)
                (= main@%sm14_0
                   (store main@%shadow.mem.4.0_0 main@%_53_0 main@%_55_0))
                (= main@%_56_0 (+ main@%.02.i4_0 1))
                a!1
                (or (<= @b_2_0 0) (> main@%_57_0 0))
                (> @b_2_0 0)
                (= main@%_58_0 (select main@%shadow.mem.12.0_0 main@%_57_0))
                (= main@%_59_0 (+ main@%_51_0 main@%_58_0))
                (> @b_2_0 0)
                (= main@%sm15_0
                   (store main@%shadow.mem.12.0_0 main@%_57_0 main@%_59_0))
                a!2
                (or (<= @c_2_0 0) (> main@%_60_0 0))
                (> @c_2_0 0)
                (= main@%_61_0 (select main@%shadow.mem.20.0_0 main@%_60_0))
                (= main@%_62_0 (+ main@%_50_0 main@%_61_0))
                (> @c_2_0 0)
                (= main@%sm16_0
                   (store main@%shadow.mem.20.0_0 main@%_60_0 main@%_62_0))
                (= main@%_63_0 (< main@%.02.i4_0 main@%loop.bound_0))
                (=> main@_64_0 (and main@_64_0 main@_49_0))
                (=> (and main@_64_0 main@_49_0) (not main@%_63_0))
                (=> main@_64_0 a!3)
                (=> main@_64_0 (or (<= @c_2_0 0) (> main@%_65_0 0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%_66_0 (select main@%sm16_0 main@%_65_0)))
                (=> main@_64_0 (= main@%_67_0 (+ main@%_59_0 main@%_66_0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%sm17_0
                       (store main@%sm16_0 main@%_65_0 main@%_67_0)))
                (=> main@_64_0 a!4)
                (=> main@_64_0 (or (<= @b_2_0 0) (> main@%_68_0 0)))
                (=> main@_64_0 (> @b_2_0 0))
                (=> main@_64_0
                    (= main@%_69_0 (select main@%sm15_0 main@%_68_0)))
                (=> main@_64_0 (= main@%_70_0 (+ main@%_55_0 main@%_69_0)))
                (=> main@_64_0 (> @b_2_0 0))
                (=> main@_64_0
                    (= main@%sm18_0
                       (store main@%sm15_0 main@%_68_0 main@%_70_0)))
                (=> main@_64_0 a!5)
                (=> main@_64_0 (or (<= @c_2_0 0) (> main@%_71_0 0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%_72_0 (select main@%sm16_0 main@%_71_0)))
                (=> main@_64_0 (= main@%_73_0 (+ main@%_72_0 main@%_70_0)))
                (=> main@_64_0 (> @c_2_0 0))
                (=> main@_64_0
                    (= main@%sm19_0
                       (store main@%sm17_0 main@%_71_0 main@%_73_0)))
                true
                a!6
                (=> main@_64_0 (or (<= @a_1_0 0) (> main@%_74_0 0)))
                (=> main@_64_0 (= main@%_75_0 (select main@%sm8_0 main@%_74_0)))
                (=> main@_64_0 (= main@%_76_0 (= main@%_75_0 main@%_39_0)))
                a!7
                (=> main@_64_0 (or (<= @b_1_0 0) (> main@%_77_0 0)))
                (=> main@_64_0 (= main@%_78_0 (select main@%sm9_0 main@%_77_0)))
                (=> main@_64_0 (= main@%_79_0 (= main@%_78_0 main@%_43_0)))
                (=> main@_64_0
                    (= main@%or.cond_0 (ite main@%_76_0 main@%_79_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_64_0))
                (=> (and main@verifier.error_0 main@_64_0)
                    (not main@%or.cond_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!8 main@verifier.error.split))))
(rule (let ((a!1 (=> main@_80_0 (= main@%_82_0 (+ @a_1_0 (* 0 40) (* main@%_95_0 4)))))
      (a!2 (=> main@_80_0 (= main@%_84_0 (+ @a_2_0 (* 0 40) (* main@%_95_0 4)))))
      (a!3 (=> main@..lr.ph_crit_edge_0
               (= main@%.phi.trans.insert_0
                  (+ @b_2_0 (* 0 40) (* main@%_95_0 4)))))
      (a!4 (=> main@..lr.ph_crit_edge_0
               (= main@%_87_0 (+ @b_1_0 (* 0 40) (* main@%_95_0 4))))))
(let ((a!5 (and (main@.lr.ph15 @b_2_0
                               main@%sm18_0
                               @b_1_0
                               main@%sm9_0
                               main@%.03.i114_0
                               @a_1_0
                               main@%sm8_0
                               @a_2_0
                               main@%sm14_0
                               @c_1_0
                               main@%sm10_0
                               @c_2_0
                               main@%sm19_0)
                true
                (= main@%_90_0 (+ @c_1_0 (* 0 40) (* main@%.03.i114_0 4)))
                (or (<= @c_1_0 0) (> main@%_90_0 0))
                (> @c_1_0 0)
                (= main@%_91_0 (select main@%sm10_0 main@%_90_0))
                (= main@%_92_0 (+ @c_2_0 (* 0 40) (* main@%.03.i114_0 4)))
                (or (<= @c_2_0 0) (> main@%_92_0 0))
                (> @c_2_0 0)
                (= main@%_93_0 (select main@%sm19_0 main@%_92_0))
                (= main@%_94_0 (= main@%_91_0 main@%_93_0))
                (= main@%_95_0 (+ main@%.03.i114_0 1))
                (=> main@_80_0 (and main@_80_0 main@.lr.ph15_0))
                (=> (and main@_80_0 main@.lr.ph15_0) main@%_94_0)
                (=> main@_80_0 (= main@%_81_0 (< main@%.03.i114_0 9)))
                (=> main@_80_0 main@%_81_0)
                a!1
                (=> main@_80_0 (or (<= @a_1_0 0) (> main@%_82_0 0)))
                (=> main@_80_0 (> @a_1_0 0))
                (=> main@_80_0 (= main@%_83_0 (select main@%sm8_0 main@%_82_0)))
                a!2
                (=> main@_80_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_80_0 (> @a_2_0 0))
                (=> main@_80_0
                    (= main@%_85_0 (select main@%sm14_0 main@%_84_0)))
                (=> main@_80_0 (= main@%_86_0 (= main@%_83_0 main@%_85_0)))
                (=> main@..lr.ph_crit_edge_0
                    (and main@..lr.ph_crit_edge_0 main@_80_0))
                (=> (and main@..lr.ph_crit_edge_0 main@_80_0) main@%_86_0)
                a!3
                (=> main@..lr.ph_crit_edge_0
                    (or (<= @b_2_0 0) (> main@%.phi.trans.insert_0 0)))
                (=> main@..lr.ph_crit_edge_0 (> @b_2_0 0))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%.pre_0
                       (select main@%sm18_0 main@%.phi.trans.insert_0)))
                a!4
                (=> main@..lr.ph_crit_edge_0
                    (or (<= @b_1_0 0) (> main@%_87_0 0)))
                (=> main@..lr.ph_crit_edge_0 (> @b_1_0 0))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%_88_0 (select main@%sm9_0 main@%_87_0)))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%_89_0 (= main@%_88_0 main@%.pre_0)))
                (=> main@.lr.ph15_1
                    (and main@.lr.ph15_1 main@..lr.ph_crit_edge_0))
                (=> (and main@.lr.ph15_1 main@..lr.ph_crit_edge_0) main@%_89_0)
                (=> (and main@.lr.ph15_1 main@..lr.ph_crit_edge_0)
                    (= main@%.03.i114_1 main@%_95_0))
                (=> (and main@.lr.ph15_1 main@..lr.ph_crit_edge_0)
                    (= main@%.03.i114_2 main@%.03.i114_1))
                main@.lr.ph15_1)))
  (=> a!5
      (main@.lr.ph15 @b_2_0
                     main@%sm18_0
                     @b_1_0
                     main@%sm9_0
                     main@%.03.i114_2
                     @a_1_0
                     main@%sm8_0
                     @a_2_0
                     main@%sm14_0
                     @c_1_0
                     main@%sm10_0
                     @c_2_0
                     main@%sm19_0)))))
(rule (let ((a!1 (=> main@_80_0 (= main@%_82_0 (+ @a_1_0 (* 0 40) (* main@%_95_0 4)))))
      (a!2 (=> main@_80_0 (= main@%_84_0 (+ @a_2_0 (* 0 40) (* main@%_95_0 4)))))
      (a!3 (=> main@..lr.ph_crit_edge_0
               (= main@%.phi.trans.insert_0
                  (+ @b_2_0 (* 0 40) (* main@%_95_0 4)))))
      (a!4 (=> main@..lr.ph_crit_edge_0
               (= main@%_87_0 (+ @b_1_0 (* 0 40) (* main@%_95_0 4))))))
(let ((a!5 (and (main@.lr.ph15 @b_2_0
                               main@%sm18_0
                               @b_1_0
                               main@%sm9_0
                               main@%.03.i114_0
                               @a_1_0
                               main@%sm8_0
                               @a_2_0
                               main@%sm14_0
                               @c_1_0
                               main@%sm10_0
                               @c_2_0
                               main@%sm19_0)
                true
                (= main@%_90_0 (+ @c_1_0 (* 0 40) (* main@%.03.i114_0 4)))
                (or (<= @c_1_0 0) (> main@%_90_0 0))
                (> @c_1_0 0)
                (= main@%_91_0 (select main@%sm10_0 main@%_90_0))
                (= main@%_92_0 (+ @c_2_0 (* 0 40) (* main@%.03.i114_0 4)))
                (or (<= @c_2_0 0) (> main@%_92_0 0))
                (> @c_2_0 0)
                (= main@%_93_0 (select main@%sm19_0 main@%_92_0))
                (= main@%_94_0 (= main@%_91_0 main@%_93_0))
                (= main@%_95_0 (+ main@%.03.i114_0 1))
                (=> main@_80_0 (and main@_80_0 main@.lr.ph15_0))
                (=> (and main@_80_0 main@.lr.ph15_0) main@%_94_0)
                (=> main@_80_0 (= main@%_81_0 (< main@%.03.i114_0 9)))
                (=> main@_80_0 main@%_81_0)
                a!1
                (=> main@_80_0 (or (<= @a_1_0 0) (> main@%_82_0 0)))
                (=> main@_80_0 (> @a_1_0 0))
                (=> main@_80_0 (= main@%_83_0 (select main@%sm8_0 main@%_82_0)))
                a!2
                (=> main@_80_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_80_0 (> @a_2_0 0))
                (=> main@_80_0
                    (= main@%_85_0 (select main@%sm14_0 main@%_84_0)))
                (=> main@_80_0 (= main@%_86_0 (= main@%_83_0 main@%_85_0)))
                (=> main@..lr.ph_crit_edge_0
                    (and main@..lr.ph_crit_edge_0 main@_80_0))
                (=> (and main@..lr.ph_crit_edge_0 main@_80_0) main@%_86_0)
                a!3
                (=> main@..lr.ph_crit_edge_0
                    (or (<= @b_2_0 0) (> main@%.phi.trans.insert_0 0)))
                (=> main@..lr.ph_crit_edge_0 (> @b_2_0 0))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%.pre_0
                       (select main@%sm18_0 main@%.phi.trans.insert_0)))
                a!4
                (=> main@..lr.ph_crit_edge_0
                    (or (<= @b_1_0 0) (> main@%_87_0 0)))
                (=> main@..lr.ph_crit_edge_0 (> @b_1_0 0))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%_88_0 (select main@%sm9_0 main@%_87_0)))
                (=> main@..lr.ph_crit_edge_0
                    (= main@%_89_0 (= main@%_88_0 main@%.pre_0)))
                (=> |tuple(main@_80_0, main@verifier.error_0)| main@_80_0)
                (=> |tuple(main@..lr.ph_crit_edge_0, main@verifier.error_0)|
                    main@..lr.ph_crit_edge_0)
                (=> |tuple(main@.lr.ph15_0, main@verifier.error_0)|
                    main@.lr.ph15_0)
                (=> main@verifier.error_0
                    (or |tuple(main@_80_0, main@verifier.error_0)|
                        |tuple(main@..lr.ph_crit_edge_0, main@verifier.error_0)|
                        |tuple(main@.lr.ph15_0, main@verifier.error_0)|))
                (=> |tuple(main@_80_0, main@verifier.error_0)|
                    (not main@%_86_0))
                (=> |tuple(main@..lr.ph_crit_edge_0, main@verifier.error_0)|
                    (not main@%_89_0))
                (=> |tuple(main@.lr.ph15_0, main@verifier.error_0)|
                    (not main@%_94_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(query main@verifier.error.split)

