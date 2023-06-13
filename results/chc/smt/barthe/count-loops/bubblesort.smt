(set-info :original "./results/chc/bytecode/barthe/count-loops/bubblesort.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@_5 (Int Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@.preheader28 (Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@.lr.ph41 (Int Int Int Int Int Bool Int (Array Int Int) Int Int (Array Int Int) Int ))
(declare-rel main@.lr.ph45 (Int Int Int Int Int (Array Int Int) Int Bool Int Int Bool (Array Int Int) Int Int ))
(declare-rel main@.lr.ph48 (Int Int Int Int Int (Array Int Int) Int Bool Int Int (Array Int Int) Int Int Int ))
(declare-rel main@.lr.ph37.preheader (Int Int Int Int (Array Int Int) Bool Int Int (Array Int Int) Bool ))
(declare-rel main@.lr.ph37 (Int Int Int Int (Array Int Int) Bool Int Int Bool (Array Int Int) Int ))
(declare-rel main@.lr.ph34.us.preheader (Int (Array Int Int) Int Int Int (Array Int Int) Bool ))
(declare-rel main@.lr.ph34.us (Int (Array Int Int) Int Int Int Bool (Array Int Int) Int ))
(declare-rel main@.lr.ph83 (Int Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_118_0 Bool )
(declare-var main@%_120_0 Bool )
(declare-var main@%or.cond22_0 Bool )
(declare-var main@%_110_0 Bool )
(declare-var main@%_111_0 Int )
(declare-var main@%_113_0 Int )
(declare-var main@%_115_0 Bool )
(declare-var main@%_117_0 Bool )
(declare-var main@%or.cond20_0 Bool )
(declare-var main@%_106_0 Bool )
(declare-var main@%_108_0 Bool )
(declare-var main@%or.cond2281_0 Bool )
(declare-var main@%.05.i3182_2 Int )
(declare-var main@%_99_0 Int )
(declare-var main@%_101_0 Int )
(declare-var main@%_103_0 Bool )
(declare-var main@%_105_0 Bool )
(declare-var main@%or.cond2030_0 Bool )
(declare-var main@%_87_0 Bool )
(declare-var main@%_84_0 Int )
(declare-var main@%_80_0 Int )
(declare-var main@%_82_0 Bool )
(declare-var main@%_77_0 Int )
(declare-var main@%_76_2 Bool )
(declare-var main@%_71_0 Bool )
(declare-var main@%_72_0 Bool )
(declare-var main@%_97_0 Bool )
(declare-var main@%_94_0 Int )
(declare-var main@%_90_0 Int )
(declare-var main@%_92_0 Bool )
(declare-var main@%_70_0 Int )
(declare-var main@%_69_2 Bool )
(declare-var main@%_25_0 Bool )
(declare-var main@%_26_0 Bool )
(declare-var main@%_67_0 Bool )
(declare-var main@%_63_0 Bool )
(declare-var main@%_60_0 Int )
(declare-var main@%_56_0 Int )
(declare-var main@%_58_0 Bool )
(declare-var main@%_53_0 Int )
(declare-var main@%.not_0 Bool )
(declare-var main@%_51_0 Bool )
(declare-var main@%_48_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%_46_0 Bool )
(declare-var main@%_41_0 Int )
(declare-var main@%_37_0 Bool )
(declare-var main@%_34_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_32_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%or.cond_0 Bool )
(declare-var main@%_19_3 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%sm16_0 (Array Int Int) )
(declare-var main@%sm17_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%loop.bound4_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_5_0 Bool )
(declare-var main@%.0.i52_0 Int )
(declare-var main@%.0.i52_1 Int )
(declare-var main@_13_0 Bool )
(declare-var main@_15_0 Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@_18_0 Bool )
(declare-var |tuple(main@_5_0, main@_18_0)| Bool )
(declare-var |tuple(main@_13_0, main@_18_0)| Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%_19_1 Bool )
(declare-var main@%_19_2 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@_5_1 Bool )
(declare-var main@%.0.i52_2 Int )
(declare-var main@.preheader28_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.01.i51_0 Int )
(declare-var main@%.02.i50_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.01.i51_1 Int )
(declare-var main@%.02.i50_1 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@.lr.ph41.preheader_0 Bool )
(declare-var main@.lr.ph41_0 Bool )
(declare-var main@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var main@%.04.i40_0 Int )
(declare-var main@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var main@%.04.i40_1 Int )
(declare-var main@._crit_edge42_0 Bool )
(declare-var main@%shadow.mem.0.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.3_1 (Array Int Int) )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@.lr.ph45.preheader_0 Bool )
(declare-var main@.lr.ph45_0 Bool )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%.06.i43_0 Int )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%.06.i43_1 Int )
(declare-var main@._crit_edge46.thread_0 Bool )
(declare-var main@%_40_0 Int )
(declare-var main@.preheader26_0 Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%_24_0 Bool )
(declare-var main@%.13.i59_0 Int )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%_24_1 Bool )
(declare-var main@%.13.i59_1 Int )
(declare-var main@.preheader25.preheader_0 Bool )
(declare-var main@%_27_0 Bool )
(declare-var main@.lr.ph37.preheader_0 Bool )
(declare-var main@%shadow.mem.0.4_0 (Array Int Int) )
(declare-var main@%_69_0 Bool )
(declare-var main@%.1.i3985_0 Int )
(declare-var main@%shadow.mem.0.4_1 (Array Int Int) )
(declare-var main@%_69_1 Bool )
(declare-var main@%.1.i3985_1 Int )
(declare-var main@.preheader24_0 Bool )
(declare-var |tuple(main@.preheader25.preheader_0, main@.preheader24_0)| Bool )
(declare-var |tuple(main@.preheader26_0, main@.preheader24_0)| Bool )
(declare-var main@%shadow.mem.0.5_0 (Array Int Int) )
(declare-var main@%.1.i.lcssa_0 Int )
(declare-var main@%shadow.mem.0.5_1 (Array Int Int) )
(declare-var main@%.1.i.lcssa_1 Int )
(declare-var main@%shadow.mem.0.5_2 (Array Int Int) )
(declare-var main@%.1.i.lcssa_2 Int )
(declare-var main@.preheader23.us.preheader_0 Bool )
(declare-var main@%_73_0 Bool )
(declare-var main@.lr.ph34.us.preheader_0 Bool )
(declare-var main@%shadow.mem.4.6_0 (Array Int Int) )
(declare-var main@%_76_0 Bool )
(declare-var main@%.2.i35.us84_0 Int )
(declare-var main@%shadow.mem.4.6_1 (Array Int Int) )
(declare-var main@%_76_1 Bool )
(declare-var main@%.2.i35.us84_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)| Bool )
(declare-var |tuple(main@.preheader24_0, main@.preheader_0)| Bool )
(declare-var main@%shadow.mem.4.9_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.9_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.9_2 (Array Int Int) )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph83_0 Bool )
(declare-var main@%_109_0 Int )
(declare-var main@%.05.i3182_0 Int )
(declare-var main@%_109_1 Int )
(declare-var main@%.05.i3182_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.preheader_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_29_0 Int )
(declare-var main@_33_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@_35_0 Bool )
(declare-var |tuple(main@.lr.ph41_0, main@_35_0)| Bool )
(declare-var main@%shadow.mem.0.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_2 (Array Int Int) )
(declare-var main@.lr.ph41_1 Bool )
(declare-var main@%shadow.mem.0.1_2 (Array Int Int) )
(declare-var main@%.04.i40_2 Int )
(declare-var main@%_43_0 Int )
(declare-var main@_47_0 Bool )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@_49_0 Bool )
(declare-var |tuple(main@.lr.ph45_0, main@_49_0)| Bool )
(declare-var main@%shadow.mem.4.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_2 (Array Int Int) )
(declare-var main@.lr.ph45_1 Bool )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@%.06.i43_2 Int )
(declare-var main@._crit_edge46_0 Bool )
(declare-var main@%_52_0 Int )
(declare-var main@.preheader27_0 Bool )
(declare-var main@.lr.ph48.preheader_0 Bool )
(declare-var main@.lr.ph48_0 Bool )
(declare-var main@%shadow.mem.4.4_0 (Array Int Int) )
(declare-var main@%.08.i47_0 Int )
(declare-var main@%shadow.mem.4.4_1 (Array Int Int) )
(declare-var main@%.08.i47_1 Int )
(declare-var |tuple(main@._crit_edge46_0, main@.preheader26_0)| Bool )
(declare-var |tuple(main@.preheader27_0, main@.preheader26_0)| Bool )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@%_24_2 Bool )
(declare-var main@%.13.i59_2 Int )
(declare-var main@%_55_0 Int )
(declare-var main@_59_0 Bool )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@_61_0 Bool )
(declare-var |tuple(main@.lr.ph48_0, main@_61_0)| Bool )
(declare-var main@%shadow.mem.4.5_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.5_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.5_2 (Array Int Int) )
(declare-var main@_64_0 Bool )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Bool )
(declare-var main@%.01.i51_2 Int )
(declare-var main@%.02.i50_2 Int )
(declare-var main@.lr.ph48_1 Bool )
(declare-var main@%shadow.mem.4.4_2 (Array Int Int) )
(declare-var main@%.08.i47_2 Int )
(declare-var main@.lr.ph37_0 Bool )
(declare-var main@%shadow.mem.0.6_0 (Array Int Int) )
(declare-var main@%.09.i36_0 Int )
(declare-var main@%shadow.mem.0.6_1 (Array Int Int) )
(declare-var main@%.09.i36_1 Int )
(declare-var main@%_89_0 Int )
(declare-var main@_93_0 Bool )
(declare-var main@%sm15_0 (Array Int Int) )
(declare-var main@_95_0 Bool )
(declare-var |tuple(main@.lr.ph37_0, main@_95_0)| Bool )
(declare-var main@%shadow.mem.0.7_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.7_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.7_2 (Array Int Int) )
(declare-var main@._crit_edge38_0 Bool )
(declare-var main@%_98_0 Int )
(declare-var main@.preheader25_0 Bool )
(declare-var main@%_68_0 Bool )
(declare-var main@%.1.i3985_2 Int )
(declare-var main@.lr.ph37_1 Bool )
(declare-var main@%shadow.mem.0.6_2 (Array Int Int) )
(declare-var main@%.09.i36_2 Int )
(declare-var |tuple(main@.preheader25_0, main@.preheader24_0)| Bool )
(declare-var |tuple(main@._crit_edge38_0, main@.preheader24_0)| Bool )
(declare-var main@.lr.ph34.us_0 Bool )
(declare-var main@%shadow.mem.4.7_0 (Array Int Int) )
(declare-var main@%.07.i33.us_0 Int )
(declare-var main@%shadow.mem.4.7_1 (Array Int Int) )
(declare-var main@%.07.i33.us_1 Int )
(declare-var main@%_79_0 Int )
(declare-var main@_83_0 Bool )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@_85_0 Bool )
(declare-var |tuple(main@.lr.ph34.us_0, main@_85_0)| Bool )
(declare-var main@%shadow.mem.4.8_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.8_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.8_2 (Array Int Int) )
(declare-var main@._crit_edge.us_0 Bool )
(declare-var main@.preheader23.us_0 Bool )
(declare-var main@%_74_0 Int )
(declare-var main@%_75_0 Bool )
(declare-var main@%.2.i35.us84_2 Int )
(declare-var main@.lr.ph34.us_1 Bool )
(declare-var main@%shadow.mem.4.7_2 (Array Int Int) )
(declare-var main@%.07.i33.us_2 Int )
(declare-var |tuple(main@._crit_edge.us_0, main@.preheader_0)| Bool )
(declare-var |tuple(main@.preheader23.us_0, main@.preheader_0)| Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_121_0 Int )
(declare-var main@.lr.ph83_1 Bool )
(declare-var main@%_109_2 Int )
(declare-var |tuple(main@.lr.ph_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.lr.ph83_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm16_0 main@%sm17_0))
(rule (=> (and (main@entry main@%sm16_0 main@%sm17_0)
         true
         (= main@%sm_0 main@%sm16_0)
         (= main@%sm5_0 main@%sm17_0)
         (= main@%_0_0 (= main@%loop.bound_0 8))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 8))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (= main@%_3_0 (= main@%loop.bound3_0 8))
         main@%_3_0
         (= main@%_4_0 (= main@%loop.bound4_0 9))
         main@%_4_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound3_0
                     main@%loop.bound2_0
                     main@%loop.bound4_0
                     main@%sm5_0
                     main@%sm_0)))
(rule (let ((a!1 (main@empty.loop @a_1_0
                            @a_2_0
                            main@%loop.bound_0
                            main@%loop.bound1_0
                            main@%loop.bound3_0
                            main@%loop.bound2_0
                            main@%loop.bound4_0
                            main@%sm5_0
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
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%loop.bound2_0
                          main@%loop.bound4_0
                          main@%sm5_0
                          main@%sm_0)
         true
         (=> main@_5_0 (and main@_5_0 main@empty.loop_0))
         (=> (and main@_5_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_5_0 main@empty.loop_0) (= main@%.0.i52_0 1))
         (=> (and main@_5_0 main@empty.loop_0)
             (= main@%.0.i52_1 main@%.0.i52_0))
         main@_5_0)
    (main@_5 @a_1_0
             @a_2_0
             main@%loop.bound_0
             main@%loop.bound1_0
             main@%loop.bound3_0
             main@%loop.bound2_0
             main@%.0.i52_1
             main@%loop.bound4_0
             main@%sm5_0
             main@%sm_0)))
(rule (let ((a!1 (and (main@_5 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%loop.bound3_0
                         main@%loop.bound2_0
                         main@%.0.i52_0
                         main@%loop.bound4_0
                         main@%sm5_0
                         main@%sm_0)
                true
                (= main@%_6_0 (+ @a_1_0 (* 0 40) (* main@%.0.i52_0 4)))
                (or (<= @a_1_0 0) (> main@%_6_0 0))
                (> @a_1_0 0)
                (= main@%_8_0 (+ @a_2_0 (* 0 40) (* main@%.0.i52_0 4)))
                (or (<= @a_2_0 0) (> main@%_8_0 0))
                (> @a_2_0 0)
                (= main@%or.cond_0 (or main@%_10_0 main@%_12_0))
                (=> main@_13_0 (and main@_13_0 main@_5_0))
                (=> (and main@_13_0 main@_5_0) main@%or.cond_0)
                (=> main@_15_0 (and main@_15_0 main@_13_0))
                (=> (and main@_15_0 main@_13_0) (not main@%_14_0))
                (=> |tuple(main@_5_0, main@_18_0)| main@_5_0)
                (=> |tuple(main@_13_0, main@_18_0)| main@_13_0)
                (=> main@_18_0
                    (or |tuple(main@_5_0, main@_18_0)|
                        (and main@_18_0 main@_15_0)
                        |tuple(main@_13_0, main@_18_0)|))
                (=> |tuple(main@_5_0, main@_18_0)| (not main@%or.cond_0))
                (=> |tuple(main@_13_0, main@_18_0)| main@%_14_0)
                (=> |tuple(main@_5_0, main@_18_0)| (= main@%_19_0 false))
                (=> (and main@_18_0 main@_15_0) (= main@%_19_1 main@%_17_0))
                (=> |tuple(main@_13_0, main@_18_0)| (= main@%_19_2 true))
                (=> |tuple(main@_5_0, main@_18_0)| (= main@%_19_3 main@%_19_0))
                (=> (and main@_18_0 main@_15_0) (= main@%_19_3 main@%_19_1))
                (=> |tuple(main@_13_0, main@_18_0)| (= main@%_19_3 main@%_19_2))
                (=> main@_18_0 main@%_19_3)
                (=> main@_18_0 (= main@%_20_0 (+ main@%.0.i52_0 1)))
                (=> main@_18_0
                    (= main@%_21_0 (< main@%.0.i52_0 main@%loop.bound4_0)))
                (=> main@_5_1 (and main@_5_1 main@_18_0))
                (=> (and main@_5_1 main@_18_0) main@%_21_0)
                (=> (and main@_5_1 main@_18_0) (= main@%.0.i52_1 main@%_20_0))
                (=> (and main@_5_1 main@_18_0)
                    (= main@%.0.i52_2 main@%.0.i52_1))
                main@_5_1)))
  (=> a!1
      (main@_5 @a_1_0
               @a_2_0
               main@%loop.bound_0
               main@%loop.bound1_0
               main@%loop.bound3_0
               main@%loop.bound2_0
               main@%.0.i52_2
               main@%loop.bound4_0
               main@%sm5_0
               main@%sm_0))))
(rule (let ((a!1 (and (main@_5 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%loop.bound3_0
                         main@%loop.bound2_0
                         main@%.0.i52_0
                         main@%loop.bound4_0
                         main@%sm5_0
                         main@%sm_0)
                true
                (= main@%_6_0 (+ @a_1_0 (* 0 40) (* main@%.0.i52_0 4)))
                (or (<= @a_1_0 0) (> main@%_6_0 0))
                (> @a_1_0 0)
                (= main@%_8_0 (+ @a_2_0 (* 0 40) (* main@%.0.i52_0 4)))
                (or (<= @a_2_0 0) (> main@%_8_0 0))
                (> @a_2_0 0)
                (= main@%or.cond_0 (or main@%_10_0 main@%_12_0))
                (=> main@_13_0 (and main@_13_0 main@_5_0))
                (=> (and main@_13_0 main@_5_0) main@%or.cond_0)
                (=> main@_15_0 (and main@_15_0 main@_13_0))
                (=> (and main@_15_0 main@_13_0) (not main@%_14_0))
                (=> |tuple(main@_5_0, main@_18_0)| main@_5_0)
                (=> |tuple(main@_13_0, main@_18_0)| main@_13_0)
                (=> main@_18_0
                    (or |tuple(main@_5_0, main@_18_0)|
                        (and main@_18_0 main@_15_0)
                        |tuple(main@_13_0, main@_18_0)|))
                (=> |tuple(main@_5_0, main@_18_0)| (not main@%or.cond_0))
                (=> |tuple(main@_13_0, main@_18_0)| main@%_14_0)
                (=> |tuple(main@_5_0, main@_18_0)| (= main@%_19_0 false))
                (=> (and main@_18_0 main@_15_0) (= main@%_19_1 main@%_17_0))
                (=> |tuple(main@_13_0, main@_18_0)| (= main@%_19_2 true))
                (=> |tuple(main@_5_0, main@_18_0)| (= main@%_19_3 main@%_19_0))
                (=> (and main@_18_0 main@_15_0) (= main@%_19_3 main@%_19_1))
                (=> |tuple(main@_13_0, main@_18_0)| (= main@%_19_3 main@%_19_2))
                (=> main@_18_0 main@%_19_3)
                (=> main@_18_0 (= main@%_20_0 (+ main@%.0.i52_0 1)))
                (=> main@_18_0
                    (= main@%_21_0 (< main@%.0.i52_0 main@%loop.bound4_0)))
                (=> main@.preheader28_0 (and main@.preheader28_0 main@_18_0))
                (=> (and main@.preheader28_0 main@_18_0) (not main@%_21_0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%shadow.mem.4.0_0 main@%sm5_0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@.preheader28_0 main@_18_0) (= main@%.01.i51_0 0))
                (=> (and main@.preheader28_0 main@_18_0) (= main@%.02.i50_0 0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%.01.i51_1 main@%.01.i51_0))
                (=> (and main@.preheader28_0 main@_18_0)
                    (= main@%.02.i50_1 main@%.02.i50_0))
                main@.preheader28_0)))
  (=> a!1
      (main@.preheader28
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%loop.bound1_0
        main@%.01.i51_1
        main@%.02.i50_1
        main@%shadow.mem.4.0_1
        main@%shadow.mem.0.0_1
        main@%loop.bound3_0
        main@%loop.bound2_0))))
(rule (let ((a!1 (=> main@.lr.ph41.preheader_0
               (= main@%_23_0 (+ @a_1_0 (* 0 40) (* 9 4))))))
(let ((a!2 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@.lr.ph41.preheader_0
                    (and main@.lr.ph41.preheader_0 main@.preheader28_0))
                (=> (and main@.lr.ph41.preheader_0 main@.preheader28_0)
                    main@%_22_0)
                a!1
                (=> main@.lr.ph41.preheader_0
                    (or (<= @a_1_0 0) (> main@%_23_0 0)))
                (=> main@.lr.ph41.preheader_0 (> @a_1_0 0))
                (=> main@.lr.ph41_0
                    (and main@.lr.ph41_0 main@.lr.ph41.preheader_0))
                (=> (and main@.lr.ph41_0 main@.lr.ph41.preheader_0)
                    (= main@%shadow.mem.0.1_0 main@%shadow.mem.0.0_0))
                (=> (and main@.lr.ph41_0 main@.lr.ph41.preheader_0)
                    (= main@%.04.i40_0 9))
                (=> (and main@.lr.ph41_0 main@.lr.ph41.preheader_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.lr.ph41_0 main@.lr.ph41.preheader_0)
                    (= main@%.04.i40_1 main@%.04.i40_0))
                main@.lr.ph41_0)))
  (=> a!2
      (main@.lr.ph41 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%shadow.mem.4.0_0
                     main@%loop.bound3_0
                     main@%loop.bound2_0
                     main@%shadow.mem.0.1_1
                     main@%.04.i40_1)))))
(rule (let ((a!1 (=> main@.lr.ph45.preheader_0
               (= main@%_41_0 (+ @a_2_0 (* 0 40) (* 9 4))))))
(let ((a!2 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@._crit_edge42_0
                    (and main@._crit_edge42_0 main@.preheader28_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (not main@%_22_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@.lr.ph45.preheader_0
                    (and main@.lr.ph45.preheader_0 main@._crit_edge42_0))
                (=> (and main@.lr.ph45.preheader_0 main@._crit_edge42_0)
                    main@%_39_0)
                a!1
                (=> main@.lr.ph45.preheader_0
                    (or (<= @a_2_0 0) (> main@%_41_0 0)))
                (=> main@.lr.ph45.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph45_0
                    (and main@.lr.ph45_0 main@.lr.ph45.preheader_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%.06.i43_0 9))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%.06.i43_1 main@%.06.i43_0))
                main@.lr.ph45_0)))
  (=> a!2
      (main@.lr.ph45 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%shadow.mem.0.3_1
                     main@%_38_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%loop.bound3_0
                     main@%_39_0
                     main@%shadow.mem.4.2_1
                     main@%.06.i43_1
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@._crit_edge42_0
                    (and main@._crit_edge42_0 main@.preheader28_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (not main@%_22_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> main@.lr.ph37.preheader_0
                    (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    main@%_27_0)
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.3_1))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_0 main@%_27_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_0 main@%_38_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_1 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_1 main@%_69_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_1 main@%.1.i3985_0))
                main@.lr.ph37.preheader_0)))
  (=> a!1
      (main@.lr.ph37.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%.13.i59_1
        main@%shadow.mem.4.1_1
        main@%_24_1
        main@%.1.i3985_1
        main@%loop.bound1_0
        main@%shadow.mem.0.4_1
        main@%_69_1))))
(rule (let ((a!1 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@._crit_edge42_0
                    (and main@._crit_edge42_0 main@.preheader28_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (not main@%_22_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    main@%_73_0)
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.1_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_0 main@%_73_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_0 main@%.13.i59_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_1 main@%_76_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_1 main@%.2.i35.us84_0))
                main@.lr.ph34.us.preheader_0)))
  (=> a!1
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_2
        @a_2_0
        main@%.2.i35.us84_1
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_1))))
(rule (let ((a!1 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!2 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!3 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@._crit_edge42_0
                    (and main@._crit_edge42_0 main@.preheader28_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (not main@%_22_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!1
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!2
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!3
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_2
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!2 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!3 (and (main@.preheader28
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%loop.bound1_0
                  main@%.01.i51_0
                  main@%.02.i50_0
                  main@%shadow.mem.4.0_0
                  main@%shadow.mem.0.0_0
                  main@%loop.bound3_0
                  main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.01.i51_0 9))
                (=> main@._crit_edge42_0
                    (and main@._crit_edge42_0 main@.preheader28_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (not main@%_22_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@._crit_edge42_0 main@.preheader28_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!1
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!2
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!3 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4)))))
(let ((a!3 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@.lr.ph41_1 (and main@.lr.ph41_1 main@_35_0))
                (=> (and main@.lr.ph41_1 main@_35_0) main@%_37_0)
                (=> (and main@.lr.ph41_1 main@_35_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.2_2))
                (=> (and main@.lr.ph41_1 main@_35_0)
                    (= main@%.04.i40_1 main@%_29_0))
                (=> (and main@.lr.ph41_1 main@_35_0)
                    (= main@%shadow.mem.0.1_2 main@%shadow.mem.0.1_1))
                (=> (and main@.lr.ph41_1 main@_35_0)
                    (= main@%.04.i40_2 main@%.04.i40_1))
                main@.lr.ph41_1)))
  (=> a!3
      (main@.lr.ph41 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%shadow.mem.4.0_0
                     main@%loop.bound3_0
                     main@%loop.bound2_0
                     main@%shadow.mem.0.1_2
                     main@%.04.i40_2)))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4))))
      (a!3 (=> main@.lr.ph45.preheader_0
               (= main@%_41_0 (+ @a_2_0 (* 0 40) (* 9 4))))))
(let ((a!4 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_35_0))
                (=> (and main@._crit_edge42_0 main@_35_0) (not main@%_37_0))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.2_2))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@.lr.ph45.preheader_0
                    (and main@.lr.ph45.preheader_0 main@._crit_edge42_0))
                (=> (and main@.lr.ph45.preheader_0 main@._crit_edge42_0)
                    main@%_39_0)
                a!3
                (=> main@.lr.ph45.preheader_0
                    (or (<= @a_2_0 0) (> main@%_41_0 0)))
                (=> main@.lr.ph45.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph45_0
                    (and main@.lr.ph45_0 main@.lr.ph45.preheader_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%.06.i43_0 9))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@.lr.ph45_0 main@.lr.ph45.preheader_0)
                    (= main@%.06.i43_1 main@%.06.i43_0))
                main@.lr.ph45_0)))
  (=> a!4
      (main@.lr.ph45 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%shadow.mem.0.3_1
                     main@%_38_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%loop.bound3_0
                     main@%_39_0
                     main@%shadow.mem.4.2_1
                     main@%.06.i43_1
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4)))))
(let ((a!3 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_35_0))
                (=> (and main@._crit_edge42_0 main@_35_0) (not main@%_37_0))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.2_2))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> main@.lr.ph37.preheader_0
                    (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    main@%_27_0)
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.3_1))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_0 main@%_27_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_0 main@%_38_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_1 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_1 main@%_69_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_1 main@%.1.i3985_0))
                main@.lr.ph37.preheader_0)))
  (=> a!3
      (main@.lr.ph37.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%.13.i59_1
        main@%shadow.mem.4.1_1
        main@%_24_1
        main@%.1.i3985_1
        main@%loop.bound1_0
        main@%shadow.mem.0.4_1
        main@%_69_1)))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4)))))
(let ((a!3 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_35_0))
                (=> (and main@._crit_edge42_0 main@_35_0) (not main@%_37_0))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.2_2))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    main@%_73_0)
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.1_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_0 main@%_73_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_0 main@%.13.i59_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_1 main@%_76_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_1 main@%.2.i35.us84_0))
                main@.lr.ph34.us.preheader_0)))
  (=> a!3
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_2
        @a_2_0
        main@%.2.i35.us84_1
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_1)))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4))))
      (a!3 (= main@%_99_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!4 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!5 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_35_0))
                (=> (and main@._crit_edge42_0 main@_35_0) (not main@%_37_0))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.2_2))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!4
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!5
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_2
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_29_0 4))))
      (a!2 (= main@%_34_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4))))
      (a!3 (= main@%_99_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!4 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!5 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%shadow.mem.4.0_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0)
                true
                (= main@%_29_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_30_0 0))
                (> @a_1_0 0)
                (=> main@_33_0 (and main@_33_0 main@.lr.ph41_0))
                (=> (and main@_33_0 main@.lr.ph41_0) main@%_32_0)
                (=> main@_33_0 a!2)
                (=> main@_33_0 (or (<= @a_1_0 0) (> main@%_34_0 0)))
                (=> main@_33_0 (> @a_1_0 0))
                (=> main@_33_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| main@.lr.ph41_0)
                (=> main@_35_0
                    (or (and main@_35_0 main@_33_0)
                        |tuple(main@.lr.ph41_0, main@_35_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)| (not main@%_32_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_35_0 main@_33_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_35_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_35_0 (= main@%_37_0 (> main@%_29_0 main@%.01.i51_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_35_0))
                (=> (and main@._crit_edge42_0 main@_35_0) (not main@%_37_0))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.2_2))
                (=> (and main@._crit_edge42_0 main@_35_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> main@._crit_edge42_0 (= main@%_38_0 (+ main@%.01.i51_0 1)))
                (=> main@._crit_edge42_0
                    (= main@%_39_0 (< main@%.02.i50_0 main@%loop.bound2_0)))
                (=> main@._crit_edge46.thread_0
                    (and main@._crit_edge46.thread_0 main@._crit_edge42_0))
                (=> (and main@._crit_edge46.thread_0 main@._crit_edge42_0)
                    (not main@%_39_0))
                (=> main@._crit_edge46.thread_0
                    (= main@%_40_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge46.thread_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_0 false))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_0 main@%_40_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@._crit_edge46.thread_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!4
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4)))))
(let ((a!3 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@.lr.ph45_1 (and main@.lr.ph45_1 main@_49_0))
                (=> (and main@.lr.ph45_1 main@_49_0) main@%_51_0)
                (=> (and main@.lr.ph45_1 main@_49_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.3_2))
                (=> (and main@.lr.ph45_1 main@_49_0)
                    (= main@%.06.i43_1 main@%_43_0))
                (=> (and main@.lr.ph45_1 main@_49_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> (and main@.lr.ph45_1 main@_49_0)
                    (= main@%.06.i43_2 main@%.06.i43_1))
                main@.lr.ph45_1)))
  (=> a!3
      (main@.lr.ph45 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%shadow.mem.0.3_0
                     main@%_38_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%loop.bound3_0
                     main@%_39_0
                     main@%shadow.mem.4.2_2
                     main@%.06.i43_2
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4))))
      (a!3 (= main@%_53_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4)))))
(let ((a!4 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@._crit_edge46_0 (and main@._crit_edge46_0 main@_49_0))
                (=> (and main@._crit_edge46_0 main@_49_0) (not main@%_51_0))
                (=> main@._crit_edge46_0 (= main@%_52_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader27_0
                    (and main@.preheader27_0 main@._crit_edge46_0))
                (=> (and main@.preheader27_0 main@._crit_edge46_0) main@%_39_0)
                (=> main@.preheader27_0
                    (= main@%.not_0 (= main@%.02.i50_0 main@%loop.bound3_0)))
                (=> main@.lr.ph48.preheader_0
                    (and main@.lr.ph48.preheader_0 main@.preheader27_0))
                (=> (and main@.lr.ph48.preheader_0 main@.preheader27_0)
                    (not main@%.not_0))
                (=> main@.lr.ph48.preheader_0 a!3)
                (=> main@.lr.ph48.preheader_0
                    (or (<= @a_2_0 0) (> main@%_53_0 0)))
                (=> main@.lr.ph48.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph48_0
                    (and main@.lr.ph48_0 main@.lr.ph48.preheader_0))
                (=> (and main@.lr.ph48_0 main@.lr.ph48.preheader_0)
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.3_2))
                (=> (and main@.lr.ph48_0 main@.lr.ph48.preheader_0)
                    (= main@%.08.i47_0 9))
                (=> (and main@.lr.ph48_0 main@.lr.ph48.preheader_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.4_0))
                (=> (and main@.lr.ph48_0 main@.lr.ph48.preheader_0)
                    (= main@%.08.i47_1 main@%.08.i47_0))
                main@.lr.ph48_0)))
  (=> a!4
      (main@.lr.ph48 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%shadow.mem.0.3_0
                     main@%_38_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%_52_0
                     main@%shadow.mem.4.4_1
                     main@%.08.i47_1
                     main@%loop.bound3_0
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4)))))
(let ((a!3 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@._crit_edge46_0 (and main@._crit_edge46_0 main@_49_0))
                (=> (and main@._crit_edge46_0 main@_49_0) (not main@%_51_0))
                (=> main@._crit_edge46_0 (= main@%_52_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader27_0
                    (and main@.preheader27_0 main@._crit_edge46_0))
                (=> (and main@.preheader27_0 main@._crit_edge46_0) main@%_39_0)
                (=> main@.preheader27_0
                    (= main@%.not_0 (= main@%.02.i50_0 main@%loop.bound3_0)))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    main@._crit_edge46_0)
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@.preheader27_0)
                (=> main@.preheader26_0
                    (or |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                        |tuple(main@.preheader27_0, main@.preheader26_0)|))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (not main@%_39_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@%.not_0)
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_0 false))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_0 main@%_52_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.3_2))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_1 false))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_1 10))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_1))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_2 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> main@.lr.ph37.preheader_0
                    (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    main@%_27_0)
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.3_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_0 main@%_27_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_0 main@%_38_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_1 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_1 main@%_69_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_1 main@%.1.i3985_0))
                main@.lr.ph37.preheader_0)))
  (=> a!3
      (main@.lr.ph37.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%.13.i59_2
        main@%shadow.mem.4.1_2
        main@%_24_2
        main@%.1.i3985_1
        main@%loop.bound1_0
        main@%shadow.mem.0.4_1
        main@%_69_1)))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4)))))
(let ((a!3 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@._crit_edge46_0 (and main@._crit_edge46_0 main@_49_0))
                (=> (and main@._crit_edge46_0 main@_49_0) (not main@%_51_0))
                (=> main@._crit_edge46_0 (= main@%_52_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader27_0
                    (and main@.preheader27_0 main@._crit_edge46_0))
                (=> (and main@.preheader27_0 main@._crit_edge46_0) main@%_39_0)
                (=> main@.preheader27_0
                    (= main@%.not_0 (= main@%.02.i50_0 main@%loop.bound3_0)))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    main@._crit_edge46_0)
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@.preheader27_0)
                (=> main@.preheader26_0
                    (or |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                        |tuple(main@.preheader27_0, main@.preheader26_0)|))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (not main@%_39_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@%.not_0)
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_0 false))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_0 main@%_52_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.3_2))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_1 false))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_1 10))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_1))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_2 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_2 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_2 9)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    main@%_73_0)
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.1_2))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_0 main@%_73_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_0 main@%.13.i59_2))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_1 main@%_76_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_1 main@%.2.i35.us84_0))
                main@.lr.ph34.us.preheader_0)))
  (=> a!3
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_2
        @a_2_0
        main@%.2.i35.us84_1
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_1)))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@._crit_edge46_0 (and main@._crit_edge46_0 main@_49_0))
                (=> (and main@._crit_edge46_0 main@_49_0) (not main@%_51_0))
                (=> main@._crit_edge46_0 (= main@%_52_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader27_0
                    (and main@.preheader27_0 main@._crit_edge46_0))
                (=> (and main@.preheader27_0 main@._crit_edge46_0) main@%_39_0)
                (=> main@.preheader27_0
                    (= main@%.not_0 (= main@%.02.i50_0 main@%loop.bound3_0)))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    main@._crit_edge46_0)
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@.preheader27_0)
                (=> main@.preheader26_0
                    (or |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                        |tuple(main@.preheader27_0, main@.preheader26_0)|))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (not main@%_39_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@%.not_0)
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_0 false))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_0 main@%_52_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.3_2))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_1 false))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_1 10))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_1))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_2 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_2 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_2 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_2))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_2))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!5
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_2
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (= main@%_44_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_43_0 4))))
      (a!2 (= main@%_48_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.06.i43_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph45 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%loop.bound3_0
                               main@%_39_0
                               main@%shadow.mem.4.2_0
                               main@%.06.i43_0
                               main@%loop.bound2_0)
                true
                (= main@%_43_0 (+ main@%.06.i43_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_44_0 0))
                (> @a_2_0 0)
                (=> main@_47_0 (and main@_47_0 main@.lr.ph45_0))
                (=> (and main@_47_0 main@.lr.ph45_0) main@%_46_0)
                (=> main@_47_0 a!2)
                (=> main@_47_0 (or (<= @a_2_0 0) (> main@%_48_0 0)))
                (=> main@_47_0 (> @a_2_0 0))
                (=> main@_47_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| main@.lr.ph45_0)
                (=> main@_49_0
                    (or (and main@_49_0 main@_47_0)
                        |tuple(main@.lr.ph45_0, main@_49_0)|))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)| (not main@%_46_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_49_0 main@_47_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph45_0, main@_49_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_49_0 (= main@%_51_0 (> main@%_43_0 main@%.02.i50_0)))
                (=> main@._crit_edge46_0 (and main@._crit_edge46_0 main@_49_0))
                (=> (and main@._crit_edge46_0 main@_49_0) (not main@%_51_0))
                (=> main@._crit_edge46_0 (= main@%_52_0 (+ main@%.02.i50_0 1)))
                (=> main@.preheader27_0
                    (and main@.preheader27_0 main@._crit_edge46_0))
                (=> (and main@.preheader27_0 main@._crit_edge46_0) main@%_39_0)
                (=> main@.preheader27_0
                    (= main@%.not_0 (= main@%.02.i50_0 main@%loop.bound3_0)))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    main@._crit_edge46_0)
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@.preheader27_0)
                (=> main@.preheader26_0
                    (or |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                        |tuple(main@.preheader27_0, main@.preheader26_0)|))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (not main@%_39_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    main@%.not_0)
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_0 false))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_0 main@%_52_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.3_2))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_1 false))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_1 10))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_0))
                (=> |tuple(main@._crit_edge46_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_0))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%_24_2 main@%_24_1))
                (=> |tuple(main@.preheader27_0, main@.preheader26_0)|
                    (= main@%.13.i59_2 main@%.13.i59_1))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_2 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_2 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_2 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_2))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_2))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4)))))
(let ((a!3 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@_64_0 (and main@_64_0 main@_61_0))
                (=> (and main@_64_0 main@_61_0) (not main@%_63_0))
                (=> main@_64_0 (= main@%_65_0 (+ main@%.02.i50_0 2)))
                (=> main@_64_0 (= main@%_66_0 (< main@%.02.i50_0 8)))
                (=> main@_64_0
                    (= main@%_67_0 (ite main@%_22_0 main@%_66_0 false)))
                (=> main@.preheader28_0 (and main@.preheader28_0 main@_64_0))
                (=> (and main@.preheader28_0 main@_64_0) main@%_67_0)
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%shadow.mem.4.0_0 main@%shadow.mem.4.5_2))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.3_0))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%.01.i51_1 main@%_38_0))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%.02.i50_1 main@%_65_0))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%.01.i51_2 main@%.01.i51_1))
                (=> (and main@.preheader28_0 main@_64_0)
                    (= main@%.02.i50_2 main@%.02.i50_1))
                main@.preheader28_0)))
  (=> a!3
      (main@.preheader28
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%loop.bound1_0
        main@%.01.i51_2
        main@%.02.i50_2
        main@%shadow.mem.4.0_1
        main@%shadow.mem.0.0_1
        main@%loop.bound3_0
        main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4)))))
(let ((a!3 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@.lr.ph48_1 (and main@.lr.ph48_1 main@_61_0))
                (=> (and main@.lr.ph48_1 main@_61_0) main@%_63_0)
                (=> (and main@.lr.ph48_1 main@_61_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.5_2))
                (=> (and main@.lr.ph48_1 main@_61_0)
                    (= main@%.08.i47_1 main@%_55_0))
                (=> (and main@.lr.ph48_1 main@_61_0)
                    (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.4_1))
                (=> (and main@.lr.ph48_1 main@_61_0)
                    (= main@%.08.i47_2 main@%.08.i47_1))
                main@.lr.ph48_1)))
  (=> a!3
      (main@.lr.ph48 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.01.i51_0
                     main@%shadow.mem.0.3_0
                     main@%_38_0
                     main@%_22_0
                     main@%.02.i50_0
                     main@%_52_0
                     main@%shadow.mem.4.4_2
                     main@%.08.i47_2
                     main@%loop.bound3_0
                     main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4)))))
(let ((a!3 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@_64_0 (and main@_64_0 main@_61_0))
                (=> (and main@_64_0 main@_61_0) (not main@%_63_0))
                (=> main@_64_0 (= main@%_65_0 (+ main@%.02.i50_0 2)))
                (=> main@_64_0 (= main@%_66_0 (< main@%.02.i50_0 8)))
                (=> main@_64_0
                    (= main@%_67_0 (ite main@%_22_0 main@%_66_0 false)))
                (=> main@.preheader26_0 (and main@.preheader26_0 main@_64_0))
                (=> (and main@.preheader26_0 main@_64_0) (not main@%_67_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.5_2))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_0 main@%_66_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_0 main@%_65_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> main@.lr.ph37.preheader_0
                    (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    main@%_27_0)
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.3_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_0 main@%_27_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_0 main@%_38_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%shadow.mem.0.4_1 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%_69_1 main@%_69_0))
                (=> (and main@.lr.ph37.preheader_0
                         main@.preheader25.preheader_0)
                    (= main@%.1.i3985_1 main@%.1.i3985_0))
                main@.lr.ph37.preheader_0)))
  (=> a!3
      (main@.lr.ph37.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%.13.i59_1
        main@%shadow.mem.4.1_1
        main@%_24_1
        main@%.1.i3985_1
        main@%loop.bound1_0
        main@%shadow.mem.0.4_1
        main@%_69_1)))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4)))))
(let ((a!3 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@_64_0 (and main@_64_0 main@_61_0))
                (=> (and main@_64_0 main@_61_0) (not main@%_63_0))
                (=> main@_64_0 (= main@%_65_0 (+ main@%.02.i50_0 2)))
                (=> main@_64_0 (= main@%_66_0 (< main@%.02.i50_0 8)))
                (=> main@_64_0
                    (= main@%_67_0 (ite main@%_22_0 main@%_66_0 false)))
                (=> main@.preheader26_0 (and main@.preheader26_0 main@_64_0))
                (=> (and main@.preheader26_0 main@_64_0) (not main@%_67_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.5_2))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_0 main@%_66_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_0 main@%_65_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    main@%_73_0)
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.1_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_0 main@%_73_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_0 main@%.13.i59_1))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_1 main@%_76_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_1 main@%.2.i35.us84_0))
                main@.lr.ph34.us.preheader_0)))
  (=> a!3
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_2
        @a_2_0
        main@%.2.i35.us84_1
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_1)))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@_64_0 (and main@_64_0 main@_61_0))
                (=> (and main@_64_0 main@_61_0) (not main@%_63_0))
                (=> main@_64_0 (= main@%_65_0 (+ main@%.02.i50_0 2)))
                (=> main@_64_0 (= main@%_66_0 (< main@%.02.i50_0 8)))
                (=> main@_64_0
                    (= main@%_67_0 (ite main@%_22_0 main@%_66_0 false)))
                (=> main@.preheader26_0 (and main@.preheader26_0 main@_64_0))
                (=> (and main@.preheader26_0 main@_64_0) (not main@%_67_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.5_2))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_0 main@%_66_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_0 main@%_65_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!5
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_2
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (= main@%_56_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_55_0 4))))
      (a!2 (= main@%_60_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.08.i47_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph48 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.01.i51_0
                               main@%shadow.mem.0.3_0
                               main@%_38_0
                               main@%_22_0
                               main@%.02.i50_0
                               main@%_52_0
                               main@%shadow.mem.4.4_0
                               main@%.08.i47_0
                               main@%loop.bound3_0
                               main@%loop.bound2_0)
                true
                (= main@%_55_0 (+ main@%.08.i47_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_56_0 0))
                (> @a_2_0 0)
                (=> main@_59_0 (and main@_59_0 main@.lr.ph48_0))
                (=> (and main@_59_0 main@.lr.ph48_0) main@%_58_0)
                (=> main@_59_0 a!2)
                (=> main@_59_0 (or (<= @a_2_0 0) (> main@%_60_0 0)))
                (=> main@_59_0 (> @a_2_0 0))
                (=> main@_59_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| main@.lr.ph48_0)
                (=> main@_61_0
                    (or (and main@_61_0 main@_59_0)
                        |tuple(main@.lr.ph48_0, main@_61_0)|))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)| (not main@%_58_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_0 main@%sm11_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.4_0))
                (=> (and main@_61_0 main@_59_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_0))
                (=> |tuple(main@.lr.ph48_0, main@_61_0)|
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> main@_61_0 (= main@%_63_0 (> main@%_55_0 main@%_52_0)))
                (=> main@_64_0 (and main@_64_0 main@_61_0))
                (=> (and main@_64_0 main@_61_0) (not main@%_63_0))
                (=> main@_64_0 (= main@%_65_0 (+ main@%.02.i50_0 2)))
                (=> main@_64_0 (= main@%_66_0 (< main@%.02.i50_0 8)))
                (=> main@_64_0
                    (= main@%_67_0 (ite main@%_22_0 main@%_66_0 false)))
                (=> main@.preheader26_0 (and main@.preheader26_0 main@_64_0))
                (=> (and main@.preheader26_0 main@_64_0) (not main@%_67_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.5_2))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_0 main@%_66_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_0 main@%_65_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%_24_1 main@%_24_0))
                (=> (and main@.preheader26_0 main@_64_0)
                    (= main@%.13.i59_1 main@%.13.i59_0))
                (=> main@.preheader26_0 (= main@%_25_0 (> main@%.13.i59_1 9)))
                (=> main@.preheader26_0
                    (= main@%_26_0 (ite main@%_22_0 main@%_25_0 false)))
                (=> main@.preheader25.preheader_0
                    (and main@.preheader25.preheader_0 main@.preheader26_0))
                (=> (and main@.preheader25.preheader_0 main@.preheader26_0)
                    main@%_26_0)
                (=> main@.preheader25.preheader_0
                    (= main@%_27_0 (< main@%.01.i51_0 8)))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    main@.preheader25.preheader_0)
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    main@.preheader26_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                        |tuple(main@.preheader26_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (not main@%_27_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (not main@%_26_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.3_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_38_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25.preheader_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@.preheader26_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_1 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_1 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph37.preheader
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%.13.i59_0
                  main@%shadow.mem.4.1_0
                  main@%_24_0
                  main@%.1.i3985_0
                  main@%loop.bound1_0
                  main@%shadow.mem.0.4_0
                  main@%_69_0)
                true
                (= main@%_70_0 (+ @a_1_0 (* 0 40) (* 9 4)))
                (or (<= @a_1_0 0) (> main@%_70_0 0))
                (> @a_1_0 0)
                (=> main@.lr.ph37_0
                    (and main@.lr.ph37_0 main@.lr.ph37.preheader_0))
                (=> (and main@.lr.ph37_0 main@.lr.ph37.preheader_0)
                    (= main@%shadow.mem.0.6_0 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37_0 main@.lr.ph37.preheader_0)
                    (= main@%.09.i36_0 9))
                (=> (and main@.lr.ph37_0 main@.lr.ph37.preheader_0)
                    (= main@%shadow.mem.0.6_1 main@%shadow.mem.0.6_0))
                (=> (and main@.lr.ph37_0 main@.lr.ph37.preheader_0)
                    (= main@%.09.i36_1 main@%.09.i36_0))
                main@.lr.ph37_0)))
  (=> a!1
      (main@.lr.ph37 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%.13.i59_0
                     main@%shadow.mem.4.1_0
                     main@%_24_0
                     main@%.1.i3985_0
                     main@%loop.bound1_0
                     main@%_69_0
                     main@%shadow.mem.0.6_1
                     main@%.09.i36_1))))
(rule (let ((a!1 (= main@%_90_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_89_0 4))))
      (a!2 (= main@%_94_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.09.i36_0 4)))))
(let ((a!3 (and (main@.lr.ph37 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%.13.i59_0
                               main@%shadow.mem.4.1_0
                               main@%_24_0
                               main@%.1.i3985_0
                               main@%loop.bound1_0
                               main@%_69_0
                               main@%shadow.mem.0.6_0
                               main@%.09.i36_0)
                true
                (= main@%_89_0 (+ main@%.09.i36_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_90_0 0))
                (> @a_1_0 0)
                (=> main@_93_0 (and main@_93_0 main@.lr.ph37_0))
                (=> (and main@_93_0 main@.lr.ph37_0) main@%_92_0)
                (=> main@_93_0 a!2)
                (=> main@_93_0 (or (<= @a_1_0 0) (> main@%_94_0 0)))
                (=> main@_93_0 (> @a_1_0 0))
                (=> main@_93_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| main@.lr.ph37_0)
                (=> main@_95_0
                    (or (and main@_95_0 main@_93_0)
                        |tuple(main@.lr.ph37_0, main@_95_0)|))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| (not main@%_92_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_0 main@%sm15_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_1 main@%shadow.mem.0.6_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_1))
                (=> main@_95_0 (= main@%_97_0 (> main@%_89_0 main@%.1.i3985_0)))
                (=> main@._crit_edge38_0 (and main@._crit_edge38_0 main@_95_0))
                (=> (and main@._crit_edge38_0 main@_95_0) (not main@%_97_0))
                (=> main@._crit_edge38_0 (= main@%_98_0 (+ main@%.1.i3985_0 1)))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@._crit_edge38_0))
                (=> (and main@.preheader25_0 main@._crit_edge38_0) main@%_69_0)
                (=> main@.preheader25_0
                    (= main@%_68_0 (< main@%.1.i3985_0 main@%loop.bound1_0)))
                (=> main@.lr.ph37.preheader_0
                    (and main@.lr.ph37.preheader_0 main@.preheader25_0))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    main@%_68_0)
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.7_2))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%_69_1 main@%_68_0))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%.1.i3985_1 main@%_98_0))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%shadow.mem.0.4_1 main@%shadow.mem.0.4_0))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%_69_2 main@%_69_1))
                (=> (and main@.lr.ph37.preheader_0 main@.preheader25_0)
                    (= main@%.1.i3985_2 main@%.1.i3985_1))
                main@.lr.ph37.preheader_0)))
  (=> a!3
      (main@.lr.ph37.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%.13.i59_0
        main@%shadow.mem.4.1_0
        main@%_24_0
        main@%.1.i3985_2
        main@%loop.bound1_0
        main@%shadow.mem.0.4_1
        main@%_69_2)))))
(rule (let ((a!1 (= main@%_90_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_89_0 4))))
      (a!2 (= main@%_94_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.09.i36_0 4)))))
(let ((a!3 (and (main@.lr.ph37 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%.13.i59_0
                               main@%shadow.mem.4.1_0
                               main@%_24_0
                               main@%.1.i3985_0
                               main@%loop.bound1_0
                               main@%_69_0
                               main@%shadow.mem.0.6_0
                               main@%.09.i36_0)
                true
                (= main@%_89_0 (+ main@%.09.i36_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_90_0 0))
                (> @a_1_0 0)
                (=> main@_93_0 (and main@_93_0 main@.lr.ph37_0))
                (=> (and main@_93_0 main@.lr.ph37_0) main@%_92_0)
                (=> main@_93_0 a!2)
                (=> main@_93_0 (or (<= @a_1_0 0) (> main@%_94_0 0)))
                (=> main@_93_0 (> @a_1_0 0))
                (=> main@_93_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| main@.lr.ph37_0)
                (=> main@_95_0
                    (or (and main@_95_0 main@_93_0)
                        |tuple(main@.lr.ph37_0, main@_95_0)|))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| (not main@%_92_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_0 main@%sm15_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_1 main@%shadow.mem.0.6_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_1))
                (=> main@_95_0 (= main@%_97_0 (> main@%_89_0 main@%.1.i3985_0)))
                (=> main@.lr.ph37_1 (and main@.lr.ph37_1 main@_95_0))
                (=> (and main@.lr.ph37_1 main@_95_0) main@%_97_0)
                (=> (and main@.lr.ph37_1 main@_95_0)
                    (= main@%shadow.mem.0.6_1 main@%shadow.mem.0.7_2))
                (=> (and main@.lr.ph37_1 main@_95_0)
                    (= main@%.09.i36_1 main@%_89_0))
                (=> (and main@.lr.ph37_1 main@_95_0)
                    (= main@%shadow.mem.0.6_2 main@%shadow.mem.0.6_1))
                (=> (and main@.lr.ph37_1 main@_95_0)
                    (= main@%.09.i36_2 main@%.09.i36_1))
                main@.lr.ph37_1)))
  (=> a!3
      (main@.lr.ph37 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%.13.i59_0
                     main@%shadow.mem.4.1_0
                     main@%_24_0
                     main@%.1.i3985_0
                     main@%loop.bound1_0
                     main@%_69_0
                     main@%shadow.mem.0.6_2
                     main@%.09.i36_2)))))
(rule (let ((a!1 (= main@%_90_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_89_0 4))))
      (a!2 (= main@%_94_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.09.i36_0 4)))))
(let ((a!3 (and (main@.lr.ph37 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%.13.i59_0
                               main@%shadow.mem.4.1_0
                               main@%_24_0
                               main@%.1.i3985_0
                               main@%loop.bound1_0
                               main@%_69_0
                               main@%shadow.mem.0.6_0
                               main@%.09.i36_0)
                true
                (= main@%_89_0 (+ main@%.09.i36_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_90_0 0))
                (> @a_1_0 0)
                (=> main@_93_0 (and main@_93_0 main@.lr.ph37_0))
                (=> (and main@_93_0 main@.lr.ph37_0) main@%_92_0)
                (=> main@_93_0 a!2)
                (=> main@_93_0 (or (<= @a_1_0 0) (> main@%_94_0 0)))
                (=> main@_93_0 (> @a_1_0 0))
                (=> main@_93_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| main@.lr.ph37_0)
                (=> main@_95_0
                    (or (and main@_95_0 main@_93_0)
                        |tuple(main@.lr.ph37_0, main@_95_0)|))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| (not main@%_92_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_0 main@%sm15_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_1 main@%shadow.mem.0.6_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_1))
                (=> main@_95_0 (= main@%_97_0 (> main@%_89_0 main@%.1.i3985_0)))
                (=> main@._crit_edge38_0 (and main@._crit_edge38_0 main@_95_0))
                (=> (and main@._crit_edge38_0 main@_95_0) (not main@%_97_0))
                (=> main@._crit_edge38_0 (= main@%_98_0 (+ main@%.1.i3985_0 1)))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@._crit_edge38_0))
                (=> (and main@.preheader25_0 main@._crit_edge38_0) main@%_69_0)
                (=> main@.preheader25_0
                    (= main@%_68_0 (< main@%.1.i3985_0 main@%loop.bound1_0)))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    main@.preheader25_0)
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    main@._crit_edge38_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25_0, main@.preheader24_0)|
                        |tuple(main@._crit_edge38_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (not main@%_68_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (not main@%_69_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.7_2))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.7_2))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_98_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_0 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_0 9)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    main@%_73_0)
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.1_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_0 main@%_73_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_0 main@%.13.i59_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%_76_1 main@%_76_0))
                (=> (and main@.lr.ph34.us.preheader_0
                         main@.preheader23.us.preheader_0)
                    (= main@%.2.i35.us84_1 main@%.2.i35.us84_0))
                main@.lr.ph34.us.preheader_0)))
  (=> a!3
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_2
        @a_2_0
        main@%.2.i35.us84_1
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_1)))))
(rule (let ((a!1 (= main@%_90_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_89_0 4))))
      (a!2 (= main@%_94_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.09.i36_0 4))))
      (a!3 (= main@%_99_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!4 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!5 (and (main@.lr.ph37 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%.13.i59_0
                               main@%shadow.mem.4.1_0
                               main@%_24_0
                               main@%.1.i3985_0
                               main@%loop.bound1_0
                               main@%_69_0
                               main@%shadow.mem.0.6_0
                               main@%.09.i36_0)
                true
                (= main@%_89_0 (+ main@%.09.i36_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_90_0 0))
                (> @a_1_0 0)
                (=> main@_93_0 (and main@_93_0 main@.lr.ph37_0))
                (=> (and main@_93_0 main@.lr.ph37_0) main@%_92_0)
                (=> main@_93_0 a!2)
                (=> main@_93_0 (or (<= @a_1_0 0) (> main@%_94_0 0)))
                (=> main@_93_0 (> @a_1_0 0))
                (=> main@_93_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| main@.lr.ph37_0)
                (=> main@_95_0
                    (or (and main@_95_0 main@_93_0)
                        |tuple(main@.lr.ph37_0, main@_95_0)|))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| (not main@%_92_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_0 main@%sm15_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_1 main@%shadow.mem.0.6_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_1))
                (=> main@_95_0 (= main@%_97_0 (> main@%_89_0 main@%.1.i3985_0)))
                (=> main@._crit_edge38_0 (and main@._crit_edge38_0 main@_95_0))
                (=> (and main@._crit_edge38_0 main@_95_0) (not main@%_97_0))
                (=> main@._crit_edge38_0 (= main@%_98_0 (+ main@%.1.i3985_0 1)))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@._crit_edge38_0))
                (=> (and main@.preheader25_0 main@._crit_edge38_0) main@%_69_0)
                (=> main@.preheader25_0
                    (= main@%_68_0 (< main@%.1.i3985_0 main@%loop.bound1_0)))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    main@.preheader25_0)
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    main@._crit_edge38_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25_0, main@.preheader24_0)|
                        |tuple(main@._crit_edge38_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (not main@%_68_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (not main@%_69_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.7_2))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.7_2))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_98_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_0 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_0 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!4
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!5
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_2
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (= main@%_90_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_89_0 4))))
      (a!2 (= main@%_94_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.09.i36_0 4))))
      (a!3 (= main@%_99_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!4 (=> main@.preheader_0 (= main@%_101_0 (+ @a_2_0 (* 0 40) (* 1 4))))))
(let ((a!5 (and (main@.lr.ph37 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%.13.i59_0
                               main@%shadow.mem.4.1_0
                               main@%_24_0
                               main@%.1.i3985_0
                               main@%loop.bound1_0
                               main@%_69_0
                               main@%shadow.mem.0.6_0
                               main@%.09.i36_0)
                true
                (= main@%_89_0 (+ main@%.09.i36_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_90_0 0))
                (> @a_1_0 0)
                (=> main@_93_0 (and main@_93_0 main@.lr.ph37_0))
                (=> (and main@_93_0 main@.lr.ph37_0) main@%_92_0)
                (=> main@_93_0 a!2)
                (=> main@_93_0 (or (<= @a_1_0 0) (> main@%_94_0 0)))
                (=> main@_93_0 (> @a_1_0 0))
                (=> main@_93_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| main@.lr.ph37_0)
                (=> main@_95_0
                    (or (and main@_95_0 main@_93_0)
                        |tuple(main@.lr.ph37_0, main@_95_0)|))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)| (not main@%_92_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_0 main@%sm15_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_1 main@%shadow.mem.0.6_0))
                (=> (and main@_95_0 main@_93_0)
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_0))
                (=> |tuple(main@.lr.ph37_0, main@_95_0)|
                    (= main@%shadow.mem.0.7_2 main@%shadow.mem.0.7_1))
                (=> main@_95_0 (= main@%_97_0 (> main@%_89_0 main@%.1.i3985_0)))
                (=> main@._crit_edge38_0 (and main@._crit_edge38_0 main@_95_0))
                (=> (and main@._crit_edge38_0 main@_95_0) (not main@%_97_0))
                (=> main@._crit_edge38_0 (= main@%_98_0 (+ main@%.1.i3985_0 1)))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@._crit_edge38_0))
                (=> (and main@.preheader25_0 main@._crit_edge38_0) main@%_69_0)
                (=> main@.preheader25_0
                    (= main@%_68_0 (< main@%.1.i3985_0 main@%loop.bound1_0)))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    main@.preheader25_0)
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    main@._crit_edge38_0)
                (=> main@.preheader24_0
                    (or |tuple(main@.preheader25_0, main@.preheader24_0)|
                        |tuple(main@._crit_edge38_0, main@.preheader24_0)|))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (not main@%_68_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (not main@%_69_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_0 main@%shadow.mem.0.7_2))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_0 10))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_1 main@%shadow.mem.0.7_2))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_1 main@%_98_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_0))
                (=> |tuple(main@.preheader25_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%shadow.mem.0.5_2 main@%shadow.mem.0.5_1))
                (=> |tuple(main@._crit_edge38_0, main@.preheader24_0)|
                    (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                (=> main@.preheader24_0
                    (= main@%_71_0 (> main@%.1.i.lcssa_2 9)))
                (=> main@.preheader24_0
                    (= main@%_72_0 (ite main@%_71_0 main@%_24_0 false)))
                (=> main@.preheader23.us.preheader_0
                    (and main@.preheader23.us.preheader_0 main@.preheader24_0))
                (=> (and main@.preheader23.us.preheader_0 main@.preheader24_0)
                    main@%_72_0)
                (=> main@.preheader23.us.preheader_0
                    (= main@%_73_0 (< main@%.13.i59_0 9)))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    main@.preheader23.us.preheader_0)
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    main@.preheader24_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                        |tuple(main@.preheader24_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (not main@%_73_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (not main@%_72_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.1_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.1_0))
                (=> |tuple(main@.preheader23.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader24_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                a!4
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph34.us.preheader
                  @a_1_0
                  main@%shadow.mem.0.5_0
                  @a_2_0
                  main@%.2.i35.us84_0
                  main@%loop.bound_0
                  main@%shadow.mem.4.6_0
                  main@%_76_0)
                true
                (= main@%_77_0 (+ @a_2_0 (* 0 40) (* 9 4)))
                (or (<= @a_2_0 0) (> main@%_77_0 0))
                (> @a_2_0 0)
                (=> main@.lr.ph34.us_0
                    (and main@.lr.ph34.us_0 main@.lr.ph34.us.preheader_0))
                (=> (and main@.lr.ph34.us_0 main@.lr.ph34.us.preheader_0)
                    (= main@%shadow.mem.4.7_0 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us_0 main@.lr.ph34.us.preheader_0)
                    (= main@%.07.i33.us_0 9))
                (=> (and main@.lr.ph34.us_0 main@.lr.ph34.us.preheader_0)
                    (= main@%shadow.mem.4.7_1 main@%shadow.mem.4.7_0))
                (=> (and main@.lr.ph34.us_0 main@.lr.ph34.us.preheader_0)
                    (= main@%.07.i33.us_1 main@%.07.i33.us_0))
                main@.lr.ph34.us_0)))
  (=> a!1
      (main@.lr.ph34.us @a_1_0
                        main@%shadow.mem.0.5_0
                        @a_2_0
                        main@%.2.i35.us84_0
                        main@%loop.bound_0
                        main@%_76_0
                        main@%shadow.mem.4.7_1
                        main@%.07.i33.us_1))))
(rule (let ((a!1 (= main@%_80_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_79_0 4))))
      (a!2 (= main@%_84_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.07.i33.us_0 4)))))
(let ((a!3 (and (main@.lr.ph34.us @a_1_0
                                  main@%shadow.mem.0.5_0
                                  @a_2_0
                                  main@%.2.i35.us84_0
                                  main@%loop.bound_0
                                  main@%_76_0
                                  main@%shadow.mem.4.7_0
                                  main@%.07.i33.us_0)
                true
                (= main@%_79_0 (+ main@%.07.i33.us_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_80_0 0))
                (> @a_2_0 0)
                (=> main@_83_0 (and main@_83_0 main@.lr.ph34.us_0))
                (=> (and main@_83_0 main@.lr.ph34.us_0) main@%_82_0)
                (=> main@_83_0 a!2)
                (=> main@_83_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_83_0 (> @a_2_0 0))
                (=> main@_83_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| main@.lr.ph34.us_0)
                (=> main@_85_0
                    (or (and main@_85_0 main@_83_0)
                        |tuple(main@.lr.ph34.us_0, main@_85_0)|))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| (not main@%_82_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_0 main@%sm13_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_1 main@%shadow.mem.4.7_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_1))
                (=> main@_85_0
                    (= main@%_87_0 (> main@%_79_0 main@%.2.i35.us84_0)))
                (=> main@._crit_edge.us_0
                    (and main@._crit_edge.us_0 main@_85_0))
                (=> (and main@._crit_edge.us_0 main@_85_0) (not main@%_87_0))
                (=> main@.preheader23.us_0
                    (and main@.preheader23.us_0 main@._crit_edge.us_0))
                (=> (and main@.preheader23.us_0 main@._crit_edge.us_0)
                    main@%_76_0)
                (=> main@.preheader23.us_0
                    (= main@%_74_0 (+ main@%.2.i35.us84_0 1)))
                (=> main@.preheader23.us_0
                    (= main@%_75_0 (< main@%.2.i35.us84_0 main@%loop.bound_0)))
                (=> main@.lr.ph34.us.preheader_0
                    (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    main@%_75_0)
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.8_2))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%_76_1 main@%_75_0))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%.2.i35.us84_1 main@%_74_0))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%_76_2 main@%_76_1))
                (=> (and main@.lr.ph34.us.preheader_0 main@.preheader23.us_0)
                    (= main@%.2.i35.us84_2 main@%.2.i35.us84_1))
                main@.lr.ph34.us.preheader_0)))
  (=> a!3
      (main@.lr.ph34.us.preheader
        @a_1_0
        main@%shadow.mem.0.5_0
        @a_2_0
        main@%.2.i35.us84_2
        main@%loop.bound_0
        main@%shadow.mem.4.6_1
        main@%_76_2)))))
(rule (let ((a!1 (= main@%_80_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_79_0 4))))
      (a!2 (= main@%_84_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.07.i33.us_0 4)))))
(let ((a!3 (and (main@.lr.ph34.us @a_1_0
                                  main@%shadow.mem.0.5_0
                                  @a_2_0
                                  main@%.2.i35.us84_0
                                  main@%loop.bound_0
                                  main@%_76_0
                                  main@%shadow.mem.4.7_0
                                  main@%.07.i33.us_0)
                true
                (= main@%_79_0 (+ main@%.07.i33.us_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_80_0 0))
                (> @a_2_0 0)
                (=> main@_83_0 (and main@_83_0 main@.lr.ph34.us_0))
                (=> (and main@_83_0 main@.lr.ph34.us_0) main@%_82_0)
                (=> main@_83_0 a!2)
                (=> main@_83_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_83_0 (> @a_2_0 0))
                (=> main@_83_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| main@.lr.ph34.us_0)
                (=> main@_85_0
                    (or (and main@_85_0 main@_83_0)
                        |tuple(main@.lr.ph34.us_0, main@_85_0)|))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| (not main@%_82_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_0 main@%sm13_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_1 main@%shadow.mem.4.7_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_1))
                (=> main@_85_0
                    (= main@%_87_0 (> main@%_79_0 main@%.2.i35.us84_0)))
                (=> main@.lr.ph34.us_1 (and main@.lr.ph34.us_1 main@_85_0))
                (=> (and main@.lr.ph34.us_1 main@_85_0) main@%_87_0)
                (=> (and main@.lr.ph34.us_1 main@_85_0)
                    (= main@%shadow.mem.4.7_1 main@%shadow.mem.4.8_2))
                (=> (and main@.lr.ph34.us_1 main@_85_0)
                    (= main@%.07.i33.us_1 main@%_79_0))
                (=> (and main@.lr.ph34.us_1 main@_85_0)
                    (= main@%shadow.mem.4.7_2 main@%shadow.mem.4.7_1))
                (=> (and main@.lr.ph34.us_1 main@_85_0)
                    (= main@%.07.i33.us_2 main@%.07.i33.us_1))
                main@.lr.ph34.us_1)))
  (=> a!3
      (main@.lr.ph34.us @a_1_0
                        main@%shadow.mem.0.5_0
                        @a_2_0
                        main@%.2.i35.us84_0
                        main@%loop.bound_0
                        main@%_76_0
                        main@%shadow.mem.4.7_2
                        main@%.07.i33.us_2)))))
(rule (let ((a!1 (= main@%_80_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_79_0 4))))
      (a!2 (= main@%_84_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.07.i33.us_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph34.us @a_1_0
                                  main@%shadow.mem.0.5_0
                                  @a_2_0
                                  main@%.2.i35.us84_0
                                  main@%loop.bound_0
                                  main@%_76_0
                                  main@%shadow.mem.4.7_0
                                  main@%.07.i33.us_0)
                true
                (= main@%_79_0 (+ main@%.07.i33.us_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_80_0 0))
                (> @a_2_0 0)
                (=> main@_83_0 (and main@_83_0 main@.lr.ph34.us_0))
                (=> (and main@_83_0 main@.lr.ph34.us_0) main@%_82_0)
                (=> main@_83_0 a!2)
                (=> main@_83_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_83_0 (> @a_2_0 0))
                (=> main@_83_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| main@.lr.ph34.us_0)
                (=> main@_85_0
                    (or (and main@_85_0 main@_83_0)
                        |tuple(main@.lr.ph34.us_0, main@_85_0)|))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| (not main@%_82_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_0 main@%sm13_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_1 main@%shadow.mem.4.7_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_1))
                (=> main@_85_0
                    (= main@%_87_0 (> main@%_79_0 main@%.2.i35.us84_0)))
                (=> main@._crit_edge.us_0
                    (and main@._crit_edge.us_0 main@_85_0))
                (=> (and main@._crit_edge.us_0 main@_85_0) (not main@%_87_0))
                (=> main@.preheader23.us_0
                    (and main@.preheader23.us_0 main@._crit_edge.us_0))
                (=> (and main@.preheader23.us_0 main@._crit_edge.us_0)
                    main@%_76_0)
                (=> main@.preheader23.us_0
                    (= main@%_74_0 (+ main@%.2.i35.us84_0 1)))
                (=> main@.preheader23.us_0
                    (= main@%_75_0 (< main@%.2.i35.us84_0 main@%loop.bound_0)))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    main@._crit_edge.us_0)
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    main@.preheader23.us_0)
                (=> main@.preheader_0
                    (or |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                        |tuple(main@.preheader23.us_0, main@.preheader_0)|))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (not main@%_76_0))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (not main@%_75_0))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.8_2))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.8_2))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> main@.lr.ph83_0
                    (and main@.lr.ph83_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    main@%or.cond2281_0)
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_0 2))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_0 1))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%_109_1 main@%_109_0))
                (=> (and main@.lr.ph83_0 main@.lr.ph.preheader_0)
                    (= main@%.05.i3182_1 main@%.05.i3182_0))
                main@.lr.ph83_0)))
  (=> a!5
      (main@.lr.ph83 main@%_109_1
                     main@%.05.i3182_1
                     @a_1_0
                     main@%shadow.mem.0.5_0
                     @a_2_0
                     main@%shadow.mem.4.9_2)))))
(rule (let ((a!1 (= main@%_80_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_79_0 4))))
      (a!2 (= main@%_84_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.07.i33.us_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_99_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_101_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph34.us @a_1_0
                                  main@%shadow.mem.0.5_0
                                  @a_2_0
                                  main@%.2.i35.us84_0
                                  main@%loop.bound_0
                                  main@%_76_0
                                  main@%shadow.mem.4.7_0
                                  main@%.07.i33.us_0)
                true
                (= main@%_79_0 (+ main@%.07.i33.us_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_80_0 0))
                (> @a_2_0 0)
                (=> main@_83_0 (and main@_83_0 main@.lr.ph34.us_0))
                (=> (and main@_83_0 main@.lr.ph34.us_0) main@%_82_0)
                (=> main@_83_0 a!2)
                (=> main@_83_0 (or (<= @a_2_0 0) (> main@%_84_0 0)))
                (=> main@_83_0 (> @a_2_0 0))
                (=> main@_83_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| main@.lr.ph34.us_0)
                (=> main@_85_0
                    (or (and main@_85_0 main@_83_0)
                        |tuple(main@.lr.ph34.us_0, main@_85_0)|))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)| (not main@%_82_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_0 main@%sm13_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_1 main@%shadow.mem.4.7_0))
                (=> (and main@_85_0 main@_83_0)
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_0))
                (=> |tuple(main@.lr.ph34.us_0, main@_85_0)|
                    (= main@%shadow.mem.4.8_2 main@%shadow.mem.4.8_1))
                (=> main@_85_0
                    (= main@%_87_0 (> main@%_79_0 main@%.2.i35.us84_0)))
                (=> main@._crit_edge.us_0
                    (and main@._crit_edge.us_0 main@_85_0))
                (=> (and main@._crit_edge.us_0 main@_85_0) (not main@%_87_0))
                (=> main@.preheader23.us_0
                    (and main@.preheader23.us_0 main@._crit_edge.us_0))
                (=> (and main@.preheader23.us_0 main@._crit_edge.us_0)
                    main@%_76_0)
                (=> main@.preheader23.us_0
                    (= main@%_74_0 (+ main@%.2.i35.us84_0 1)))
                (=> main@.preheader23.us_0
                    (= main@%_75_0 (< main@%.2.i35.us84_0 main@%loop.bound_0)))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    main@._crit_edge.us_0)
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    main@.preheader23.us_0)
                (=> main@.preheader_0
                    (or |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                        |tuple(main@.preheader23.us_0, main@.preheader_0)|))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (not main@%_76_0))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (not main@%_75_0))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_0 main@%shadow.mem.4.8_2))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_1 main@%shadow.mem.4.8_2))
                (=> |tuple(main@._crit_edge.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_0))
                (=> |tuple(main@.preheader23.us_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.9_2 main@%shadow.mem.4.9_1))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_99_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_101_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond2030_0 (or main@%_103_0 main@%_105_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond2030_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2281_0 (or main@%_106_0 main@%_108_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2281_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2030_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph83 main@%_109_0
                               main@%.05.i3182_0
                               @a_1_0
                               main@%shadow.mem.0.5_0
                               @a_2_0
                               main@%shadow.mem.4.9_0)
                true
                (= main@%_110_0 (< main@%.05.i3182_0 9))
                main@%_110_0
                (= main@%_111_0 (+ @a_1_0 (* 0 40) (* main@%_109_0 4)))
                (or (<= @a_1_0 0) (> main@%_111_0 0))
                (> @a_1_0 0)
                (= main@%_113_0 (+ @a_2_0 (* 0 40) (* main@%_109_0 4)))
                (or (<= @a_2_0 0) (> main@%_113_0 0))
                (> @a_2_0 0)
                (= main@%or.cond20_0 (or main@%_115_0 main@%_117_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph83_0))
                (=> (and main@.lr.ph_0 main@.lr.ph83_0) main@%or.cond20_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond22_0 (or main@%_118_0 main@%_120_0)))
                (=> main@.lr.ph_0 (= main@%_121_0 (+ main@%_109_0 1)))
                (=> main@.lr.ph83_1 (and main@.lr.ph83_1 main@.lr.ph_0))
                (=> (and main@.lr.ph83_1 main@.lr.ph_0) main@%or.cond22_0)
                (=> (and main@.lr.ph83_1 main@.lr.ph_0)
                    (= main@%_109_1 main@%_121_0))
                (=> (and main@.lr.ph83_1 main@.lr.ph_0)
                    (= main@%.05.i3182_1 main@%_109_0))
                (=> (and main@.lr.ph83_1 main@.lr.ph_0)
                    (= main@%_109_2 main@%_109_1))
                (=> (and main@.lr.ph83_1 main@.lr.ph_0)
                    (= main@%.05.i3182_2 main@%.05.i3182_1))
                main@.lr.ph83_1)))
  (=> a!1
      (main@.lr.ph83 main@%_109_2
                     main@%.05.i3182_2
                     @a_1_0
                     main@%shadow.mem.0.5_0
                     @a_2_0
                     main@%shadow.mem.4.9_0))))
(rule (let ((a!1 (and (main@.lr.ph83 main@%_109_0
                               main@%.05.i3182_0
                               @a_1_0
                               main@%shadow.mem.0.5_0
                               @a_2_0
                               main@%shadow.mem.4.9_0)
                true
                (= main@%_110_0 (< main@%.05.i3182_0 9))
                main@%_110_0
                (= main@%_111_0 (+ @a_1_0 (* 0 40) (* main@%_109_0 4)))
                (or (<= @a_1_0 0) (> main@%_111_0 0))
                (> @a_1_0 0)
                (= main@%_113_0 (+ @a_2_0 (* 0 40) (* main@%_109_0 4)))
                (or (<= @a_2_0 0) (> main@%_113_0 0))
                (> @a_2_0 0)
                (= main@%or.cond20_0 (or main@%_115_0 main@%_117_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph83_0))
                (=> (and main@.lr.ph_0 main@.lr.ph83_0) main@%or.cond20_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond22_0 (or main@%_118_0 main@%_120_0)))
                (=> main@.lr.ph_0 (= main@%_121_0 (+ main@%_109_0 1)))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)| main@.lr.ph_0)
                (=> |tuple(main@.lr.ph83_0, main@verifier.error_0)|
                    main@.lr.ph83_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph_0, main@verifier.error_0)|
                        |tuple(main@.lr.ph83_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)|
                    (not main@%or.cond22_0))
                (=> |tuple(main@.lr.ph83_0, main@verifier.error_0)|
                    (not main@%or.cond20_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

