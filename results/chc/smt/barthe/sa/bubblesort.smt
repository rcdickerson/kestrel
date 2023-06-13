(set-info :original "./results/chc/bytecode/barthe/sa/bubblesort.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@_3 (Int Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@.preheader26 (Int Int Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@.lr.ph39 (Int Int Bool Int Int (Array Int Int) Int (Array Int Int) Int Int ))
(declare-rel main@.lr.ph41 (Int Int (Array Int Int) Bool Int Int Bool (Array Int Int) Int Int Int ))
(declare-rel main@.lr.ph66 (Int Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_86_0 Bool )
(declare-var main@%_88_0 Bool )
(declare-var main@%or.cond20_0 Bool )
(declare-var main@%_78_0 Bool )
(declare-var main@%_79_0 Int )
(declare-var main@%_81_0 Int )
(declare-var main@%_83_0 Bool )
(declare-var main@%_85_0 Bool )
(declare-var main@%or.cond18_0 Bool )
(declare-var main@%_74_0 Bool )
(declare-var main@%_76_0 Bool )
(declare-var main@%or.cond2064_0 Bool )
(declare-var main@%.06.i2965_2 Int )
(declare-var main@%_67_0 Int )
(declare-var main@%_69_0 Int )
(declare-var main@%_71_0 Bool )
(declare-var main@%_73_0 Bool )
(declare-var main@%or.cond1828_0 Bool )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%_57_0 Int )
(declare-var main@%_59_0 Bool )
(declare-var main@%_52_0 Bool )
(declare-var main@%_53_0 Bool )
(declare-var main@%_54_0 Bool )
(declare-var main@%or.cond56_0 Bool )
(declare-var main@%_64_0 Int )
(declare-var main@%_65_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_49_0 Int )
(declare-var main@%_51_0 Bool )
(declare-var main@%.not_0 Bool )
(declare-var main@%shadow.mem.0.4_3 (Array Int Int) )
(declare-var main@%_44_0 Bool )
(declare-var main@%_41_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_39_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_34_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%or.cond_0 Bool )
(declare-var main@%_17_3 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_3_0 Bool )
(declare-var main@%.0.i45_0 Int )
(declare-var main@%.0.i45_1 Int )
(declare-var main@_11_0 Bool )
(declare-var main@_13_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@_16_0 Bool )
(declare-var |tuple(main@_3_0, main@_16_0)| Bool )
(declare-var |tuple(main@_11_0, main@_16_0)| Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%_17_1 Bool )
(declare-var main@%_17_2 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@_3_1 Bool )
(declare-var main@%.0.i45_2 Int )
(declare-var main@.preheader26_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%.01.i44_0 Int )
(declare-var main@%.02.i43_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%.01.i44_1 Int )
(declare-var main@%.02.i43_1 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@.lr.ph39.preheader_0 Bool )
(declare-var main@.lr.ph39_0 Bool )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%.05.i38_0 Int )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%.05.i38_1 Int )
(declare-var main@.preheader25_0 Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%_22_0 Bool )
(declare-var main@.lr.ph41.preheader_0 Bool )
(declare-var main@.lr.ph41_0 Bool )
(declare-var main@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var main@%.04.i40_0 Int )
(declare-var main@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var main@%.04.i40_1 Int )
(declare-var main@.preheader24.thread_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@.preheader22_0 Bool )
(declare-var main@%shadow.mem.0.3_0 (Array Int Int) )
(declare-var main@%.1.i.lcssa_0 Int )
(declare-var main@%shadow.mem.0.3_1 (Array Int Int) )
(declare-var main@%.1.i.lcssa_1 Int )
(declare-var main@.lr.ph32.us.preheader_0 Bool )
(declare-var main@_60_0 Bool )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@.preheader_0 Bool )
(declare-var |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)| Bool )
(declare-var |tuple(main@.preheader22_0, main@.preheader_0)| Bool )
(declare-var main@%shadow.mem.4.4_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.4_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.4_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.4_3 (Array Int Int) )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph66_0 Bool )
(declare-var main@%_77_0 Int )
(declare-var main@%.06.i2965_0 Int )
(declare-var main@%_77_1 Int )
(declare-var main@%.06.i2965_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.preheader_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@_30_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@_32_0 Bool )
(declare-var |tuple(main@.lr.ph39_0, main@_32_0)| Bool )
(declare-var main@%shadow.mem.4.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_2 (Array Int Int) )
(declare-var main@.lr.ph39_1 Bool )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@%.05.i38_2 Int )
(declare-var main@%_36_0 Int )
(declare-var main@_40_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@_42_0 Bool )
(declare-var |tuple(main@.lr.ph41_0, main@_42_0)| Bool )
(declare-var main@%shadow.mem.0.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_2 (Array Int Int) )
(declare-var main@._crit_edge42_0 Bool )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%.01.i44_2 Int )
(declare-var main@%.02.i43_2 Int )
(declare-var main@.lr.ph41_1 Bool )
(declare-var main@%shadow.mem.0.1_2 (Array Int Int) )
(declare-var main@%.04.i40_2 Int )
(declare-var main@.preheader24_0 Bool )
(declare-var main@.preheader23.preheader_0 Bool )
(declare-var main@.lr.ph35.preheader_0 Bool )
(declare-var main@_63_0 Bool )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@._crit_edge36_0 Bool )
(declare-var |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)| Bool )
(declare-var |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)| Bool )
(declare-var main@%shadow.mem.0.4_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.4_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.4_2 (Array Int Int) )
(declare-var main@%_66_0 Int )
(declare-var |tuple(main@.preheader24_0, main@.preheader22_0)| Bool )
(declare-var main@%shadow.mem.0.3_2 (Array Int Int) )
(declare-var main@%.1.i.lcssa_2 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_89_0 Int )
(declare-var main@.lr.ph66_1 Bool )
(declare-var main@%_77_2 Int )
(declare-var |tuple(main@.lr.ph_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.lr.ph66_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm12_0 main@%sm13_0))
(rule (=> (and (main@entry main@%sm12_0 main@%sm13_0)
         true
         (= main@%sm_0 main@%sm13_0)
         (= main@%sm3_0 main@%sm12_0)
         (= main@%_0_0 (= main@%loop.bound_0 9))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%sm_0
                     main@%sm3_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%sm_0
                          main@%sm3_0)
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
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%sm_0
                     main@%sm3_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%sm_0
                          main@%sm3_0)
         true
         (=> main@_3_0 (and main@_3_0 main@empty.loop_0))
         (=> (and main@_3_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i45_0 1))
         (=> (and main@_3_0 main@empty.loop_0)
             (= main@%.0.i45_1 main@%.0.i45_0))
         main@_3_0)
    (main@_3 @a_1_0
             @a_2_0
             main@%loop.bound_0
             main@%loop.bound1_0
             main@%.0.i45_1
             main@%loop.bound2_0
             main@%sm_0
             main@%sm3_0)))
(rule (let ((a!1 (and (main@_3 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%.0.i45_0
                         main@%loop.bound2_0
                         main@%sm_0
                         main@%sm3_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i45_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i45_0 4)))
                (or (<= @a_2_0 0) (> main@%_6_0 0))
                (> @a_2_0 0)
                (= main@%or.cond_0 (or main@%_8_0 main@%_10_0))
                (=> main@_11_0 (and main@_11_0 main@_3_0))
                (=> (and main@_11_0 main@_3_0) main@%or.cond_0)
                (=> main@_13_0 (and main@_13_0 main@_11_0))
                (=> (and main@_13_0 main@_11_0) (not main@%_12_0))
                (=> |tuple(main@_3_0, main@_16_0)| main@_3_0)
                (=> |tuple(main@_11_0, main@_16_0)| main@_11_0)
                (=> main@_16_0
                    (or |tuple(main@_3_0, main@_16_0)|
                        (and main@_16_0 main@_13_0)
                        |tuple(main@_11_0, main@_16_0)|))
                (=> |tuple(main@_3_0, main@_16_0)| (not main@%or.cond_0))
                (=> |tuple(main@_11_0, main@_16_0)| main@%_12_0)
                (=> |tuple(main@_3_0, main@_16_0)| (= main@%_17_0 false))
                (=> (and main@_16_0 main@_13_0) (= main@%_17_1 main@%_15_0))
                (=> |tuple(main@_11_0, main@_16_0)| (= main@%_17_2 true))
                (=> |tuple(main@_3_0, main@_16_0)| (= main@%_17_3 main@%_17_0))
                (=> (and main@_16_0 main@_13_0) (= main@%_17_3 main@%_17_1))
                (=> |tuple(main@_11_0, main@_16_0)| (= main@%_17_3 main@%_17_2))
                (=> main@_16_0 main@%_17_3)
                (=> main@_16_0 (= main@%_18_0 (+ main@%.0.i45_0 1)))
                (=> main@_16_0
                    (= main@%_19_0 (< main@%.0.i45_0 main@%loop.bound2_0)))
                (=> main@_3_1 (and main@_3_1 main@_16_0))
                (=> (and main@_3_1 main@_16_0) main@%_19_0)
                (=> (and main@_3_1 main@_16_0) (= main@%.0.i45_1 main@%_18_0))
                (=> (and main@_3_1 main@_16_0)
                    (= main@%.0.i45_2 main@%.0.i45_1))
                main@_3_1)))
  (=> a!1
      (main@_3 @a_1_0
               @a_2_0
               main@%loop.bound_0
               main@%loop.bound1_0
               main@%.0.i45_2
               main@%loop.bound2_0
               main@%sm_0
               main@%sm3_0))))
(rule (let ((a!1 (and (main@_3 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%loop.bound1_0
                         main@%.0.i45_0
                         main@%loop.bound2_0
                         main@%sm_0
                         main@%sm3_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i45_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i45_0 4)))
                (or (<= @a_2_0 0) (> main@%_6_0 0))
                (> @a_2_0 0)
                (= main@%or.cond_0 (or main@%_8_0 main@%_10_0))
                (=> main@_11_0 (and main@_11_0 main@_3_0))
                (=> (and main@_11_0 main@_3_0) main@%or.cond_0)
                (=> main@_13_0 (and main@_13_0 main@_11_0))
                (=> (and main@_13_0 main@_11_0) (not main@%_12_0))
                (=> |tuple(main@_3_0, main@_16_0)| main@_3_0)
                (=> |tuple(main@_11_0, main@_16_0)| main@_11_0)
                (=> main@_16_0
                    (or |tuple(main@_3_0, main@_16_0)|
                        (and main@_16_0 main@_13_0)
                        |tuple(main@_11_0, main@_16_0)|))
                (=> |tuple(main@_3_0, main@_16_0)| (not main@%or.cond_0))
                (=> |tuple(main@_11_0, main@_16_0)| main@%_12_0)
                (=> |tuple(main@_3_0, main@_16_0)| (= main@%_17_0 false))
                (=> (and main@_16_0 main@_13_0) (= main@%_17_1 main@%_15_0))
                (=> |tuple(main@_11_0, main@_16_0)| (= main@%_17_2 true))
                (=> |tuple(main@_3_0, main@_16_0)| (= main@%_17_3 main@%_17_0))
                (=> (and main@_16_0 main@_13_0) (= main@%_17_3 main@%_17_1))
                (=> |tuple(main@_11_0, main@_16_0)| (= main@%_17_3 main@%_17_2))
                (=> main@_16_0 main@%_17_3)
                (=> main@_16_0 (= main@%_18_0 (+ main@%.0.i45_0 1)))
                (=> main@_16_0
                    (= main@%_19_0 (< main@%.0.i45_0 main@%loop.bound2_0)))
                (=> main@.preheader26_0 (and main@.preheader26_0 main@_16_0))
                (=> (and main@.preheader26_0 main@_16_0) (not main@%_19_0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%shadow.mem.4.0_0 main@%sm3_0))
                (=> (and main@.preheader26_0 main@_16_0) (= main@%.01.i44_0 0))
                (=> (and main@.preheader26_0 main@_16_0) (= main@%.02.i43_0 0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%.01.i44_1 main@%.01.i44_0))
                (=> (and main@.preheader26_0 main@_16_0)
                    (= main@%.02.i43_1 main@%.02.i43_0))
                main@.preheader26_0)))
  (=> a!1
      (main@.preheader26
        @a_1_0
        @a_2_0
        main@%.02.i43_1
        main@%.01.i44_1
        main@%shadow.mem.0.0_1
        main@%shadow.mem.4.0_1
        main@%loop.bound_0
        main@%loop.bound1_0))))
(rule (let ((a!1 (=> main@.lr.ph39.preheader_0
               (= main@%_21_0 (+ @a_2_0 (* 0 40) (* 9 4))))))
(let ((a!2 (and (main@.preheader26
                  @a_1_0
                  @a_2_0
                  main@%.02.i43_0
                  main@%.01.i44_0
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_20_0 (< main@%.02.i43_0 main@%loop.bound1_0))
                (=> main@.lr.ph39.preheader_0
                    (and main@.lr.ph39.preheader_0 main@.preheader26_0))
                (=> (and main@.lr.ph39.preheader_0 main@.preheader26_0)
                    main@%_20_0)
                a!1
                (=> main@.lr.ph39.preheader_0
                    (or (<= @a_2_0 0) (> main@%_21_0 0)))
                (=> main@.lr.ph39.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph39_0
                    (and main@.lr.ph39_0 main@.lr.ph39.preheader_0))
                (=> (and main@.lr.ph39_0 main@.lr.ph39.preheader_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph39_0 main@.lr.ph39.preheader_0)
                    (= main@%.05.i38_0 9))
                (=> (and main@.lr.ph39_0 main@.lr.ph39.preheader_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@.lr.ph39_0 main@.lr.ph39.preheader_0)
                    (= main@%.05.i38_1 main@%.05.i38_0))
                main@.lr.ph39_0)))
  (=> a!2
      (main@.lr.ph39 @a_1_0
                     @a_2_0
                     main@%_20_0
                     main@%.02.i43_0
                     main@%.01.i44_0
                     main@%shadow.mem.0.0_0
                     main@%loop.bound_0
                     main@%shadow.mem.4.2_1
                     main@%.05.i38_1
                     main@%loop.bound1_0)))))
(rule (let ((a!1 (=> main@.lr.ph41.preheader_0
               (= main@%_24_0 (+ @a_1_0 (* 0 40) (* 9 4))))))
(let ((a!2 (and (main@.preheader26
                  @a_1_0
                  @a_2_0
                  main@%.02.i43_0
                  main@%.01.i44_0
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_20_0 (< main@%.02.i43_0 main@%loop.bound1_0))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@.preheader26_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (not main@%_20_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.lr.ph41.preheader_0
                    (and main@.lr.ph41.preheader_0 main@.preheader25_0))
                (=> (and main@.lr.ph41.preheader_0 main@.preheader25_0)
                    main@%_22_0)
                a!1
                (=> main@.lr.ph41.preheader_0
                    (or (<= @a_1_0 0) (> main@%_24_0 0)))
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
                     main@%shadow.mem.4.1_1
                     main@%_20_0
                     main@%.02.i43_0
                     main@%.01.i44_0
                     main@%_22_0
                     main@%shadow.mem.0.1_1
                     main@%.04.i40_1
                     main@%loop.bound_0
                     main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!2 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!3 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!4 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!5 (=> main@.preheader_0 (= main@%_67_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!6 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!7 (and (main@.preheader26
                  @a_1_0
                  @a_2_0
                  main@%.02.i43_0
                  main@%.01.i44_0
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_20_0 (< main@%.02.i43_0 main@%loop.bound1_0))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@.preheader26_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (not main@%_20_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.preheader24.thread_0
                    (and main@.preheader24.thread_0 main@.preheader25_0))
                (=> (and main@.preheader24.thread_0 main@.preheader25_0)
                    (not main@%_22_0))
                (=> main@.preheader24.thread_0
                    (= main@%_23_0 (+ main@%.01.i44_0 1)))
                (=> main@.preheader22_0
                    (and main@.preheader22_0 main@.preheader24.thread_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_0 main@%_23_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader22_0
                    (= main@%_52_0 (> main@%.1.i.lcssa_1 9)))
                (=> main@.preheader22_0
                    (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                (=> main@.preheader22_0
                    (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph32.us.preheader_0
                    (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                    main@%or.cond56_0)
                (=> main@.lr.ph32.us.preheader_0 a!1)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph32.us.preheader_0 a!2)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_57_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                (=> main@_60_0 a!3)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> main@_60_0 a!4)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    main@.lr.ph32.us.preheader_0)
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    main@.preheader22_0)
                (=> main@.preheader_0
                    (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                        (and main@.preheader_0 main@_60_0)
                        |tuple(main@.preheader22_0, main@.preheader_0)|))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (not main@%_59_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (not main@%or.cond56_0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_1))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_1 main@%sm9_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                true
                a!5
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!6)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1828_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                (=> main@.lr.ph66_0
                    (and main@.lr.ph66_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    main@%or.cond2064_0)
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%_77_0 2))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%.06.i2965_0 1))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%_77_1 main@%_77_0))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%.06.i2965_1 main@%.06.i2965_0))
                main@.lr.ph66_0)))
  (=> a!7
      (main@.lr.ph66 main@%_77_1
                     main@%.06.i2965_1
                     @a_1_0
                     main@%shadow.mem.0.3_1
                     @a_2_0
                     main@%shadow.mem.4.4_3)))))
(rule (let ((a!1 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!2 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!3 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!4 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!5 (=> main@.preheader_0 (= main@%_67_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!6 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!7 (and (main@.preheader26
                  @a_1_0
                  @a_2_0
                  main@%.02.i43_0
                  main@%.01.i44_0
                  main@%shadow.mem.0.0_0
                  main@%shadow.mem.4.0_0
                  main@%loop.bound_0
                  main@%loop.bound1_0)
                true
                (= main@%_20_0 (< main@%.02.i43_0 main@%loop.bound1_0))
                (=> main@.preheader25_0
                    (and main@.preheader25_0 main@.preheader26_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (not main@%_20_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader25_0 main@.preheader26_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.preheader24.thread_0
                    (and main@.preheader24.thread_0 main@.preheader25_0))
                (=> (and main@.preheader24.thread_0 main@.preheader25_0)
                    (not main@%_22_0))
                (=> main@.preheader24.thread_0
                    (= main@%_23_0 (+ main@%.01.i44_0 1)))
                (=> main@.preheader22_0
                    (and main@.preheader22_0 main@.preheader24.thread_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_0 main@%_23_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader22_0
                    (= main@%_52_0 (> main@%.1.i.lcssa_1 9)))
                (=> main@.preheader22_0
                    (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                (=> main@.preheader22_0
                    (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph32.us.preheader_0
                    (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                    main@%or.cond56_0)
                (=> main@.lr.ph32.us.preheader_0 a!1)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph32.us.preheader_0 a!2)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_57_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                (=> main@_60_0 a!3)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> main@_60_0 a!4)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    main@.lr.ph32.us.preheader_0)
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    main@.preheader22_0)
                (=> main@.preheader_0
                    (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                        (and main@.preheader_0 main@_60_0)
                        |tuple(main@.preheader22_0, main@.preheader_0)|))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (not main@%_59_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (not main@%or.cond56_0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_1))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_1 main@%sm9_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                true
                a!5
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!6)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1828_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2064_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond1828_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!7 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_27_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_26_0 4))))
      (a!2 (= main@%_31_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i38_0 4)))))
(let ((a!3 (and (main@.lr.ph39 @a_1_0
                               @a_2_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%shadow.mem.0.0_0
                               main@%loop.bound_0
                               main@%shadow.mem.4.2_0
                               main@%.05.i38_0
                               main@%loop.bound1_0)
                true
                (= main@%_26_0 (+ main@%.05.i38_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_27_0 0))
                (> @a_2_0 0)
                (=> main@_30_0 (and main@_30_0 main@.lr.ph39_0))
                (=> (and main@_30_0 main@.lr.ph39_0) main@%_29_0)
                (=> main@_30_0 a!2)
                (=> main@_30_0 (or (<= @a_2_0 0) (> main@%_31_0 0)))
                (=> main@_30_0 (> @a_2_0 0))
                (=> main@_30_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| main@.lr.ph39_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_30_0)
                        |tuple(main@.lr.ph39_0, main@_32_0)|))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| (not main@%_29_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_32_0 (= main@%_34_0 (> main@%_26_0 main@%.02.i43_0)))
                (=> main@.lr.ph39_1 (and main@.lr.ph39_1 main@_32_0))
                (=> (and main@.lr.ph39_1 main@_32_0) main@%_34_0)
                (=> (and main@.lr.ph39_1 main@_32_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.3_2))
                (=> (and main@.lr.ph39_1 main@_32_0)
                    (= main@%.05.i38_1 main@%_26_0))
                (=> (and main@.lr.ph39_1 main@_32_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> (and main@.lr.ph39_1 main@_32_0)
                    (= main@%.05.i38_2 main@%.05.i38_1))
                main@.lr.ph39_1)))
  (=> a!3
      (main@.lr.ph39 @a_1_0
                     @a_2_0
                     main@%_20_0
                     main@%.02.i43_0
                     main@%.01.i44_0
                     main@%shadow.mem.0.0_0
                     main@%loop.bound_0
                     main@%shadow.mem.4.2_2
                     main@%.05.i38_2
                     main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_27_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_26_0 4))))
      (a!2 (= main@%_31_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i38_0 4))))
      (a!3 (=> main@.lr.ph41.preheader_0
               (= main@%_24_0 (+ @a_1_0 (* 0 40) (* 9 4))))))
(let ((a!4 (and (main@.lr.ph39 @a_1_0
                               @a_2_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%shadow.mem.0.0_0
                               main@%loop.bound_0
                               main@%shadow.mem.4.2_0
                               main@%.05.i38_0
                               main@%loop.bound1_0)
                true
                (= main@%_26_0 (+ main@%.05.i38_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_27_0 0))
                (> @a_2_0 0)
                (=> main@_30_0 (and main@_30_0 main@.lr.ph39_0))
                (=> (and main@_30_0 main@.lr.ph39_0) main@%_29_0)
                (=> main@_30_0 a!2)
                (=> main@_30_0 (or (<= @a_2_0 0) (> main@%_31_0 0)))
                (=> main@_30_0 (> @a_2_0 0))
                (=> main@_30_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| main@.lr.ph39_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_30_0)
                        |tuple(main@.lr.ph39_0, main@_32_0)|))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| (not main@%_29_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_32_0 (= main@%_34_0 (> main@%_26_0 main@%.02.i43_0)))
                (=> main@.preheader25_0 (and main@.preheader25_0 main@_32_0))
                (=> (and main@.preheader25_0 main@_32_0) (not main@%_34_0))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.lr.ph41.preheader_0
                    (and main@.lr.ph41.preheader_0 main@.preheader25_0))
                (=> (and main@.lr.ph41.preheader_0 main@.preheader25_0)
                    main@%_22_0)
                a!3
                (=> main@.lr.ph41.preheader_0
                    (or (<= @a_1_0 0) (> main@%_24_0 0)))
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
  (=> a!4
      (main@.lr.ph41 @a_1_0
                     @a_2_0
                     main@%shadow.mem.4.1_1
                     main@%_20_0
                     main@%.02.i43_0
                     main@%.01.i44_0
                     main@%_22_0
                     main@%shadow.mem.0.1_1
                     main@%.04.i40_1
                     main@%loop.bound_0
                     main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_27_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_26_0 4))))
      (a!2 (= main@%_31_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i38_0 4))))
      (a!3 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!4 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!5 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!6 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!7 (=> main@.preheader_0 (= main@%_67_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!8 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!9 (and (main@.lr.ph39 @a_1_0
                               @a_2_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%shadow.mem.0.0_0
                               main@%loop.bound_0
                               main@%shadow.mem.4.2_0
                               main@%.05.i38_0
                               main@%loop.bound1_0)
                true
                (= main@%_26_0 (+ main@%.05.i38_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_27_0 0))
                (> @a_2_0 0)
                (=> main@_30_0 (and main@_30_0 main@.lr.ph39_0))
                (=> (and main@_30_0 main@.lr.ph39_0) main@%_29_0)
                (=> main@_30_0 a!2)
                (=> main@_30_0 (or (<= @a_2_0 0) (> main@%_31_0 0)))
                (=> main@_30_0 (> @a_2_0 0))
                (=> main@_30_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| main@.lr.ph39_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_30_0)
                        |tuple(main@.lr.ph39_0, main@_32_0)|))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| (not main@%_29_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_32_0 (= main@%_34_0 (> main@%_26_0 main@%.02.i43_0)))
                (=> main@.preheader25_0 (and main@.preheader25_0 main@_32_0))
                (=> (and main@.preheader25_0 main@_32_0) (not main@%_34_0))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.preheader24.thread_0
                    (and main@.preheader24.thread_0 main@.preheader25_0))
                (=> (and main@.preheader24.thread_0 main@.preheader25_0)
                    (not main@%_22_0))
                (=> main@.preheader24.thread_0
                    (= main@%_23_0 (+ main@%.01.i44_0 1)))
                (=> main@.preheader22_0
                    (and main@.preheader22_0 main@.preheader24.thread_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_0 main@%_23_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader22_0
                    (= main@%_52_0 (> main@%.1.i.lcssa_1 9)))
                (=> main@.preheader22_0
                    (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                (=> main@.preheader22_0
                    (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph32.us.preheader_0
                    (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                    main@%or.cond56_0)
                (=> main@.lr.ph32.us.preheader_0 a!3)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph32.us.preheader_0 a!4)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_57_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                (=> main@_60_0 a!5)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> main@_60_0 a!6)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    main@.lr.ph32.us.preheader_0)
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    main@.preheader22_0)
                (=> main@.preheader_0
                    (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                        (and main@.preheader_0 main@_60_0)
                        |tuple(main@.preheader22_0, main@.preheader_0)|))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (not main@%_59_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (not main@%or.cond56_0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_1))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_1 main@%sm9_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                true
                a!7
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!8)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1828_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                (=> main@.lr.ph66_0
                    (and main@.lr.ph66_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    main@%or.cond2064_0)
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%_77_0 2))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%.06.i2965_0 1))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%_77_1 main@%_77_0))
                (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                    (= main@%.06.i2965_1 main@%.06.i2965_0))
                main@.lr.ph66_0)))
  (=> a!9
      (main@.lr.ph66 main@%_77_1
                     main@%.06.i2965_1
                     @a_1_0
                     main@%shadow.mem.0.3_1
                     @a_2_0
                     main@%shadow.mem.4.4_3)))))
(rule (let ((a!1 (= main@%_27_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_26_0 4))))
      (a!2 (= main@%_31_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i38_0 4))))
      (a!3 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!4 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!5 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!6 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!7 (=> main@.preheader_0 (= main@%_67_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!8 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!9 (and (main@.lr.ph39 @a_1_0
                               @a_2_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%shadow.mem.0.0_0
                               main@%loop.bound_0
                               main@%shadow.mem.4.2_0
                               main@%.05.i38_0
                               main@%loop.bound1_0)
                true
                (= main@%_26_0 (+ main@%.05.i38_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_27_0 0))
                (> @a_2_0 0)
                (=> main@_30_0 (and main@_30_0 main@.lr.ph39_0))
                (=> (and main@_30_0 main@.lr.ph39_0) main@%_29_0)
                (=> main@_30_0 a!2)
                (=> main@_30_0 (or (<= @a_2_0 0) (> main@%_31_0 0)))
                (=> main@_30_0 (> @a_2_0 0))
                (=> main@_30_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| main@.lr.ph39_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_30_0)
                        |tuple(main@.lr.ph39_0, main@_32_0)|))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)| (not main@%_29_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.2_0))
                (=> (and main@_32_0 main@_30_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_0))
                (=> |tuple(main@.lr.ph39_0, main@_32_0)|
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> main@_32_0 (= main@%_34_0 (> main@%_26_0 main@%.02.i43_0)))
                (=> main@.preheader25_0 (and main@.preheader25_0 main@_32_0))
                (=> (and main@.preheader25_0 main@_32_0) (not main@%_34_0))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.3_2))
                (=> (and main@.preheader25_0 main@_32_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> main@.preheader25_0
                    (= main@%_22_0 (< main@%.01.i44_0 main@%loop.bound_0)))
                (=> main@.preheader24.thread_0
                    (and main@.preheader24.thread_0 main@.preheader25_0))
                (=> (and main@.preheader24.thread_0 main@.preheader25_0)
                    (not main@%_22_0))
                (=> main@.preheader24.thread_0
                    (= main@%_23_0 (+ main@%.01.i44_0 1)))
                (=> main@.preheader22_0
                    (and main@.preheader22_0 main@.preheader24.thread_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_0 main@%_23_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> (and main@.preheader22_0 main@.preheader24.thread_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader22_0
                    (= main@%_52_0 (> main@%.1.i.lcssa_1 9)))
                (=> main@.preheader22_0
                    (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                (=> main@.preheader22_0
                    (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph32.us.preheader_0
                    (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                    main@%or.cond56_0)
                (=> main@.lr.ph32.us.preheader_0 a!3)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@.lr.ph32.us.preheader_0 a!4)
                (=> main@.lr.ph32.us.preheader_0
                    (or (<= @a_2_0 0) (> main@%_57_0 0)))
                (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                (=> main@_60_0 a!5)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> main@_60_0 a!6)
                (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                (=> main@_60_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    main@.lr.ph32.us.preheader_0)
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    main@.preheader22_0)
                (=> main@.preheader_0
                    (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                        (and main@.preheader_0 main@_60_0)
                        |tuple(main@.preheader22_0, main@.preheader_0)|))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (not main@%_59_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (not main@%or.cond56_0))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_1))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_1 main@%sm9_0))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_1))
                (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader_0 main@_60_0)
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                    (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                true
                a!7
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!8)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1828_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond2064_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond1828_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!9 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_37_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_36_0 4))))
      (a!2 (= main@%_41_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4)))))
(let ((a!3 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%shadow.mem.4.1_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%_22_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0
                               main@%loop.bound_0
                               main@%loop.bound1_0)
                true
                (= main@%_36_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_37_0 0))
                (> @a_1_0 0)
                (=> main@_40_0 (and main@_40_0 main@.lr.ph41_0))
                (=> (and main@_40_0 main@.lr.ph41_0) main@%_39_0)
                (=> main@_40_0 a!2)
                (=> main@_40_0 (or (<= @a_1_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @a_1_0 0))
                (=> main@_40_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)| main@.lr.ph41_0)
                (=> main@_42_0
                    (or (and main@_42_0 main@_40_0)
                        |tuple(main@.lr.ph41_0, main@_42_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)| (not main@%_39_0))
                (=> (and main@_42_0 main@_40_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_42_0 main@_40_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_42_0 (= main@%_44_0 (> main@%_36_0 main@%.01.i44_0)))
                (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_42_0))
                (=> (and main@._crit_edge42_0 main@_42_0) (not main@%_44_0))
                (=> main@._crit_edge42_0 (= main@%_45_0 (+ main@%.02.i43_0 1)))
                (=> main@._crit_edge42_0 (= main@%_46_0 (+ main@%.01.i44_0 1)))
                (=> main@.preheader26_0
                    (and main@.preheader26_0 main@._crit_edge42_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0) main@%_20_0)
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.2_2))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%shadow.mem.4.0_0 main@%shadow.mem.4.1_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%.01.i44_1 main@%_46_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%.02.i43_1 main@%_45_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%.01.i44_2 main@%.01.i44_1))
                (=> (and main@.preheader26_0 main@._crit_edge42_0)
                    (= main@%.02.i43_2 main@%.02.i43_1))
                main@.preheader26_0)))
  (=> a!3
      (main@.preheader26
        @a_1_0
        @a_2_0
        main@%.02.i43_2
        main@%.01.i44_2
        main@%shadow.mem.0.0_1
        main@%shadow.mem.4.0_1
        main@%loop.bound_0
        main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_37_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_36_0 4))))
      (a!2 (= main@%_41_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4)))))
(let ((a!3 (and (main@.lr.ph41 @a_1_0
                               @a_2_0
                               main@%shadow.mem.4.1_0
                               main@%_20_0
                               main@%.02.i43_0
                               main@%.01.i44_0
                               main@%_22_0
                               main@%shadow.mem.0.1_0
                               main@%.04.i40_0
                               main@%loop.bound_0
                               main@%loop.bound1_0)
                true
                (= main@%_36_0 (+ main@%.04.i40_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_37_0 0))
                (> @a_1_0 0)
                (=> main@_40_0 (and main@_40_0 main@.lr.ph41_0))
                (=> (and main@_40_0 main@.lr.ph41_0) main@%_39_0)
                (=> main@_40_0 a!2)
                (=> main@_40_0 (or (<= @a_1_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @a_1_0 0))
                (=> main@_40_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)| main@.lr.ph41_0)
                (=> main@_42_0
                    (or (and main@_42_0 main@_40_0)
                        |tuple(main@.lr.ph41_0, main@_42_0)|))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)| (not main@%_39_0))
                (=> (and main@_42_0 main@_40_0)
                    (= main@%shadow.mem.0.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_42_0 main@_40_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_42_0 (= main@%_44_0 (> main@%_36_0 main@%.01.i44_0)))
                (=> main@.lr.ph41_1 (and main@.lr.ph41_1 main@_42_0))
                (=> (and main@.lr.ph41_1 main@_42_0) main@%_44_0)
                (=> (and main@.lr.ph41_1 main@_42_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.2_2))
                (=> (and main@.lr.ph41_1 main@_42_0)
                    (= main@%.04.i40_1 main@%_36_0))
                (=> (and main@.lr.ph41_1 main@_42_0)
                    (= main@%shadow.mem.0.1_2 main@%shadow.mem.0.1_1))
                (=> (and main@.lr.ph41_1 main@_42_0)
                    (= main@%.04.i40_2 main@%.04.i40_1))
                main@.lr.ph41_1)))
  (=> a!3
      (main@.lr.ph41 @a_1_0
                     @a_2_0
                     main@%shadow.mem.4.1_0
                     main@%_20_0
                     main@%.02.i43_0
                     main@%.01.i44_0
                     main@%_22_0
                     main@%shadow.mem.0.1_2
                     main@%.04.i40_2
                     main@%loop.bound_0
                     main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_37_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_36_0 4))))
      (a!2 (= main@%_41_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4))))
      (a!3 (= main@%_47_0 (+ (+ @a_1_0 (* 0 40)) (* 8 4))))
      (a!4 (= main@%_49_0 (+ (+ @a_1_0 (* 0 40)) (* 9 4))))
      (a!5 (= main@%_64_0 (+ (+ @a_1_0 (* 0 40)) (* 9 4))))
      (a!6 (= main@%_65_0 (+ (+ @a_1_0 (* 0 40)) (* 8 4))))
      (a!7 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!8 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!9 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!10 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!11 (= main@%_67_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!12 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!13 (and (main@.lr.ph41 @a_1_0
                                @a_2_0
                                main@%shadow.mem.4.1_0
                                main@%_20_0
                                main@%.02.i43_0
                                main@%.01.i44_0
                                main@%_22_0
                                main@%shadow.mem.0.1_0
                                main@%.04.i40_0
                                main@%loop.bound_0
                                main@%loop.bound1_0)
                 true
                 (= main@%_36_0 (+ main@%.04.i40_0 (- 1)))
                 a!1
                 (or (<= @a_1_0 0) (> main@%_37_0 0))
                 (> @a_1_0 0)
                 (=> main@_40_0 (and main@_40_0 main@.lr.ph41_0))
                 (=> (and main@_40_0 main@.lr.ph41_0) main@%_39_0)
                 (=> main@_40_0 a!2)
                 (=> main@_40_0 (or (<= @a_1_0 0) (> main@%_41_0 0)))
                 (=> main@_40_0 (> @a_1_0 0))
                 (=> main@_40_0 (> @a_1_0 0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)| main@.lr.ph41_0)
                 (=> main@_42_0
                     (or (and main@_42_0 main@_40_0)
                         |tuple(main@.lr.ph41_0, main@_42_0)|))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)| (not main@%_39_0))
                 (=> (and main@_42_0 main@_40_0)
                     (= main@%shadow.mem.0.2_0 main@%sm7_0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                     (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                 (=> (and main@_42_0 main@_40_0)
                     (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                     (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                 (=> main@_42_0 (= main@%_44_0 (> main@%_36_0 main@%.01.i44_0)))
                 (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_42_0))
                 (=> (and main@._crit_edge42_0 main@_42_0) (not main@%_44_0))
                 (=> main@._crit_edge42_0 (= main@%_45_0 (+ main@%.02.i43_0 1)))
                 (=> main@._crit_edge42_0 (= main@%_46_0 (+ main@%.01.i44_0 1)))
                 (=> main@.preheader24_0
                     (and main@.preheader24_0 main@._crit_edge42_0))
                 (=> (and main@.preheader24_0 main@._crit_edge42_0)
                     (not main@%_20_0))
                 (=> main@.preheader23.preheader_0
                     (and main@.preheader23.preheader_0 main@.preheader24_0))
                 (=> (and main@.preheader23.preheader_0 main@.preheader24_0)
                     main@%_22_0)
                 (=> main@.preheader23.preheader_0
                     (= main@%.not_0 (= main@%.01.i44_0 8)))
                 (=> main@.lr.ph35.preheader_0
                     (and main@.lr.ph35.preheader_0
                          main@.preheader23.preheader_0))
                 (=> (and main@.lr.ph35.preheader_0
                          main@.preheader23.preheader_0)
                     (not main@%.not_0))
                 (=> main@.lr.ph35.preheader_0 a!3)
                 (=> main@.lr.ph35.preheader_0
                     (or (<= @a_1_0 0) (> main@%_47_0 0)))
                 (=> main@.lr.ph35.preheader_0 (> @a_1_0 0))
                 (=> main@.lr.ph35.preheader_0 a!4)
                 (=> main@.lr.ph35.preheader_0
                     (or (<= @a_1_0 0) (> main@%_49_0 0)))
                 (=> main@.lr.ph35.preheader_0 (> @a_1_0 0))
                 (=> main@_63_0 (and main@_63_0 main@.lr.ph35.preheader_0))
                 (=> (and main@_63_0 main@.lr.ph35.preheader_0) main@%_51_0)
                 (=> main@_63_0 a!5)
                 (=> main@_63_0 (or (<= @a_1_0 0) (> main@%_64_0 0)))
                 (=> main@_63_0 (> @a_1_0 0))
                 (=> main@_63_0 a!6)
                 (=> main@_63_0 (or (<= @a_1_0 0) (> main@%_65_0 0)))
                 (=> main@_63_0 (> @a_1_0 0))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     main@.lr.ph35.preheader_0)
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     main@.preheader23.preheader_0)
                 (=> main@._crit_edge36_0
                     (or |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                         (and main@._crit_edge36_0 main@_63_0)
                         |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (not main@%_51_0))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     main@%.not_0)
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.2_2))
                 (=> (and main@._crit_edge36_0 main@_63_0)
                     (= main@%shadow.mem.0.4_1 main@%sm11_0))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_2 main@%shadow.mem.0.2_2))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_0))
                 (=> (and main@._crit_edge36_0 main@_63_0)
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_1))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_2))
                 (=> main@._crit_edge36_0 (= main@%_66_0 (+ main@%.01.i44_0 2)))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     main@.preheader24_0)
                 (=> main@.preheader22_0
                     (or (and main@.preheader22_0 main@._crit_edge36_0)
                         |tuple(main@.preheader24_0, main@.preheader22_0)|))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (not main@%_22_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.4_3))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%.1.i.lcssa_0 main@%_66_0))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.2_2))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%.1.i.lcssa_1 main@%_46_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%shadow.mem.0.3_2 main@%shadow.mem.0.3_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%shadow.mem.0.3_2 main@%shadow.mem.0.3_1))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                 (=> main@.preheader22_0
                     (= main@%_52_0 (> main@%.1.i.lcssa_2 9)))
                 (=> main@.preheader22_0
                     (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                 (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                 (=> main@.preheader22_0
                     (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                 (=> main@.lr.ph32.us.preheader_0
                     (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                 (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                     main@%or.cond56_0)
                 (=> main@.lr.ph32.us.preheader_0 a!7)
                 (=> main@.lr.ph32.us.preheader_0
                     (or (<= @a_2_0 0) (> main@%_55_0 0)))
                 (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                 (=> main@.lr.ph32.us.preheader_0 a!8)
                 (=> main@.lr.ph32.us.preheader_0
                     (or (<= @a_2_0 0) (> main@%_57_0 0)))
                 (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                 (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                 (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                 (=> main@_60_0 a!9)
                 (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                 (=> main@_60_0 (> @a_2_0 0))
                 (=> main@_60_0 a!10)
                 (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                 (=> main@_60_0 (> @a_2_0 0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     main@.lr.ph32.us.preheader_0)
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     main@.preheader22_0)
                 (=> main@.preheader_0
                     (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                         (and main@.preheader_0 main@_60_0)
                         |tuple(main@.preheader22_0, main@.preheader_0)|))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (not main@%_59_0))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (not main@%or.cond56_0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_0))
                 (=> (and main@.preheader_0 main@_60_0)
                     (= main@%shadow.mem.4.4_1 main@%sm9_0))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                 (=> (and main@.preheader_0 main@_60_0)
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                 true
                 (=> main@.preheader_0 a!11)
                 (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                 (=> main@.preheader_0 (> @a_1_0 0))
                 (=> main@.preheader_0 a!12)
                 (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                 (=> main@.preheader_0 (> @a_2_0 0))
                 (=> main@.preheader_0
                     (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                 (=> main@.lr.ph.preheader_0
                     (and main@.lr.ph.preheader_0 main@.preheader_0))
                 (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                     main@%or.cond1828_0)
                 (=> main@.lr.ph.preheader_0
                     (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                 (=> main@.lr.ph66_0
                     (and main@.lr.ph66_0 main@.lr.ph.preheader_0))
                 (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                     main@%or.cond2064_0)
                 (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                     (= main@%_77_0 2))
                 (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                     (= main@%.06.i2965_0 1))
                 (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                     (= main@%_77_1 main@%_77_0))
                 (=> (and main@.lr.ph66_0 main@.lr.ph.preheader_0)
                     (= main@%.06.i2965_1 main@%.06.i2965_0))
                 main@.lr.ph66_0)))
  (=> a!13
      (main@.lr.ph66 main@%_77_1
                     main@%.06.i2965_1
                     @a_1_0
                     main@%shadow.mem.0.3_2
                     @a_2_0
                     main@%shadow.mem.4.4_3)))))
(rule (let ((a!1 (= main@%_37_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_36_0 4))))
      (a!2 (= main@%_41_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.04.i40_0 4))))
      (a!3 (= main@%_47_0 (+ (+ @a_1_0 (* 0 40)) (* 8 4))))
      (a!4 (= main@%_49_0 (+ (+ @a_1_0 (* 0 40)) (* 9 4))))
      (a!5 (= main@%_64_0 (+ (+ @a_1_0 (* 0 40)) (* 9 4))))
      (a!6 (= main@%_65_0 (+ (+ @a_1_0 (* 0 40)) (* 8 4))))
      (a!7 (= main@%_55_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!8 (= main@%_57_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!9 (= main@%_61_0 (+ (+ @a_2_0 (* 0 40)) (* 9 4))))
      (a!10 (= main@%_62_0 (+ (+ @a_2_0 (* 0 40)) (* 8 4))))
      (a!11 (= main@%_67_0 (+ (+ @a_1_0 (* 0 40)) (* 1 4))))
      (a!12 (= main@%_69_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!13 (and (main@.lr.ph41 @a_1_0
                                @a_2_0
                                main@%shadow.mem.4.1_0
                                main@%_20_0
                                main@%.02.i43_0
                                main@%.01.i44_0
                                main@%_22_0
                                main@%shadow.mem.0.1_0
                                main@%.04.i40_0
                                main@%loop.bound_0
                                main@%loop.bound1_0)
                 true
                 (= main@%_36_0 (+ main@%.04.i40_0 (- 1)))
                 a!1
                 (or (<= @a_1_0 0) (> main@%_37_0 0))
                 (> @a_1_0 0)
                 (=> main@_40_0 (and main@_40_0 main@.lr.ph41_0))
                 (=> (and main@_40_0 main@.lr.ph41_0) main@%_39_0)
                 (=> main@_40_0 a!2)
                 (=> main@_40_0 (or (<= @a_1_0 0) (> main@%_41_0 0)))
                 (=> main@_40_0 (> @a_1_0 0))
                 (=> main@_40_0 (> @a_1_0 0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)| main@.lr.ph41_0)
                 (=> main@_42_0
                     (or (and main@_42_0 main@_40_0)
                         |tuple(main@.lr.ph41_0, main@_42_0)|))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)| (not main@%_39_0))
                 (=> (and main@_42_0 main@_40_0)
                     (= main@%shadow.mem.0.2_0 main@%sm7_0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                     (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                 (=> (and main@_42_0 main@_40_0)
                     (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                 (=> |tuple(main@.lr.ph41_0, main@_42_0)|
                     (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                 (=> main@_42_0 (= main@%_44_0 (> main@%_36_0 main@%.01.i44_0)))
                 (=> main@._crit_edge42_0 (and main@._crit_edge42_0 main@_42_0))
                 (=> (and main@._crit_edge42_0 main@_42_0) (not main@%_44_0))
                 (=> main@._crit_edge42_0 (= main@%_45_0 (+ main@%.02.i43_0 1)))
                 (=> main@._crit_edge42_0 (= main@%_46_0 (+ main@%.01.i44_0 1)))
                 (=> main@.preheader24_0
                     (and main@.preheader24_0 main@._crit_edge42_0))
                 (=> (and main@.preheader24_0 main@._crit_edge42_0)
                     (not main@%_20_0))
                 (=> main@.preheader23.preheader_0
                     (and main@.preheader23.preheader_0 main@.preheader24_0))
                 (=> (and main@.preheader23.preheader_0 main@.preheader24_0)
                     main@%_22_0)
                 (=> main@.preheader23.preheader_0
                     (= main@%.not_0 (= main@%.01.i44_0 8)))
                 (=> main@.lr.ph35.preheader_0
                     (and main@.lr.ph35.preheader_0
                          main@.preheader23.preheader_0))
                 (=> (and main@.lr.ph35.preheader_0
                          main@.preheader23.preheader_0)
                     (not main@%.not_0))
                 (=> main@.lr.ph35.preheader_0 a!3)
                 (=> main@.lr.ph35.preheader_0
                     (or (<= @a_1_0 0) (> main@%_47_0 0)))
                 (=> main@.lr.ph35.preheader_0 (> @a_1_0 0))
                 (=> main@.lr.ph35.preheader_0 a!4)
                 (=> main@.lr.ph35.preheader_0
                     (or (<= @a_1_0 0) (> main@%_49_0 0)))
                 (=> main@.lr.ph35.preheader_0 (> @a_1_0 0))
                 (=> main@_63_0 (and main@_63_0 main@.lr.ph35.preheader_0))
                 (=> (and main@_63_0 main@.lr.ph35.preheader_0) main@%_51_0)
                 (=> main@_63_0 a!5)
                 (=> main@_63_0 (or (<= @a_1_0 0) (> main@%_64_0 0)))
                 (=> main@_63_0 (> @a_1_0 0))
                 (=> main@_63_0 a!6)
                 (=> main@_63_0 (or (<= @a_1_0 0) (> main@%_65_0 0)))
                 (=> main@_63_0 (> @a_1_0 0))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     main@.lr.ph35.preheader_0)
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     main@.preheader23.preheader_0)
                 (=> main@._crit_edge36_0
                     (or |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                         (and main@._crit_edge36_0 main@_63_0)
                         |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (not main@%_51_0))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     main@%.not_0)
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_0 main@%shadow.mem.0.2_2))
                 (=> (and main@._crit_edge36_0 main@_63_0)
                     (= main@%shadow.mem.0.4_1 main@%sm11_0))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_2 main@%shadow.mem.0.2_2))
                 (=> |tuple(main@.lr.ph35.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_0))
                 (=> (and main@._crit_edge36_0 main@_63_0)
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_1))
                 (=> |tuple(main@.preheader23.preheader_0, main@._crit_edge36_0)|
                     (= main@%shadow.mem.0.4_3 main@%shadow.mem.0.4_2))
                 (=> main@._crit_edge36_0 (= main@%_66_0 (+ main@%.01.i44_0 2)))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     main@.preheader24_0)
                 (=> main@.preheader22_0
                     (or (and main@.preheader22_0 main@._crit_edge36_0)
                         |tuple(main@.preheader24_0, main@.preheader22_0)|))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (not main@%_22_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.4_3))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%.1.i.lcssa_0 main@%_66_0))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.2_2))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%.1.i.lcssa_1 main@%_46_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%shadow.mem.0.3_2 main@%shadow.mem.0.3_0))
                 (=> (and main@.preheader22_0 main@._crit_edge36_0)
                     (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_0))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%shadow.mem.0.3_2 main@%shadow.mem.0.3_1))
                 (=> |tuple(main@.preheader24_0, main@.preheader22_0)|
                     (= main@%.1.i.lcssa_2 main@%.1.i.lcssa_1))
                 (=> main@.preheader22_0
                     (= main@%_52_0 (> main@%.1.i.lcssa_2 9)))
                 (=> main@.preheader22_0
                     (= main@%_53_0 (ite main@%_52_0 main@%_20_0 false)))
                 (=> main@.preheader22_0 (= main@%_54_0 (< main@%.02.i43_0 8)))
                 (=> main@.preheader22_0
                     (= main@%or.cond56_0 (ite main@%_53_0 main@%_54_0 false)))
                 (=> main@.lr.ph32.us.preheader_0
                     (and main@.lr.ph32.us.preheader_0 main@.preheader22_0))
                 (=> (and main@.lr.ph32.us.preheader_0 main@.preheader22_0)
                     main@%or.cond56_0)
                 (=> main@.lr.ph32.us.preheader_0 a!7)
                 (=> main@.lr.ph32.us.preheader_0
                     (or (<= @a_2_0 0) (> main@%_55_0 0)))
                 (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                 (=> main@.lr.ph32.us.preheader_0 a!8)
                 (=> main@.lr.ph32.us.preheader_0
                     (or (<= @a_2_0 0) (> main@%_57_0 0)))
                 (=> main@.lr.ph32.us.preheader_0 (> @a_2_0 0))
                 (=> main@_60_0 (and main@_60_0 main@.lr.ph32.us.preheader_0))
                 (=> (and main@_60_0 main@.lr.ph32.us.preheader_0) main@%_59_0)
                 (=> main@_60_0 a!9)
                 (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_61_0 0)))
                 (=> main@_60_0 (> @a_2_0 0))
                 (=> main@_60_0 a!10)
                 (=> main@_60_0 (or (<= @a_2_0 0) (> main@%_62_0 0)))
                 (=> main@_60_0 (> @a_2_0 0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     main@.lr.ph32.us.preheader_0)
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     main@.preheader22_0)
                 (=> main@.preheader_0
                     (or |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                         (and main@.preheader_0 main@_60_0)
                         |tuple(main@.preheader22_0, main@.preheader_0)|))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (not main@%_59_0))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (not main@%or.cond56_0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.1_0))
                 (=> (and main@.preheader_0 main@_60_0)
                     (= main@%shadow.mem.4.4_1 main@%sm9_0))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_2 main@%shadow.mem.4.1_0))
                 (=> |tuple(main@.lr.ph32.us.preheader_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_0))
                 (=> (and main@.preheader_0 main@_60_0)
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_1))
                 (=> |tuple(main@.preheader22_0, main@.preheader_0)|
                     (= main@%shadow.mem.4.4_3 main@%shadow.mem.4.4_2))
                 true
                 (=> main@.preheader_0 a!11)
                 (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_67_0 0)))
                 (=> main@.preheader_0 (> @a_1_0 0))
                 (=> main@.preheader_0 a!12)
                 (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_69_0 0)))
                 (=> main@.preheader_0 (> @a_2_0 0))
                 (=> main@.preheader_0
                     (= main@%or.cond1828_0 (or main@%_71_0 main@%_73_0)))
                 (=> main@.lr.ph.preheader_0
                     (and main@.lr.ph.preheader_0 main@.preheader_0))
                 (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                     main@%or.cond1828_0)
                 (=> main@.lr.ph.preheader_0
                     (= main@%or.cond2064_0 (or main@%_74_0 main@%_76_0)))
                 (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                     main@.lr.ph.preheader_0)
                 (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                     main@.preheader_0)
                 (=> main@verifier.error_0
                     (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                         |tuple(main@.preheader_0, main@verifier.error_0)|))
                 (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                     (not main@%or.cond2064_0))
                 (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                     (not main@%or.cond1828_0))
                 (=> main@verifier.error.split_0
                     (and main@verifier.error.split_0 main@verifier.error_0))
                 main@verifier.error.split_0)))
  (=> a!13 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph66 main@%_77_0
                               main@%.06.i2965_0
                               @a_1_0
                               main@%shadow.mem.0.3_0
                               @a_2_0
                               main@%shadow.mem.4.4_0)
                true
                (= main@%_78_0 (< main@%.06.i2965_0 9))
                main@%_78_0
                (= main@%_79_0 (+ @a_1_0 (* 0 40) (* main@%_77_0 4)))
                (or (<= @a_1_0 0) (> main@%_79_0 0))
                (> @a_1_0 0)
                (= main@%_81_0 (+ @a_2_0 (* 0 40) (* main@%_77_0 4)))
                (or (<= @a_2_0 0) (> main@%_81_0 0))
                (> @a_2_0 0)
                (= main@%or.cond18_0 (or main@%_83_0 main@%_85_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph66_0))
                (=> (and main@.lr.ph_0 main@.lr.ph66_0) main@%or.cond18_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond20_0 (or main@%_86_0 main@%_88_0)))
                (=> main@.lr.ph_0 (= main@%_89_0 (+ main@%_77_0 1)))
                (=> main@.lr.ph66_1 (and main@.lr.ph66_1 main@.lr.ph_0))
                (=> (and main@.lr.ph66_1 main@.lr.ph_0) main@%or.cond20_0)
                (=> (and main@.lr.ph66_1 main@.lr.ph_0)
                    (= main@%_77_1 main@%_89_0))
                (=> (and main@.lr.ph66_1 main@.lr.ph_0)
                    (= main@%.06.i2965_1 main@%_77_0))
                (=> (and main@.lr.ph66_1 main@.lr.ph_0)
                    (= main@%_77_2 main@%_77_1))
                (=> (and main@.lr.ph66_1 main@.lr.ph_0)
                    (= main@%.06.i2965_2 main@%.06.i2965_1))
                main@.lr.ph66_1)))
  (=> a!1
      (main@.lr.ph66 main@%_77_2
                     main@%.06.i2965_2
                     @a_1_0
                     main@%shadow.mem.0.3_0
                     @a_2_0
                     main@%shadow.mem.4.4_0))))
(rule (let ((a!1 (and (main@.lr.ph66 main@%_77_0
                               main@%.06.i2965_0
                               @a_1_0
                               main@%shadow.mem.0.3_0
                               @a_2_0
                               main@%shadow.mem.4.4_0)
                true
                (= main@%_78_0 (< main@%.06.i2965_0 9))
                main@%_78_0
                (= main@%_79_0 (+ @a_1_0 (* 0 40) (* main@%_77_0 4)))
                (or (<= @a_1_0 0) (> main@%_79_0 0))
                (> @a_1_0 0)
                (= main@%_81_0 (+ @a_2_0 (* 0 40) (* main@%_77_0 4)))
                (or (<= @a_2_0 0) (> main@%_81_0 0))
                (> @a_2_0 0)
                (= main@%or.cond18_0 (or main@%_83_0 main@%_85_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph66_0))
                (=> (and main@.lr.ph_0 main@.lr.ph66_0) main@%or.cond18_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond20_0 (or main@%_86_0 main@%_88_0)))
                (=> main@.lr.ph_0 (= main@%_89_0 (+ main@%_77_0 1)))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)| main@.lr.ph_0)
                (=> |tuple(main@.lr.ph66_0, main@verifier.error_0)|
                    main@.lr.ph66_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph_0, main@verifier.error_0)|
                        |tuple(main@.lr.ph66_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)|
                    (not main@%or.cond20_0))
                (=> |tuple(main@.lr.ph66_0, main@verifier.error_0)|
                    (not main@%or.cond18_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

