(set-info :original "./results/chc/bytecode/barthe/unaligned/bubblesort.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int (Array Int Int) Int Int (Array Int Int) ))
(declare-rel main@_3 (Int Int Int (Array Int Int) Int Int Int (Array Int Int) ))
(declare-rel main@.lr.ph28.preheader (Int Int Int (Array Int Int) Int Int (Array Int Int) Bool ))
(declare-rel main@.lr.ph28 (Int Int Int (Array Int Int) Int Int Bool (Array Int Int) Int ))
(declare-rel main@.lr.ph25.preheader (Int (Array Int Int) Int Int Int (Array Int Int) Bool ))
(declare-rel main@.lr.ph25 (Int (Array Int Int) Int Int Int Bool (Array Int Int) Int ))
(declare-rel main@.lr.ph35 (Int Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_67_0 Bool )
(declare-var main@%_69_0 Bool )
(declare-var main@%or.cond16_0 Bool )
(declare-var main@%_59_0 Bool )
(declare-var main@%_60_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@%_64_0 Bool )
(declare-var main@%_66_0 Bool )
(declare-var main@%or.cond14_0 Bool )
(declare-var main@%_45_0 Bool )
(declare-var main@%_47_0 Bool )
(declare-var main@%or.cond1633_0 Bool )
(declare-var main@%.03.i2234_2 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%_42_0 Bool )
(declare-var main@%_44_0 Bool )
(declare-var main@%or.cond1421_0 Bool )
(declare-var main@%_57_0 Bool )
(declare-var main@%_54_0 Int )
(declare-var main@%_50_0 Int )
(declare-var main@%_52_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_36_2 Bool )
(declare-var main@%_33_0 Bool )
(declare-var main@%_30_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_22_2 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%or.cond_0 Bool )
(declare-var main@%_17_3 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
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
(declare-var main@%.0.i31_0 Int )
(declare-var main@%.0.i31_1 Int )
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
(declare-var main@%.0.i31_2 Int )
(declare-var main@.lr.ph28.preheader_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%_22_0 Bool )
(declare-var main@%.01.i3037_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%_22_1 Bool )
(declare-var main@%.01.i3037_1 Int )
(declare-var main@.lr.ph28_0 Bool )
(declare-var main@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var main@%.02.i27_0 Int )
(declare-var main@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var main@%.02.i27_1 Int )
(declare-var main@%_25_0 Int )
(declare-var main@_29_0 Bool )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@_31_0 Bool )
(declare-var |tuple(main@.lr.ph28_0, main@_31_0)| Bool )
(declare-var main@%shadow.mem.0.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_2 (Array Int Int) )
(declare-var main@._crit_edge29_0 Bool )
(declare-var main@.preheader19_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%.01.i3037_2 Int )
(declare-var main@.lr.ph28_1 Bool )
(declare-var main@%shadow.mem.0.1_2 (Array Int Int) )
(declare-var main@%.02.i27_2 Int )
(declare-var main@.lr.ph25.preheader.preheader_0 Bool )
(declare-var |tuple(main@.preheader19_0, main@.lr.ph25.preheader.preheader_0)| Bool )
(declare-var |tuple(main@._crit_edge29_0, main@.lr.ph25.preheader.preheader_0)| Bool )
(declare-var main@.lr.ph25.preheader_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%_36_0 Bool )
(declare-var main@%.04.i2636_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%_36_1 Bool )
(declare-var main@%.04.i2636_1 Int )
(declare-var main@.lr.ph25_0 Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%.05.i24_0 Int )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%.05.i24_1 Int )
(declare-var main@%_49_0 Int )
(declare-var main@_53_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@_55_0 Bool )
(declare-var |tuple(main@.lr.ph25_0, main@_55_0)| Bool )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@.preheader17_0 Bool )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%.04.i2636_2 Int )
(declare-var main@.lr.ph25_1 Bool )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@%.05.i24_2 Int )
(declare-var main@.preheader_0 Bool )
(declare-var |tuple(main@.preheader17_0, main@.preheader_0)| Bool )
(declare-var |tuple(main@._crit_edge_0, main@.preheader_0)| Bool )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph35_0 Bool )
(declare-var main@%_58_0 Int )
(declare-var main@%.03.i2234_0 Int )
(declare-var main@%_58_1 Int )
(declare-var main@%.03.i2234_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.preheader_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_70_0 Int )
(declare-var main@.lr.ph35_1 Bool )
(declare-var main@%_58_2 Int )
(declare-var |tuple(main@.lr.ph_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@.lr.ph35_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm8_0 main@%sm9_0))
(rule (=> (and (main@entry main@%sm8_0 main@%sm9_0)
         true
         (= main@%sm_0 main@%sm8_0)
         (= main@%sm3_0 main@%sm9_0)
         (= main@%_0_0 (= main@%loop.bound_0 8))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 8))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%sm_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%sm3_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
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
                     main@%sm3_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%sm_0)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%sm3_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%sm_0)
         true
         (=> main@_3_0 (and main@_3_0 main@empty.loop_0))
         (=> (and main@_3_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_3_0 main@empty.loop_0) (= main@%.0.i31_0 1))
         (=> (and main@_3_0 main@empty.loop_0)
             (= main@%.0.i31_1 main@%.0.i31_0))
         main@_3_0)
    (main@_3 @a_1_0
             @a_2_0
             main@%loop.bound_0
             main@%sm3_0
             main@%loop.bound1_0
             main@%.0.i31_1
             main@%loop.bound2_0
             main@%sm_0)))
(rule (let ((a!1 (and (main@_3 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%sm3_0
                         main@%loop.bound1_0
                         main@%.0.i31_0
                         main@%loop.bound2_0
                         main@%sm_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i31_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i31_0 4)))
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
                (=> main@_16_0 (= main@%_18_0 (+ main@%.0.i31_0 1)))
                (=> main@_16_0
                    (= main@%_19_0 (< main@%.0.i31_0 main@%loop.bound2_0)))
                (=> main@_3_1 (and main@_3_1 main@_16_0))
                (=> (and main@_3_1 main@_16_0) main@%_19_0)
                (=> (and main@_3_1 main@_16_0) (= main@%.0.i31_1 main@%_18_0))
                (=> (and main@_3_1 main@_16_0)
                    (= main@%.0.i31_2 main@%.0.i31_1))
                main@_3_1)))
  (=> a!1
      (main@_3 @a_1_0
               @a_2_0
               main@%loop.bound_0
               main@%sm3_0
               main@%loop.bound1_0
               main@%.0.i31_2
               main@%loop.bound2_0
               main@%sm_0))))
(rule (let ((a!1 (and (main@_3 @a_1_0
                         @a_2_0
                         main@%loop.bound_0
                         main@%sm3_0
                         main@%loop.bound1_0
                         main@%.0.i31_0
                         main@%loop.bound2_0
                         main@%sm_0)
                true
                (= main@%_4_0 (+ @a_1_0 (* 0 40) (* main@%.0.i31_0 4)))
                (or (<= @a_1_0 0) (> main@%_4_0 0))
                (> @a_1_0 0)
                (= main@%_6_0 (+ @a_2_0 (* 0 40) (* main@%.0.i31_0 4)))
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
                (=> main@_16_0 (= main@%_18_0 (+ main@%.0.i31_0 1)))
                (=> main@_16_0
                    (= main@%_19_0 (< main@%.0.i31_0 main@%loop.bound2_0)))
                (=> main@.lr.ph28.preheader_0
                    (and main@.lr.ph28.preheader_0 main@_16_0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (not main@%_19_0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%_22_0 true))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%.01.i3037_0 0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%_22_1 main@%_22_0))
                (=> (and main@.lr.ph28.preheader_0 main@_16_0)
                    (= main@%.01.i3037_1 main@%.01.i3037_0))
                main@.lr.ph28.preheader_0)))
  (=> a!1
      (main@.lr.ph28.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%sm3_0
        main@%.01.i3037_1
        main@%loop.bound1_0
        main@%shadow.mem.0.0_1
        main@%_22_1))))
(rule (let ((a!1 (and (main@.lr.ph28.preheader
                  @a_1_0
                  @a_2_0
                  main@%loop.bound_0
                  main@%sm3_0
                  main@%.01.i3037_0
                  main@%loop.bound1_0
                  main@%shadow.mem.0.0_0
                  main@%_22_0)
                true
                (= main@%_23_0 (+ @a_1_0 (* 0 40) (* 9 4)))
                (or (<= @a_1_0 0) (> main@%_23_0 0))
                (> @a_1_0 0)
                (=> main@.lr.ph28_0
                    (and main@.lr.ph28_0 main@.lr.ph28.preheader_0))
                (=> (and main@.lr.ph28_0 main@.lr.ph28.preheader_0)
                    (= main@%shadow.mem.0.1_0 main@%shadow.mem.0.0_0))
                (=> (and main@.lr.ph28_0 main@.lr.ph28.preheader_0)
                    (= main@%.02.i27_0 9))
                (=> (and main@.lr.ph28_0 main@.lr.ph28.preheader_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.lr.ph28_0 main@.lr.ph28.preheader_0)
                    (= main@%.02.i27_1 main@%.02.i27_0))
                main@.lr.ph28_0)))
  (=> a!1
      (main@.lr.ph28 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%.01.i3037_0
                     main@%loop.bound1_0
                     main@%_22_0
                     main@%shadow.mem.0.1_1
                     main@%.02.i27_1))))
(rule (let ((a!1 (= main@%_26_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_25_0 4))))
      (a!2 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.02.i27_0 4)))))
(let ((a!3 (and (main@.lr.ph28 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%sm3_0
                               main@%.01.i3037_0
                               main@%loop.bound1_0
                               main@%_22_0
                               main@%shadow.mem.0.1_0
                               main@%.02.i27_0)
                true
                (= main@%_25_0 (+ main@%.02.i27_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_26_0 0))
                (> @a_1_0 0)
                (=> main@_29_0 (and main@_29_0 main@.lr.ph28_0))
                (=> (and main@_29_0 main@.lr.ph28_0) main@%_28_0)
                (=> main@_29_0 a!2)
                (=> main@_29_0 (or (<= @a_1_0 0) (> main@%_30_0 0)))
                (=> main@_29_0 (> @a_1_0 0))
                (=> main@_29_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| main@.lr.ph28_0)
                (=> main@_31_0
                    (or (and main@_31_0 main@_29_0)
                        |tuple(main@.lr.ph28_0, main@_31_0)|))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| (not main@%_28_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_31_0
                    (= main@%_33_0 (> main@%_25_0 main@%.01.i3037_0)))
                (=> main@._crit_edge29_0 (and main@._crit_edge29_0 main@_31_0))
                (=> (and main@._crit_edge29_0 main@_31_0) (not main@%_33_0))
                (=> main@.preheader19_0
                    (and main@.preheader19_0 main@._crit_edge29_0))
                (=> (and main@.preheader19_0 main@._crit_edge29_0) main@%_22_0)
                (=> main@.preheader19_0 (= main@%_20_0 (+ main@%.01.i3037_0 1)))
                (=> main@.preheader19_0
                    (= main@%_21_0 (< main@%.01.i3037_0 main@%loop.bound1_0)))
                (=> main@.lr.ph28.preheader_0
                    (and main@.lr.ph28.preheader_0 main@.preheader19_0))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    main@%_21_0)
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.2_2))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%_22_1 main@%_21_0))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%.01.i3037_1 main@%_20_0))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%_22_2 main@%_22_1))
                (=> (and main@.lr.ph28.preheader_0 main@.preheader19_0)
                    (= main@%.01.i3037_2 main@%.01.i3037_1))
                main@.lr.ph28.preheader_0)))
  (=> a!3
      (main@.lr.ph28.preheader
        @a_1_0
        @a_2_0
        main@%loop.bound_0
        main@%sm3_0
        main@%.01.i3037_2
        main@%loop.bound1_0
        main@%shadow.mem.0.0_1
        main@%_22_2)))))
(rule (let ((a!1 (= main@%_26_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_25_0 4))))
      (a!2 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.02.i27_0 4)))))
(let ((a!3 (and (main@.lr.ph28 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%sm3_0
                               main@%.01.i3037_0
                               main@%loop.bound1_0
                               main@%_22_0
                               main@%shadow.mem.0.1_0
                               main@%.02.i27_0)
                true
                (= main@%_25_0 (+ main@%.02.i27_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_26_0 0))
                (> @a_1_0 0)
                (=> main@_29_0 (and main@_29_0 main@.lr.ph28_0))
                (=> (and main@_29_0 main@.lr.ph28_0) main@%_28_0)
                (=> main@_29_0 a!2)
                (=> main@_29_0 (or (<= @a_1_0 0) (> main@%_30_0 0)))
                (=> main@_29_0 (> @a_1_0 0))
                (=> main@_29_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| main@.lr.ph28_0)
                (=> main@_31_0
                    (or (and main@_31_0 main@_29_0)
                        |tuple(main@.lr.ph28_0, main@_31_0)|))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| (not main@%_28_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_31_0
                    (= main@%_33_0 (> main@%_25_0 main@%.01.i3037_0)))
                (=> main@.lr.ph28_1 (and main@.lr.ph28_1 main@_31_0))
                (=> (and main@.lr.ph28_1 main@_31_0) main@%_33_0)
                (=> (and main@.lr.ph28_1 main@_31_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.2_2))
                (=> (and main@.lr.ph28_1 main@_31_0)
                    (= main@%.02.i27_1 main@%_25_0))
                (=> (and main@.lr.ph28_1 main@_31_0)
                    (= main@%shadow.mem.0.1_2 main@%shadow.mem.0.1_1))
                (=> (and main@.lr.ph28_1 main@_31_0)
                    (= main@%.02.i27_2 main@%.02.i27_1))
                main@.lr.ph28_1)))
  (=> a!3
      (main@.lr.ph28 @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%sm3_0
                     main@%.01.i3037_0
                     main@%loop.bound1_0
                     main@%_22_0
                     main@%shadow.mem.0.1_2
                     main@%.02.i27_2)))))
(rule (let ((a!1 (= main@%_26_0 (+ (+ @a_1_0 (* 0 40)) (* main@%_25_0 4))))
      (a!2 (= main@%_30_0 (+ (+ @a_1_0 (* 0 40)) (* main@%.02.i27_0 4)))))
(let ((a!3 (and (main@.lr.ph28 @a_1_0
                               @a_2_0
                               main@%loop.bound_0
                               main@%sm3_0
                               main@%.01.i3037_0
                               main@%loop.bound1_0
                               main@%_22_0
                               main@%shadow.mem.0.1_0
                               main@%.02.i27_0)
                true
                (= main@%_25_0 (+ main@%.02.i27_0 (- 1)))
                a!1
                (or (<= @a_1_0 0) (> main@%_26_0 0))
                (> @a_1_0 0)
                (=> main@_29_0 (and main@_29_0 main@.lr.ph28_0))
                (=> (and main@_29_0 main@.lr.ph28_0) main@%_28_0)
                (=> main@_29_0 a!2)
                (=> main@_29_0 (or (<= @a_1_0 0) (> main@%_30_0 0)))
                (=> main@_29_0 (> @a_1_0 0))
                (=> main@_29_0 (> @a_1_0 0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| main@.lr.ph28_0)
                (=> main@_31_0
                    (or (and main@_31_0 main@_29_0)
                        |tuple(main@.lr.ph28_0, main@_31_0)|))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)| (not main@%_28_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_0 main@%sm5_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.1_0))
                (=> (and main@_31_0 main@_29_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_0))
                (=> |tuple(main@.lr.ph28_0, main@_31_0)|
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> main@_31_0
                    (= main@%_33_0 (> main@%_25_0 main@%.01.i3037_0)))
                (=> main@._crit_edge29_0 (and main@._crit_edge29_0 main@_31_0))
                (=> (and main@._crit_edge29_0 main@_31_0) (not main@%_33_0))
                (=> main@.preheader19_0
                    (and main@.preheader19_0 main@._crit_edge29_0))
                (=> (and main@.preheader19_0 main@._crit_edge29_0) main@%_22_0)
                (=> main@.preheader19_0 (= main@%_20_0 (+ main@%.01.i3037_0 1)))
                (=> main@.preheader19_0
                    (= main@%_21_0 (< main@%.01.i3037_0 main@%loop.bound1_0)))
                (=> |tuple(main@.preheader19_0, main@.lr.ph25.preheader.preheader_0)|
                    main@.preheader19_0)
                (=> |tuple(main@._crit_edge29_0, main@.lr.ph25.preheader.preheader_0)|
                    main@._crit_edge29_0)
                (=> main@.lr.ph25.preheader.preheader_0
                    (or |tuple(main@.preheader19_0, main@.lr.ph25.preheader.preheader_0)|
                        |tuple(main@._crit_edge29_0, main@.lr.ph25.preheader.preheader_0)|))
                (=> |tuple(main@.preheader19_0, main@.lr.ph25.preheader.preheader_0)|
                    (not main@%_21_0))
                (=> |tuple(main@._crit_edge29_0, main@.lr.ph25.preheader.preheader_0)|
                    (not main@%_22_0))
                (=> main@.lr.ph25.preheader_0
                    (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%shadow.mem.4.0_0 main@%sm3_0))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%_36_0 true))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%.04.i2636_0 0))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%_36_1 main@%_36_0))
                (=> (and main@.lr.ph25.preheader_0
                         main@.lr.ph25.preheader.preheader_0)
                    (= main@%.04.i2636_1 main@%.04.i2636_0))
                main@.lr.ph25.preheader_0)))
  (=> a!3
      (main@.lr.ph25.preheader
        @a_1_0
        main@%shadow.mem.0.2_2
        @a_2_0
        main@%.04.i2636_1
        main@%loop.bound_0
        main@%shadow.mem.4.0_1
        main@%_36_1)))))
(rule (let ((a!1 (and (main@.lr.ph25.preheader
                  @a_1_0
                  main@%shadow.mem.0.2_0
                  @a_2_0
                  main@%.04.i2636_0
                  main@%loop.bound_0
                  main@%shadow.mem.4.0_0
                  main@%_36_0)
                true
                (= main@%_37_0 (+ @a_2_0 (* 0 40) (* 9 4)))
                (or (<= @a_2_0 0) (> main@%_37_0 0))
                (> @a_2_0 0)
                (=> main@.lr.ph25_0
                    (and main@.lr.ph25_0 main@.lr.ph25.preheader_0))
                (=> (and main@.lr.ph25_0 main@.lr.ph25.preheader_0)
                    (= main@%shadow.mem.4.1_0 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph25_0 main@.lr.ph25.preheader_0)
                    (= main@%.05.i24_0 9))
                (=> (and main@.lr.ph25_0 main@.lr.ph25.preheader_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@.lr.ph25_0 main@.lr.ph25.preheader_0)
                    (= main@%.05.i24_1 main@%.05.i24_0))
                main@.lr.ph25_0)))
  (=> a!1
      (main@.lr.ph25 @a_1_0
                     main@%shadow.mem.0.2_0
                     @a_2_0
                     main@%.04.i2636_0
                     main@%loop.bound_0
                     main@%_36_0
                     main@%shadow.mem.4.1_1
                     main@%.05.i24_1))))
(rule (let ((a!1 (= main@%_50_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_49_0 4))))
      (a!2 (= main@%_54_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i24_0 4)))))
(let ((a!3 (and (main@.lr.ph25 @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%.04.i2636_0
                               main@%loop.bound_0
                               main@%_36_0
                               main@%shadow.mem.4.1_0
                               main@%.05.i24_0)
                true
                (= main@%_49_0 (+ main@%.05.i24_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_50_0 0))
                (> @a_2_0 0)
                (=> main@_53_0 (and main@_53_0 main@.lr.ph25_0))
                (=> (and main@_53_0 main@.lr.ph25_0) main@%_52_0)
                (=> main@_53_0 a!2)
                (=> main@_53_0 (or (<= @a_2_0 0) (> main@%_54_0 0)))
                (=> main@_53_0 (> @a_2_0 0))
                (=> main@_53_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| main@.lr.ph25_0)
                (=> main@_55_0
                    (or (and main@_55_0 main@_53_0)
                        |tuple(main@.lr.ph25_0, main@_55_0)|))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| (not main@%_52_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@_55_0
                    (= main@%_57_0 (> main@%_49_0 main@%.04.i2636_0)))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@_55_0))
                (=> (and main@._crit_edge_0 main@_55_0) (not main@%_57_0))
                (=> main@.preheader17_0
                    (and main@.preheader17_0 main@._crit_edge_0))
                (=> (and main@.preheader17_0 main@._crit_edge_0) main@%_36_0)
                (=> main@.preheader17_0 (= main@%_34_0 (+ main@%.04.i2636_0 1)))
                (=> main@.preheader17_0
                    (= main@%_35_0 (< main@%.04.i2636_0 main@%loop.bound_0)))
                (=> main@.lr.ph25.preheader_0
                    (and main@.lr.ph25.preheader_0 main@.preheader17_0))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    main@%_35_0)
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%shadow.mem.4.0_0 main@%shadow.mem.4.2_2))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%_36_1 main@%_35_0))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%.04.i2636_1 main@%_34_0))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%_36_2 main@%_36_1))
                (=> (and main@.lr.ph25.preheader_0 main@.preheader17_0)
                    (= main@%.04.i2636_2 main@%.04.i2636_1))
                main@.lr.ph25.preheader_0)))
  (=> a!3
      (main@.lr.ph25.preheader
        @a_1_0
        main@%shadow.mem.0.2_0
        @a_2_0
        main@%.04.i2636_2
        main@%loop.bound_0
        main@%shadow.mem.4.0_1
        main@%_36_2)))))
(rule (let ((a!1 (= main@%_50_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_49_0 4))))
      (a!2 (= main@%_54_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i24_0 4)))))
(let ((a!3 (and (main@.lr.ph25 @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%.04.i2636_0
                               main@%loop.bound_0
                               main@%_36_0
                               main@%shadow.mem.4.1_0
                               main@%.05.i24_0)
                true
                (= main@%_49_0 (+ main@%.05.i24_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_50_0 0))
                (> @a_2_0 0)
                (=> main@_53_0 (and main@_53_0 main@.lr.ph25_0))
                (=> (and main@_53_0 main@.lr.ph25_0) main@%_52_0)
                (=> main@_53_0 a!2)
                (=> main@_53_0 (or (<= @a_2_0 0) (> main@%_54_0 0)))
                (=> main@_53_0 (> @a_2_0 0))
                (=> main@_53_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| main@.lr.ph25_0)
                (=> main@_55_0
                    (or (and main@_55_0 main@_53_0)
                        |tuple(main@.lr.ph25_0, main@_55_0)|))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| (not main@%_52_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@_55_0
                    (= main@%_57_0 (> main@%_49_0 main@%.04.i2636_0)))
                (=> main@.lr.ph25_1 (and main@.lr.ph25_1 main@_55_0))
                (=> (and main@.lr.ph25_1 main@_55_0) main@%_57_0)
                (=> (and main@.lr.ph25_1 main@_55_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.2_2))
                (=> (and main@.lr.ph25_1 main@_55_0)
                    (= main@%.05.i24_1 main@%_49_0))
                (=> (and main@.lr.ph25_1 main@_55_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> (and main@.lr.ph25_1 main@_55_0)
                    (= main@%.05.i24_2 main@%.05.i24_1))
                main@.lr.ph25_1)))
  (=> a!3
      (main@.lr.ph25 @a_1_0
                     main@%shadow.mem.0.2_0
                     @a_2_0
                     main@%.04.i2636_0
                     main@%loop.bound_0
                     main@%_36_0
                     main@%shadow.mem.4.1_2
                     main@%.05.i24_2)))))
(rule (let ((a!1 (= main@%_50_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_49_0 4))))
      (a!2 (= main@%_54_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i24_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_38_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_40_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph25 @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%.04.i2636_0
                               main@%loop.bound_0
                               main@%_36_0
                               main@%shadow.mem.4.1_0
                               main@%.05.i24_0)
                true
                (= main@%_49_0 (+ main@%.05.i24_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_50_0 0))
                (> @a_2_0 0)
                (=> main@_53_0 (and main@_53_0 main@.lr.ph25_0))
                (=> (and main@_53_0 main@.lr.ph25_0) main@%_52_0)
                (=> main@_53_0 a!2)
                (=> main@_53_0 (or (<= @a_2_0 0) (> main@%_54_0 0)))
                (=> main@_53_0 (> @a_2_0 0))
                (=> main@_53_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| main@.lr.ph25_0)
                (=> main@_55_0
                    (or (and main@_55_0 main@_53_0)
                        |tuple(main@.lr.ph25_0, main@_55_0)|))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| (not main@%_52_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@_55_0
                    (= main@%_57_0 (> main@%_49_0 main@%.04.i2636_0)))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@_55_0))
                (=> (and main@._crit_edge_0 main@_55_0) (not main@%_57_0))
                (=> main@.preheader17_0
                    (and main@.preheader17_0 main@._crit_edge_0))
                (=> (and main@.preheader17_0 main@._crit_edge_0) main@%_36_0)
                (=> main@.preheader17_0 (= main@%_34_0 (+ main@%.04.i2636_0 1)))
                (=> main@.preheader17_0
                    (= main@%_35_0 (< main@%.04.i2636_0 main@%loop.bound_0)))
                (=> |tuple(main@.preheader17_0, main@.preheader_0)|
                    main@.preheader17_0)
                (=> |tuple(main@._crit_edge_0, main@.preheader_0)|
                    main@._crit_edge_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader17_0, main@.preheader_0)|
                        |tuple(main@._crit_edge_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader17_0, main@.preheader_0)|
                    (not main@%_35_0))
                (=> |tuple(main@._crit_edge_0, main@.preheader_0)|
                    (not main@%_36_0))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_38_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_40_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1421_0 (or main@%_42_0 main@%_44_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1421_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond1633_0 (or main@%_45_0 main@%_47_0)))
                (=> main@.lr.ph35_0
                    (and main@.lr.ph35_0 main@.lr.ph.preheader_0))
                (=> (and main@.lr.ph35_0 main@.lr.ph.preheader_0)
                    main@%or.cond1633_0)
                (=> (and main@.lr.ph35_0 main@.lr.ph.preheader_0)
                    (= main@%_58_0 2))
                (=> (and main@.lr.ph35_0 main@.lr.ph.preheader_0)
                    (= main@%.03.i2234_0 1))
                (=> (and main@.lr.ph35_0 main@.lr.ph.preheader_0)
                    (= main@%_58_1 main@%_58_0))
                (=> (and main@.lr.ph35_0 main@.lr.ph.preheader_0)
                    (= main@%.03.i2234_1 main@%.03.i2234_0))
                main@.lr.ph35_0)))
  (=> a!5
      (main@.lr.ph35 main@%_58_1
                     main@%.03.i2234_1
                     @a_1_0
                     main@%shadow.mem.0.2_0
                     @a_2_0
                     main@%shadow.mem.4.2_2)))))
(rule (let ((a!1 (= main@%_50_0 (+ (+ @a_2_0 (* 0 40)) (* main@%_49_0 4))))
      (a!2 (= main@%_54_0 (+ (+ @a_2_0 (* 0 40)) (* main@%.05.i24_0 4))))
      (a!3 (=> main@.preheader_0 (= main@%_38_0 (+ @a_1_0 (* 0 40) (* 1 4)))))
      (a!4 (= main@%_40_0 (+ (+ @a_2_0 (* 0 40)) (* 1 4)))))
(let ((a!5 (and (main@.lr.ph25 @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%.04.i2636_0
                               main@%loop.bound_0
                               main@%_36_0
                               main@%shadow.mem.4.1_0
                               main@%.05.i24_0)
                true
                (= main@%_49_0 (+ main@%.05.i24_0 (- 1)))
                a!1
                (or (<= @a_2_0 0) (> main@%_50_0 0))
                (> @a_2_0 0)
                (=> main@_53_0 (and main@_53_0 main@.lr.ph25_0))
                (=> (and main@_53_0 main@.lr.ph25_0) main@%_52_0)
                (=> main@_53_0 a!2)
                (=> main@_53_0 (or (<= @a_2_0 0) (> main@%_54_0 0)))
                (=> main@_53_0 (> @a_2_0 0))
                (=> main@_53_0 (> @a_2_0 0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| main@.lr.ph25_0)
                (=> main@_55_0
                    (or (and main@_55_0 main@_53_0)
                        |tuple(main@.lr.ph25_0, main@_55_0)|))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)| (not main@%_52_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_0 main@%sm7_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.1_0))
                (=> (and main@_55_0 main@_53_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_0))
                (=> |tuple(main@.lr.ph25_0, main@_55_0)|
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> main@_55_0
                    (= main@%_57_0 (> main@%_49_0 main@%.04.i2636_0)))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@_55_0))
                (=> (and main@._crit_edge_0 main@_55_0) (not main@%_57_0))
                (=> main@.preheader17_0
                    (and main@.preheader17_0 main@._crit_edge_0))
                (=> (and main@.preheader17_0 main@._crit_edge_0) main@%_36_0)
                (=> main@.preheader17_0 (= main@%_34_0 (+ main@%.04.i2636_0 1)))
                (=> main@.preheader17_0
                    (= main@%_35_0 (< main@%.04.i2636_0 main@%loop.bound_0)))
                (=> |tuple(main@.preheader17_0, main@.preheader_0)|
                    main@.preheader17_0)
                (=> |tuple(main@._crit_edge_0, main@.preheader_0)|
                    main@._crit_edge_0)
                (=> main@.preheader_0
                    (or |tuple(main@.preheader17_0, main@.preheader_0)|
                        |tuple(main@._crit_edge_0, main@.preheader_0)|))
                (=> |tuple(main@.preheader17_0, main@.preheader_0)|
                    (not main@%_35_0))
                (=> |tuple(main@._crit_edge_0, main@.preheader_0)|
                    (not main@%_36_0))
                true
                a!3
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_38_0 0)))
                (=> main@.preheader_0 (> @a_1_0 0))
                (=> main@.preheader_0 a!4)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_40_0 0)))
                (=> main@.preheader_0 (> @a_2_0 0))
                (=> main@.preheader_0
                    (= main@%or.cond1421_0 (or main@%_42_0 main@%_44_0)))
                (=> main@.lr.ph.preheader_0
                    (and main@.lr.ph.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph.preheader_0 main@.preheader_0)
                    main@%or.cond1421_0)
                (=> main@.lr.ph.preheader_0
                    (= main@%or.cond1633_0 (or main@%_45_0 main@%_47_0)))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    main@.lr.ph.preheader_0)
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    main@.preheader_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                        |tuple(main@.preheader_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond1633_0))
                (=> |tuple(main@.preheader_0, main@verifier.error_0)|
                    (not main@%or.cond1421_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph35 main@%_58_0
                               main@%.03.i2234_0
                               @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%shadow.mem.4.2_0)
                true
                (= main@%_59_0 (< main@%.03.i2234_0 9))
                main@%_59_0
                (= main@%_60_0 (+ @a_1_0 (* 0 40) (* main@%_58_0 4)))
                (or (<= @a_1_0 0) (> main@%_60_0 0))
                (> @a_1_0 0)
                (= main@%_62_0 (+ @a_2_0 (* 0 40) (* main@%_58_0 4)))
                (or (<= @a_2_0 0) (> main@%_62_0 0))
                (> @a_2_0 0)
                (= main@%or.cond14_0 (or main@%_64_0 main@%_66_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph35_0))
                (=> (and main@.lr.ph_0 main@.lr.ph35_0) main@%or.cond14_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond16_0 (or main@%_67_0 main@%_69_0)))
                (=> main@.lr.ph_0 (= main@%_70_0 (+ main@%_58_0 1)))
                (=> main@.lr.ph35_1 (and main@.lr.ph35_1 main@.lr.ph_0))
                (=> (and main@.lr.ph35_1 main@.lr.ph_0) main@%or.cond16_0)
                (=> (and main@.lr.ph35_1 main@.lr.ph_0)
                    (= main@%_58_1 main@%_70_0))
                (=> (and main@.lr.ph35_1 main@.lr.ph_0)
                    (= main@%.03.i2234_1 main@%_58_0))
                (=> (and main@.lr.ph35_1 main@.lr.ph_0)
                    (= main@%_58_2 main@%_58_1))
                (=> (and main@.lr.ph35_1 main@.lr.ph_0)
                    (= main@%.03.i2234_2 main@%.03.i2234_1))
                main@.lr.ph35_1)))
  (=> a!1
      (main@.lr.ph35 main@%_58_2
                     main@%.03.i2234_2
                     @a_1_0
                     main@%shadow.mem.0.2_0
                     @a_2_0
                     main@%shadow.mem.4.2_0))))
(rule (let ((a!1 (and (main@.lr.ph35 main@%_58_0
                               main@%.03.i2234_0
                               @a_1_0
                               main@%shadow.mem.0.2_0
                               @a_2_0
                               main@%shadow.mem.4.2_0)
                true
                (= main@%_59_0 (< main@%.03.i2234_0 9))
                main@%_59_0
                (= main@%_60_0 (+ @a_1_0 (* 0 40) (* main@%_58_0 4)))
                (or (<= @a_1_0 0) (> main@%_60_0 0))
                (> @a_1_0 0)
                (= main@%_62_0 (+ @a_2_0 (* 0 40) (* main@%_58_0 4)))
                (or (<= @a_2_0 0) (> main@%_62_0 0))
                (> @a_2_0 0)
                (= main@%or.cond14_0 (or main@%_64_0 main@%_66_0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph35_0))
                (=> (and main@.lr.ph_0 main@.lr.ph35_0) main@%or.cond14_0)
                (=> main@.lr.ph_0
                    (= main@%or.cond16_0 (or main@%_67_0 main@%_69_0)))
                (=> main@.lr.ph_0 (= main@%_70_0 (+ main@%_58_0 1)))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)| main@.lr.ph_0)
                (=> |tuple(main@.lr.ph35_0, main@verifier.error_0)|
                    main@.lr.ph35_0)
                (=> main@verifier.error_0
                    (or |tuple(main@.lr.ph_0, main@verifier.error_0)|
                        |tuple(main@.lr.ph35_0, main@verifier.error_0)|))
                (=> |tuple(main@.lr.ph_0, main@verifier.error_0)|
                    (not main@%or.cond16_0))
                (=> |tuple(main@.lr.ph35_0, main@verifier.error_0)|
                    (not main@%or.cond14_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

