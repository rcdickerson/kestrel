(set-info :original "./results/chc/bytecode/unno/sa/half-square.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph12 (Int Int Int Int Int Int ))
(declare-rel main@_29 (Int Int Int Int Int Int Bool ))
(declare-rel main@.preheader5.split.us (Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int ))
(declare-rel main@_46 (Int Int Bool ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_47_0 Bool )
(declare-var main@%_48_0 Bool )
(declare-var main@%.411.i_2 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 Bool )
(declare-var main@%_41_0 Int )
(declare-var main@%_43_0 Bool )
(declare-var main@%_44_0 Bool )
(declare-var main@%_45_0 Bool )
(declare-var main@%_35_0 Bool )
(declare-var main@%_36_0 Bool )
(declare-var main@%_37_0 Bool )
(declare-var main@%.35.i8_2 Int )
(declare-var main@%.29.i7_2 Int )
(declare-var main@%_33_0 Bool )
(declare-var main@%_31_0 Bool )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Bool )
(declare-var main@%_18_0 Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%.02.i11_2 Int )
(declare-var main@%.07.i10_2 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_17_3 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@_9_0 Bool )
(declare-var main@_12_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@_16_0 Bool )
(declare-var |tuple(main@_9_0, main@_16_0)| Bool )
(declare-var |tuple(main@entry_0, main@_16_0)| Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%_17_1 Bool )
(declare-var main@%_17_2 Bool )
(declare-var main@.lr.ph12_0 Bool )
(declare-var main@%.02.i11_0 Int )
(declare-var main@%.07.i10_0 Int )
(declare-var main@%.02.i11_1 Int )
(declare-var main@%.07.i10_1 Int )
(declare-var main@.preheader6_0 Bool )
(declare-var main@%.07.i.lcssa_0 Int )
(declare-var main@%.02.i.lcssa_0 Int )
(declare-var main@%.07.i.lcssa_1 Int )
(declare-var main@%.02.i.lcssa_1 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@_29_0 Bool )
(declare-var main@%.18.i_0 Int )
(declare-var main@%.18.i_1 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%.13.i_0 Int )
(declare-var main@.lr.ph12_1 Bool )
(declare-var main@%_30_0 Bool )
(declare-var main@%_32_0 Int )
(declare-var main@_29_1 Bool )
(declare-var main@%.18.i_2 Int )
(declare-var main@.preheader5_0 Bool )
(declare-var main@.preheader5.split.us_0 Bool )
(declare-var main@%.24.i.us_0 Int )
(declare-var main@%.24.i.us_1 Int )
(declare-var main@.preheader4_0 Bool )
(declare-var main@%.24.i.lcssa_0 Int )
(declare-var main@%.24.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.35.i8_0 Int )
(declare-var main@%.29.i7_0 Int )
(declare-var main@%.35.i8_1 Int )
(declare-var main@%.29.i7_1 Int )
(declare-var main@.preheader3_0 Bool )
(declare-var main@%.29.i.lcssa_0 Int )
(declare-var main@%.35.i.lcssa_0 Int )
(declare-var main@%.29.i.lcssa_1 Int )
(declare-var main@%.35.i.lcssa_1 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@_46_0 Bool )
(declare-var main@%.411.i_0 Int )
(declare-var main@%.411.i_1 Int )
(declare-var main@%_34_0 Int )
(declare-var main@.preheader5.split.us_1 Bool )
(declare-var main@%.24.i.us_2 Int )
(declare-var main@%.310.i_0 Int )
(declare-var main@%_42_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@%_49_0 Int )
(declare-var main@_46_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (=> main@_9_0 (and main@_9_0 main@entry_0))
                (=> (and main@_9_0 main@entry_0) main@%_8_0)
                (=> main@_9_0 (= main@%_10_0 (> main@%_1_0 main@%_3_0)))
                (=> main@_9_0 (= main@%_11_0 (> main@%_3_0 0)))
                (=> main@_9_0
                    (= main@%or.cond.i_0 (and main@%_10_0 main@%_11_0)))
                (=> main@_12_0 (and main@_12_0 main@_9_0))
                (=> (and main@_12_0 main@_9_0) main@%or.cond.i_0)
                (=> main@_12_0 (= main@%_13_0 (> main@%_1_0 main@%_7_0)))
                (=> main@_12_0 (= main@%_14_0 (> main@%_7_0 0)))
                (=> main@_12_0 (= main@%_15_0 (and main@%_13_0 main@%_14_0)))
                (=> |tuple(main@_9_0, main@_16_0)| main@_9_0)
                (=> |tuple(main@entry_0, main@_16_0)| main@entry_0)
                (=> main@_16_0
                    (or (and main@_16_0 main@_12_0)
                        |tuple(main@_9_0, main@_16_0)|
                        |tuple(main@entry_0, main@_16_0)|))
                (=> |tuple(main@_9_0, main@_16_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@entry_0, main@_16_0)| (not main@%_8_0))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_0 main@%_15_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_1 false))
                (=> |tuple(main@entry_0, main@_16_0)| (= main@%_17_2 false))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_3 main@%_17_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_3 main@%_17_1))
                (=> |tuple(main@entry_0, main@_16_0)|
                    (= main@%_17_3 main@%_17_2))
                (=> main@_16_0 main@%_17_3)
                (=> main@_16_0 (= main@%_18_0 (> main@%_3_0 0)))
                (=> main@_16_0 (= main@%_19_0 (> main@%_7_0 0)))
                (=> main@_16_0
                    (= main@%_20_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@_16_0))
                (=> (and main@.lr.ph12_0 main@_16_0) main@%_20_0)
                (=> (and main@.lr.ph12_0 main@_16_0) (= main@%.02.i11_0 0))
                (=> (and main@.lr.ph12_0 main@_16_0) (= main@%.07.i10_0 0))
                (=> (and main@.lr.ph12_0 main@_16_0)
                    (= main@%.02.i11_1 main@%.02.i11_0))
                (=> (and main@.lr.ph12_0 main@_16_0)
                    (= main@%.07.i10_1 main@%.07.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_1_0
                     main@%_5_0
                     main@%_7_0
                     main@%_3_0
                     main@%.07.i10_1
                     main@%.02.i11_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (=> main@_9_0 (and main@_9_0 main@entry_0))
                (=> (and main@_9_0 main@entry_0) main@%_8_0)
                (=> main@_9_0 (= main@%_10_0 (> main@%_1_0 main@%_3_0)))
                (=> main@_9_0 (= main@%_11_0 (> main@%_3_0 0)))
                (=> main@_9_0
                    (= main@%or.cond.i_0 (and main@%_10_0 main@%_11_0)))
                (=> main@_12_0 (and main@_12_0 main@_9_0))
                (=> (and main@_12_0 main@_9_0) main@%or.cond.i_0)
                (=> main@_12_0 (= main@%_13_0 (> main@%_1_0 main@%_7_0)))
                (=> main@_12_0 (= main@%_14_0 (> main@%_7_0 0)))
                (=> main@_12_0 (= main@%_15_0 (and main@%_13_0 main@%_14_0)))
                (=> |tuple(main@_9_0, main@_16_0)| main@_9_0)
                (=> |tuple(main@entry_0, main@_16_0)| main@entry_0)
                (=> main@_16_0
                    (or (and main@_16_0 main@_12_0)
                        |tuple(main@_9_0, main@_16_0)|
                        |tuple(main@entry_0, main@_16_0)|))
                (=> |tuple(main@_9_0, main@_16_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@entry_0, main@_16_0)| (not main@%_8_0))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_0 main@%_15_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_1 false))
                (=> |tuple(main@entry_0, main@_16_0)| (= main@%_17_2 false))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_3 main@%_17_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_3 main@%_17_1))
                (=> |tuple(main@entry_0, main@_16_0)|
                    (= main@%_17_3 main@%_17_2))
                (=> main@_16_0 main@%_17_3)
                (=> main@_16_0 (= main@%_18_0 (> main@%_3_0 0)))
                (=> main@_16_0 (= main@%_19_0 (> main@%_7_0 0)))
                (=> main@_16_0
                    (= main@%_20_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> main@.preheader6_0 (and main@.preheader6_0 main@_16_0))
                (=> (and main@.preheader6_0 main@_16_0) (not main@%_20_0))
                (=> (and main@.preheader6_0 main@_16_0)
                    (= main@%.07.i.lcssa_0 0))
                (=> (and main@.preheader6_0 main@_16_0)
                    (= main@%.02.i.lcssa_0 0))
                (=> (and main@.preheader6_0 main@_16_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader6_0 main@_16_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@.preheader6_0
                    (= main@%_21_0 (<= main@%_7_0 main@%.02.i.lcssa_1)))
                (=> main@_29_0 (and main@_29_0 main@.preheader6_0))
                (=> (and main@_29_0 main@.preheader6_0)
                    (= main@%.18.i_0 main@%.07.i.lcssa_1))
                (=> (and main@_29_0 main@.preheader6_0)
                    (= main@%.18.i_1 main@%.18.i_0))
                main@_29_0)))
  (=> a!1
      (main@_29 main@%_1_0
                main@%_5_0
                main@%.18.i_1
                main@%_7_0
                main@%.02.i.lcssa_1
                main@%_3_0
                main@%_21_0))))
(rule (=> (and (main@.lr.ph12 main@%_1_0
                        main@%_5_0
                        main@%_7_0
                        main@%_3_0
                        main@%.07.i10_0
                        main@%.02.i11_0)
         true
         (= main@%_22_0 (+ main@%.07.i10_0 1))
         (= main@%_23_0 (+ main@%.02.i11_0 1))
         (= main@%_24_0 (> main@%_7_0 main@%_23_0))
         (= main@%_25_0 (+ main@%.02.i11_0 2))
         (= main@%.13.i_0 (ite main@%_24_0 main@%_25_0 main@%_23_0))
         (= main@%_26_0 (> main@%_3_0 main@%_22_0))
         (= main@%_27_0 (> main@%_7_0 main@%.13.i_0))
         (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
         (=> main@.lr.ph12_1 (and main@.lr.ph12_1 main@.lr.ph12_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0) main@%_28_0)
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.02.i11_1 main@%.13.i_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.07.i10_1 main@%_22_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.02.i11_2 main@%.02.i11_1))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.07.i10_2 main@%.07.i10_1))
         main@.lr.ph12_1)
    (main@.lr.ph12 main@%_1_0
                   main@%_5_0
                   main@%_7_0
                   main@%_3_0
                   main@%.07.i10_2
                   main@%.02.i11_2)))
(rule (let ((a!1 (and (main@.lr.ph12 main@%_1_0
                               main@%_5_0
                               main@%_7_0
                               main@%_3_0
                               main@%.07.i10_0
                               main@%.02.i11_0)
                true
                (= main@%_22_0 (+ main@%.07.i10_0 1))
                (= main@%_23_0 (+ main@%.02.i11_0 1))
                (= main@%_24_0 (> main@%_7_0 main@%_23_0))
                (= main@%_25_0 (+ main@%.02.i11_0 2))
                (= main@%.13.i_0 (ite main@%_24_0 main@%_25_0 main@%_23_0))
                (= main@%_26_0 (> main@%_3_0 main@%_22_0))
                (= main@%_27_0 (> main@%_7_0 main@%.13.i_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader6_0 (and main@.preheader6_0 main@.lr.ph12_0))
                (=> (and main@.preheader6_0 main@.lr.ph12_0) (not main@%_28_0))
                (=> (and main@.preheader6_0 main@.lr.ph12_0)
                    (= main@%.07.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader6_0 main@.lr.ph12_0)
                    (= main@%.02.i.lcssa_0 main@%.13.i_0))
                (=> (and main@.preheader6_0 main@.lr.ph12_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader6_0 main@.lr.ph12_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@.preheader6_0
                    (= main@%_21_0 (<= main@%_7_0 main@%.02.i.lcssa_1)))
                (=> main@_29_0 (and main@_29_0 main@.preheader6_0))
                (=> (and main@_29_0 main@.preheader6_0)
                    (= main@%.18.i_0 main@%.07.i.lcssa_1))
                (=> (and main@_29_0 main@.preheader6_0)
                    (= main@%.18.i_1 main@%.18.i_0))
                main@_29_0)))
  (=> a!1
      (main@_29 main@%_1_0
                main@%_5_0
                main@%.18.i_1
                main@%_7_0
                main@%.02.i.lcssa_1
                main@%_3_0
                main@%_21_0))))
(rule (=> (and (main@_29 main@%_1_0
                   main@%_5_0
                   main@%.18.i_0
                   main@%_7_0
                   main@%.02.i.lcssa_0
                   main@%_3_0
                   main@%_21_0)
         true
         (= main@%_30_0 (> main@%_3_0 main@%.18.i_0))
         (= main@%_31_0 (ite main@%_30_0 main@%_21_0 false))
         (= main@%_32_0 (+ main@%.18.i_0 1))
         (=> main@_29_1 (and main@_29_1 main@_29_0))
         (=> (and main@_29_1 main@_29_0) main@%_31_0)
         (=> (and main@_29_1 main@_29_0) (= main@%.18.i_1 main@%_32_0))
         (=> (and main@_29_1 main@_29_0) (= main@%.18.i_2 main@%.18.i_1))
         main@_29_1)
    (main@_29 main@%_1_0
              main@%_5_0
              main@%.18.i_2
              main@%_7_0
              main@%.02.i.lcssa_0
              main@%_3_0
              main@%_21_0)))
(rule (=> (and (main@_29 main@%_1_0
                   main@%_5_0
                   main@%.18.i_0
                   main@%_7_0
                   main@%.02.i.lcssa_0
                   main@%_3_0
                   main@%_21_0)
         true
         (= main@%_30_0 (> main@%_3_0 main@%.18.i_0))
         (= main@%_31_0 (ite main@%_30_0 main@%_21_0 false))
         (= main@%_32_0 (+ main@%.18.i_0 1))
         (=> main@.preheader5_0 (and main@.preheader5_0 main@_29_0))
         (=> (and main@.preheader5_0 main@_29_0) (not main@%_31_0))
         (=> main@.preheader5.split.us_0
             (and main@.preheader5.split.us_0 main@.preheader5_0))
         (=> (and main@.preheader5.split.us_0 main@.preheader5_0)
             (not main@%_30_0))
         (=> (and main@.preheader5.split.us_0 main@.preheader5_0)
             (= main@%.24.i.us_0 main@%.02.i.lcssa_0))
         (=> (and main@.preheader5.split.us_0 main@.preheader5_0)
             (= main@%.24.i.us_1 main@%.24.i.us_0))
         main@.preheader5.split.us_0)
    (main@.preheader5.split.us
      main@%_1_0
      main@%_5_0
      main@%.18.i_0
      main@%_7_0
      main@%.24.i.us_1)))
(rule (let ((a!1 (and (main@_29 main@%_1_0
                          main@%_5_0
                          main@%.18.i_0
                          main@%_7_0
                          main@%.02.i.lcssa_0
                          main@%_3_0
                          main@%_21_0)
                true
                (= main@%_30_0 (> main@%_3_0 main@%.18.i_0))
                (= main@%_31_0 (ite main@%_30_0 main@%_21_0 false))
                (= main@%_32_0 (+ main@%.18.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_29_0))
                (=> (and main@.preheader5_0 main@_29_0) (not main@%_31_0))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0) main@%_30_0)
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.24.i.lcssa_0 main@%.02.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.24.i.lcssa_1 main@%.24.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%_35_0 (> main@%_1_0 main@%.18.i_0)))
                (=> main@.preheader4_0
                    (= main@%_36_0 (> main@%_5_0 main@%.24.i.lcssa_1)))
                (=> main@.preheader4_0
                    (= main@%_37_0 (ite main@%_35_0 main@%_36_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader4_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0) main@%_37_0)
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.35.i8_0 main@%.24.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.29.i7_0 main@%.18.i_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.35.i8_1 main@%.35.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.29.i7_1 main@%.29.i7_0))
                main@.lr.ph_0)))
  (=> a!1 (main@.lr.ph main@%_1_0 main@%_5_0 main@%.29.i7_1 main@%.35.i8_1))))
(rule (let ((a!1 (and (main@_29 main@%_1_0
                          main@%_5_0
                          main@%.18.i_0
                          main@%_7_0
                          main@%.02.i.lcssa_0
                          main@%_3_0
                          main@%_21_0)
                true
                (= main@%_30_0 (> main@%_3_0 main@%.18.i_0))
                (= main@%_31_0 (ite main@%_30_0 main@%_21_0 false))
                (= main@%_32_0 (+ main@%.18.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_29_0))
                (=> (and main@.preheader5_0 main@_29_0) (not main@%_31_0))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0) main@%_30_0)
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.24.i.lcssa_0 main@%.02.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.24.i.lcssa_1 main@%.24.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%_35_0 (> main@%_1_0 main@%.18.i_0)))
                (=> main@.preheader4_0
                    (= main@%_36_0 (> main@%_5_0 main@%.24.i.lcssa_1)))
                (=> main@.preheader4_0
                    (= main@%_37_0 (ite main@%_35_0 main@%_36_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_37_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.29.i.lcssa_0 main@%.18.i_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.35.i.lcssa_0 main@%.24.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.29.i.lcssa_1 main@%.29.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.35.i.lcssa_1 main@%.35.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%_38_0 (<= main@%_5_0 main@%.35.i.lcssa_1)))
                (=> main@_46_0 (and main@_46_0 main@.preheader3_0))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_0 main@%.29.i.lcssa_1))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_1 main@%.411.i_0))
                main@_46_0)))
  (=> a!1 (main@_46 main@%_1_0 main@%.411.i_1 main@%_38_0))))
(rule (=> (and (main@.preheader5.split.us
           main@%_1_0
           main@%_5_0
           main@%.18.i_0
           main@%_7_0
           main@%.24.i.us_0)
         true
         (= main@%_33_0 (> main@%_7_0 main@%.24.i.us_0))
         (= main@%_34_0 (+ main@%.24.i.us_0 1))
         (=> main@.preheader5.split.us_1
             (and main@.preheader5.split.us_1 main@.preheader5.split.us_0))
         (=> (and main@.preheader5.split.us_1 main@.preheader5.split.us_0)
             main@%_33_0)
         (=> (and main@.preheader5.split.us_1 main@.preheader5.split.us_0)
             (= main@%.24.i.us_1 main@%_34_0))
         (=> (and main@.preheader5.split.us_1 main@.preheader5.split.us_0)
             (= main@%.24.i.us_2 main@%.24.i.us_1))
         main@.preheader5.split.us_1)
    (main@.preheader5.split.us
      main@%_1_0
      main@%_5_0
      main@%.18.i_0
      main@%_7_0
      main@%.24.i.us_2)))
(rule (let ((a!1 (and (main@.preheader5.split.us
                  main@%_1_0
                  main@%_5_0
                  main@%.18.i_0
                  main@%_7_0
                  main@%.24.i.us_0)
                true
                (= main@%_33_0 (> main@%_7_0 main@%.24.i.us_0))
                (= main@%_34_0 (+ main@%.24.i.us_0 1))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5.split.us_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (not main@%_33_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (= main@%.24.i.lcssa_0 main@%.24.i.us_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (= main@%.24.i.lcssa_1 main@%.24.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%_35_0 (> main@%_1_0 main@%.18.i_0)))
                (=> main@.preheader4_0
                    (= main@%_36_0 (> main@%_5_0 main@%.24.i.lcssa_1)))
                (=> main@.preheader4_0
                    (= main@%_37_0 (ite main@%_35_0 main@%_36_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader4_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0) main@%_37_0)
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.35.i8_0 main@%.24.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.29.i7_0 main@%.18.i_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.35.i8_1 main@%.35.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader4_0)
                    (= main@%.29.i7_1 main@%.29.i7_0))
                main@.lr.ph_0)))
  (=> a!1 (main@.lr.ph main@%_1_0 main@%_5_0 main@%.29.i7_1 main@%.35.i8_1))))
(rule (let ((a!1 (and (main@.preheader5.split.us
                  main@%_1_0
                  main@%_5_0
                  main@%.18.i_0
                  main@%_7_0
                  main@%.24.i.us_0)
                true
                (= main@%_33_0 (> main@%_7_0 main@%.24.i.us_0))
                (= main@%_34_0 (+ main@%.24.i.us_0 1))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5.split.us_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (not main@%_33_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (= main@%.24.i.lcssa_0 main@%.24.i.us_0))
                (=> (and main@.preheader4_0 main@.preheader5.split.us_0)
                    (= main@%.24.i.lcssa_1 main@%.24.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%_35_0 (> main@%_1_0 main@%.18.i_0)))
                (=> main@.preheader4_0
                    (= main@%_36_0 (> main@%_5_0 main@%.24.i.lcssa_1)))
                (=> main@.preheader4_0
                    (= main@%_37_0 (ite main@%_35_0 main@%_36_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_37_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.29.i.lcssa_0 main@%.18.i_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.35.i.lcssa_0 main@%.24.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.29.i.lcssa_1 main@%.29.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.35.i.lcssa_1 main@%.35.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%_38_0 (<= main@%_5_0 main@%.35.i.lcssa_1)))
                (=> main@_46_0 (and main@_46_0 main@.preheader3_0))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_0 main@%.29.i.lcssa_1))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_1 main@%.411.i_0))
                main@_46_0)))
  (=> a!1 (main@_46 main@%_1_0 main@%.411.i_1 main@%_38_0))))
(rule (=> (and (main@.lr.ph main@%_1_0 main@%_5_0 main@%.29.i7_0 main@%.35.i8_0)
         true
         (= main@%_39_0 (+ main@%.29.i7_0 1))
         (= main@%_40_0 (> main@%_1_0 main@%_39_0))
         (= main@%_41_0 (+ main@%.29.i7_0 2))
         (= main@%.310.i_0 (ite main@%_40_0 main@%_41_0 main@%_39_0))
         (= main@%_42_0 (+ main@%.35.i8_0 1))
         (= main@%_43_0 (> main@%_1_0 main@%.310.i_0))
         (= main@%_44_0 (> main@%_5_0 main@%_42_0))
         (= main@%_45_0 (ite main@%_43_0 main@%_44_0 false))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_45_0)
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.35.i8_1 main@%_42_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.29.i7_1 main@%.310.i_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.35.i8_2 main@%.35.i8_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.29.i7_2 main@%.29.i7_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%_1_0 main@%_5_0 main@%.29.i7_2 main@%.35.i8_2)))
(rule (let ((a!1 (and (main@.lr.ph main@%_1_0
                             main@%_5_0
                             main@%.29.i7_0
                             main@%.35.i8_0)
                true
                (= main@%_39_0 (+ main@%.29.i7_0 1))
                (= main@%_40_0 (> main@%_1_0 main@%_39_0))
                (= main@%_41_0 (+ main@%.29.i7_0 2))
                (= main@%.310.i_0 (ite main@%_40_0 main@%_41_0 main@%_39_0))
                (= main@%_42_0 (+ main@%.35.i8_0 1))
                (= main@%_43_0 (> main@%_1_0 main@%.310.i_0))
                (= main@%_44_0 (> main@%_5_0 main@%_42_0))
                (= main@%_45_0 (ite main@%_43_0 main@%_44_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph_0))
                (=> (and main@.preheader3_0 main@.lr.ph_0) (not main@%_45_0))
                (=> (and main@.preheader3_0 main@.lr.ph_0)
                    (= main@%.29.i.lcssa_0 main@%.310.i_0))
                (=> (and main@.preheader3_0 main@.lr.ph_0)
                    (= main@%.35.i.lcssa_0 main@%_42_0))
                (=> (and main@.preheader3_0 main@.lr.ph_0)
                    (= main@%.29.i.lcssa_1 main@%.29.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph_0)
                    (= main@%.35.i.lcssa_1 main@%.35.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%_38_0 (<= main@%_5_0 main@%.35.i.lcssa_1)))
                (=> main@_46_0 (and main@_46_0 main@.preheader3_0))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_0 main@%.29.i.lcssa_1))
                (=> (and main@_46_0 main@.preheader3_0)
                    (= main@%.411.i_1 main@%.411.i_0))
                main@_46_0)))
  (=> a!1 (main@_46 main@%_1_0 main@%.411.i_1 main@%_38_0))))
(rule (=> (and (main@_46 main@%_1_0 main@%.411.i_0 main@%_38_0)
         true
         (= main@%_47_0 (> main@%_1_0 main@%.411.i_0))
         (= main@%_48_0 (ite main@%_47_0 main@%_38_0 false))
         (= main@%_49_0 (+ main@%.411.i_0 1))
         (=> main@_46_1 (and main@_46_1 main@_46_0))
         (=> (and main@_46_1 main@_46_0) main@%_48_0)
         (=> (and main@_46_1 main@_46_0) (= main@%.411.i_1 main@%_49_0))
         (=> (and main@_46_1 main@_46_0) (= main@%.411.i_2 main@%.411.i_1))
         main@_46_1)
    (main@_46 main@%_1_0 main@%.411.i_2 main@%_38_0)))
(rule (=> (and (main@_46 main@%_1_0 main@%.411.i_0 main@%_38_0)
         true
         (= main@%_47_0 (> main@%_1_0 main@%.411.i_0))
         (= main@%_48_0 (ite main@%_47_0 main@%_38_0 false))
         (= main@%_49_0 (+ main@%.411.i_0 1))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@_46_0))
         (=> (and main@verifier.error_0 main@_46_0) (not main@%_48_0))
         (=> main@verifier.error_0 false)
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(query main@verifier.error.split)

