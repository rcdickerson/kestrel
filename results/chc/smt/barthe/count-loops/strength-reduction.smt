(set-info :original "./results/chc/bytecode/barthe/count-loops/strength-reduction.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph15 (Int Int Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph7 (Int Int Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph.split.us (Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_56_0 Bool )
(declare-var main@%_50_0 Bool )
(declare-var main@%_44_0 Bool )
(declare-var main@%_45_0 Bool )
(declare-var main@%_46_0 Bool )
(declare-var main@%.2.i4.us_2 Int )
(declare-var main@%.23.i3.us_2 Int )
(declare-var main@%.210.i2.us_2 Int )
(declare-var main@%_51_0 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%_55_0 Bool )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Bool )
(declare-var main@%_29_0 Bool )
(declare-var main@%.15.i6_2 Int )
(declare-var main@%.17.i5_2 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Bool )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%_41_0 Bool )
(declare-var main@%_42_0 Bool )
(declare-var main@%_43_0 Bool )
(declare-var main@%_24_0 Bool )
(declare-var main@%_25_0 Bool )
(declare-var main@%_26_0 Bool )
(declare-var main@%.0.i14_2 Int )
(declare-var main@%.01.i13_2 Int )
(declare-var main@%.04.i12_2 Int )
(declare-var main@%.06.i11_2 Int )
(declare-var main@%.08.i10_2 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_23_2 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@_18_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@_22_0 Bool )
(declare-var |tuple(main@entry_0, main@_22_0)| Bool )
(declare-var main@%_23_0 Bool )
(declare-var main@%_23_1 Bool )
(declare-var main@.lr.ph15_0 Bool )
(declare-var main@%.0.i14_0 Int )
(declare-var main@%.01.i13_0 Int )
(declare-var main@%.04.i12_0 Int )
(declare-var main@%.06.i11_0 Int )
(declare-var main@%.08.i10_0 Int )
(declare-var main@%.0.i14_1 Int )
(declare-var main@%.01.i13_1 Int )
(declare-var main@%.04.i12_1 Int )
(declare-var main@%.06.i11_1 Int )
(declare-var main@%.08.i10_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.08.i.lcssa_0 Int )
(declare-var main@%.06.i.lcssa_0 Int )
(declare-var main@%.04.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.08.i.lcssa_1 Int )
(declare-var main@%.06.i.lcssa_1 Int )
(declare-var main@%.04.i.lcssa_1 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@.lr.ph7_0 Bool )
(declare-var main@%.15.i6_0 Int )
(declare-var main@%.17.i5_0 Int )
(declare-var main@%.15.i6_1 Int )
(declare-var main@%.17.i5_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.17.i.lcssa_0 Int )
(declare-var main@%.15.i.lcssa_0 Int )
(declare-var main@%.17.i.lcssa_1 Int )
(declare-var main@%.15.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%.2.i4.us_0 Int )
(declare-var main@%.23.i3.us_0 Int )
(declare-var main@%.210.i2.us_0 Int )
(declare-var main@%.2.i4.us_1 Int )
(declare-var main@%.23.i3.us_1 Int )
(declare-var main@%.210.i2.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.210.i.lcssa_0 Int )
(declare-var main@%.210.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_32_0 Int )
(declare-var main@%_33_0 Int )
(declare-var main@%.19.i_0 Int )
(declare-var main@%.12.i_0 Int )
(declare-var main@%.1.i_0 Int )
(declare-var main@.lr.ph15_1 Bool )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@.lr.ph7_1 Bool )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%_49_0 Int )
(declare-var main@.lr.ph.split.us_1 Bool )
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
                (= main@%_8_0 @arb_int_0)
                (= main@%_10_0 @arb_int_0)
                (= main@%_12_0 @arb_int_0)
                (= main@%_14_0 @arb_int_0)
                (= main@%_16_0 (= main@%_1_0 main@%_9_0))
                (= main@%_17_0 (= main@%_3_0 main@%_11_0))
                (= main@%or.cond.i_0 (ite main@%_16_0 main@%_17_0 false))
                (=> main@_18_0 (and main@_18_0 main@entry_0))
                (=> (and main@_18_0 main@entry_0) main@%or.cond.i_0)
                (=> main@_18_0 (= main@%_19_0 (= main@%_5_0 main@%_13_0)))
                (=> main@_18_0 (= main@%_20_0 (= main@%_7_0 main@%_15_0)))
                (=> main@_18_0
                    (= main@%_21_0 (ite main@%_19_0 main@%_20_0 false)))
                (=> |tuple(main@entry_0, main@_22_0)| main@entry_0)
                (=> main@_22_0
                    (or (and main@_22_0 main@_18_0)
                        |tuple(main@entry_0, main@_22_0)|))
                (=> |tuple(main@entry_0, main@_22_0)| (not main@%or.cond.i_0))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_0 main@%_21_0))
                (=> |tuple(main@entry_0, main@_22_0)| (= main@%_23_1 false))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_2 main@%_23_0))
                (=> |tuple(main@entry_0, main@_22_0)|
                    (= main@%_23_2 main@%_23_1))
                (=> main@_22_0 main@%_23_2)
                (=> main@_22_0 (= main@%_24_0 (> main@%_5_0 0)))
                (=> main@_22_0 (= main@%_25_0 (> main@%_13_0 0)))
                (=> main@_22_0
                    (= main@%_26_0 (ite main@%_24_0 main@%_25_0 false)))
                (=> main@.lr.ph15_0 (and main@.lr.ph15_0 main@_22_0))
                (=> (and main@.lr.ph15_0 main@_22_0) main@%_26_0)
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.0.i14_0 main@%_11_0))
                (=> (and main@.lr.ph15_0 main@_22_0) (= main@%.01.i13_0 0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.04.i12_0 main@%_7_0))
                (=> (and main@.lr.ph15_0 main@_22_0) (= main@%.06.i11_0 0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.08.i10_0 main@%_15_0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.0.i14_1 main@%.0.i14_0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.01.i13_1 main@%.01.i13_0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.04.i12_1 main@%.04.i12_0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.06.i11_1 main@%.06.i11_0))
                (=> (and main@.lr.ph15_0 main@_22_0)
                    (= main@%.08.i10_1 main@%.08.i10_0))
                main@.lr.ph15_0)))
  (=> a!1
      (main@.lr.ph15 main@%_9_0
                     main@%_13_0
                     main@%_5_0
                     main@%_1_0
                     main@%_3_0
                     main@%.06.i11_1
                     main@%.04.i12_1
                     main@%.0.i14_1
                     main@%.08.i10_1
                     main@%.01.i13_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 @arb_int_0)
                (= main@%_10_0 @arb_int_0)
                (= main@%_12_0 @arb_int_0)
                (= main@%_14_0 @arb_int_0)
                (= main@%_16_0 (= main@%_1_0 main@%_9_0))
                (= main@%_17_0 (= main@%_3_0 main@%_11_0))
                (= main@%or.cond.i_0 (ite main@%_16_0 main@%_17_0 false))
                (=> main@_18_0 (and main@_18_0 main@entry_0))
                (=> (and main@_18_0 main@entry_0) main@%or.cond.i_0)
                (=> main@_18_0 (= main@%_19_0 (= main@%_5_0 main@%_13_0)))
                (=> main@_18_0 (= main@%_20_0 (= main@%_7_0 main@%_15_0)))
                (=> main@_18_0
                    (= main@%_21_0 (ite main@%_19_0 main@%_20_0 false)))
                (=> |tuple(main@entry_0, main@_22_0)| main@entry_0)
                (=> main@_22_0
                    (or (and main@_22_0 main@_18_0)
                        |tuple(main@entry_0, main@_22_0)|))
                (=> |tuple(main@entry_0, main@_22_0)| (not main@%or.cond.i_0))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_0 main@%_21_0))
                (=> |tuple(main@entry_0, main@_22_0)| (= main@%_23_1 false))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_2 main@%_23_0))
                (=> |tuple(main@entry_0, main@_22_0)|
                    (= main@%_23_2 main@%_23_1))
                (=> main@_22_0 main@%_23_2)
                (=> main@_22_0 (= main@%_24_0 (> main@%_5_0 0)))
                (=> main@_22_0 (= main@%_25_0 (> main@%_13_0 0)))
                (=> main@_22_0
                    (= main@%_26_0 (ite main@%_24_0 main@%_25_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_22_0))
                (=> (and main@.preheader1_0 main@_22_0) (not main@%_26_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_0 main@%_15_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@.preheader1_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0) main@%_29_0)
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.15.i6_0 main@%.04.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.17.i5_0 main@%.06.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.15.i6_1 main@%.15.i6_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.17.i5_1 main@%.17.i5_0))
                main@.lr.ph7_0)))
  (=> a!1
      (main@.lr.ph7 main@%_9_0
                    main@%_13_0
                    main@%_5_0
                    main@%.01.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.08.i.lcssa_1
                    main@%.17.i5_1
                    main@%_1_0
                    main@%_3_0
                    main@%.15.i6_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 @arb_int_0)
                (= main@%_10_0 @arb_int_0)
                (= main@%_12_0 @arb_int_0)
                (= main@%_14_0 @arb_int_0)
                (= main@%_16_0 (= main@%_1_0 main@%_9_0))
                (= main@%_17_0 (= main@%_3_0 main@%_11_0))
                (= main@%or.cond.i_0 (ite main@%_16_0 main@%_17_0 false))
                (=> main@_18_0 (and main@_18_0 main@entry_0))
                (=> (and main@_18_0 main@entry_0) main@%or.cond.i_0)
                (=> main@_18_0 (= main@%_19_0 (= main@%_5_0 main@%_13_0)))
                (=> main@_18_0 (= main@%_20_0 (= main@%_7_0 main@%_15_0)))
                (=> main@_18_0
                    (= main@%_21_0 (ite main@%_19_0 main@%_20_0 false)))
                (=> |tuple(main@entry_0, main@_22_0)| main@entry_0)
                (=> main@_22_0
                    (or (and main@_22_0 main@_18_0)
                        |tuple(main@entry_0, main@_22_0)|))
                (=> |tuple(main@entry_0, main@_22_0)| (not main@%or.cond.i_0))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_0 main@%_21_0))
                (=> |tuple(main@entry_0, main@_22_0)| (= main@%_23_1 false))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_2 main@%_23_0))
                (=> |tuple(main@entry_0, main@_22_0)|
                    (= main@%_23_2 main@%_23_1))
                (=> main@_22_0 main@%_23_2)
                (=> main@_22_0 (= main@%_24_0 (> main@%_5_0 0)))
                (=> main@_22_0 (= main@%_25_0 (> main@%_13_0 0)))
                (=> main@_22_0
                    (= main@%_26_0 (ite main@%_24_0 main@%_25_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_22_0))
                (=> (and main@.preheader1_0 main@_22_0) (not main@%_26_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_0 main@%_15_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_29_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_0 main@%.06.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_0 main@%.08.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_1 main@%.210.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.15.i.lcssa_1
        main@%.2.i4.us_1
        main@%.210.i2.us_1
        main@%_9_0
        main@%.23.i3.us_1
        main@%_13_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 @arb_int_0)
                (= main@%_10_0 @arb_int_0)
                (= main@%_12_0 @arb_int_0)
                (= main@%_14_0 @arb_int_0)
                (= main@%_16_0 (= main@%_1_0 main@%_9_0))
                (= main@%_17_0 (= main@%_3_0 main@%_11_0))
                (= main@%or.cond.i_0 (ite main@%_16_0 main@%_17_0 false))
                (=> main@_18_0 (and main@_18_0 main@entry_0))
                (=> (and main@_18_0 main@entry_0) main@%or.cond.i_0)
                (=> main@_18_0 (= main@%_19_0 (= main@%_5_0 main@%_13_0)))
                (=> main@_18_0 (= main@%_20_0 (= main@%_7_0 main@%_15_0)))
                (=> main@_18_0
                    (= main@%_21_0 (ite main@%_19_0 main@%_20_0 false)))
                (=> |tuple(main@entry_0, main@_22_0)| main@entry_0)
                (=> main@_22_0
                    (or (and main@_22_0 main@_18_0)
                        |tuple(main@entry_0, main@_22_0)|))
                (=> |tuple(main@entry_0, main@_22_0)| (not main@%or.cond.i_0))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_0 main@%_21_0))
                (=> |tuple(main@entry_0, main@_22_0)| (= main@%_23_1 false))
                (=> (and main@_22_0 main@_18_0) (= main@%_23_2 main@%_23_0))
                (=> |tuple(main@entry_0, main@_22_0)|
                    (= main@%_23_2 main@%_23_1))
                (=> main@_22_0 main@%_23_2)
                (=> main@_22_0 (= main@%_24_0 (> main@%_5_0 0)))
                (=> main@_22_0 (= main@%_25_0 (> main@%_13_0 0)))
                (=> main@_22_0
                    (= main@%_26_0 (ite main@%_24_0 main@%_25_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_22_0))
                (=> (and main@.preheader1_0 main@_22_0) (not main@%_26_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_0 main@%_15_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_22_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_29_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_0 main@%.06.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_0 main@%.08.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_1 main@%.210.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_56_0 (= main@%.15.i.lcssa_1 main@%.210.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_56_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph15 main@%_9_0
                        main@%_13_0
                        main@%_5_0
                        main@%_1_0
                        main@%_3_0
                        main@%.06.i11_0
                        main@%.04.i12_0
                        main@%.0.i14_0
                        main@%.08.i10_0
                        main@%.01.i13_0)
         true
         (= main@%_31_0 (+ main@%_30_0 main@%_3_0))
         (= main@%_32_0 (+ main@%_31_0 main@%.04.i12_0))
         (= main@%_33_0 (+ main@%.06.i11_0 1))
         (= main@%_34_0 (+ main@%.0.i14_0 main@%.08.i10_0))
         (= main@%_35_0 (+ main@%.0.i14_0 main@%_9_0))
         (= main@%_36_0 (+ main@%.01.i13_0 1))
         (= main@%_37_0 (< main@%_36_0 main@%_13_0))
         (= main@%_38_0 (+ main@%.01.i13_0 2))
         (= main@%_39_0 (ite main@%_37_0 main@%_35_0 0))
         (= main@%.19.i_0 (+ main@%_34_0 main@%_39_0))
         (= main@%.12.i_0 (ite main@%_37_0 main@%_38_0 main@%_36_0))
         (= main@%_40_0 (ite main@%_37_0 main@%_9_0 0))
         (= main@%.1.i_0 (+ main@%_40_0 main@%_35_0))
         (= main@%_41_0 (< main@%_33_0 main@%_5_0))
         (= main@%_42_0 (< main@%.12.i_0 main@%_13_0))
         (= main@%_43_0 (ite main@%_41_0 main@%_42_0 false))
         (=> main@.lr.ph15_1 (and main@.lr.ph15_1 main@.lr.ph15_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0) main@%_43_0)
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.0.i14_1 main@%.1.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.01.i13_1 main@%.12.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.04.i12_1 main@%_32_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.06.i11_1 main@%_33_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.08.i10_1 main@%.19.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.0.i14_2 main@%.0.i14_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.01.i13_2 main@%.01.i13_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.04.i12_2 main@%.04.i12_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.06.i11_2 main@%.06.i11_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.08.i10_2 main@%.08.i10_1))
         main@.lr.ph15_1)
    (main@.lr.ph15 main@%_9_0
                   main@%_13_0
                   main@%_5_0
                   main@%_1_0
                   main@%_3_0
                   main@%.06.i11_2
                   main@%.04.i12_2
                   main@%.0.i14_2
                   main@%.08.i10_2
                   main@%.01.i13_2)))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_9_0
                               main@%_13_0
                               main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.06.i11_0
                               main@%.04.i12_0
                               main@%.0.i14_0
                               main@%.08.i10_0
                               main@%.01.i13_0)
                true
                (= main@%_31_0 (+ main@%_30_0 main@%_3_0))
                (= main@%_32_0 (+ main@%_31_0 main@%.04.i12_0))
                (= main@%_33_0 (+ main@%.06.i11_0 1))
                (= main@%_34_0 (+ main@%.0.i14_0 main@%.08.i10_0))
                (= main@%_35_0 (+ main@%.0.i14_0 main@%_9_0))
                (= main@%_36_0 (+ main@%.01.i13_0 1))
                (= main@%_37_0 (< main@%_36_0 main@%_13_0))
                (= main@%_38_0 (+ main@%.01.i13_0 2))
                (= main@%_39_0 (ite main@%_37_0 main@%_35_0 0))
                (= main@%.19.i_0 (+ main@%_34_0 main@%_39_0))
                (= main@%.12.i_0 (ite main@%_37_0 main@%_38_0 main@%_36_0))
                (= main@%_40_0 (ite main@%_37_0 main@%_9_0 0))
                (= main@%.1.i_0 (+ main@%_40_0 main@%_35_0))
                (= main@%_41_0 (< main@%_33_0 main@%_5_0))
                (= main@%_42_0 (< main@%.12.i_0 main@%_13_0))
                (= main@%_43_0 (ite main@%_41_0 main@%_42_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_43_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_0 main@%.19.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%_32_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@.preheader1_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0) main@%_29_0)
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.15.i6_0 main@%.04.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.17.i5_0 main@%.06.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.15.i6_1 main@%.15.i6_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.17.i5_1 main@%.17.i5_0))
                main@.lr.ph7_0)))
  (=> a!1
      (main@.lr.ph7 main@%_9_0
                    main@%_13_0
                    main@%_5_0
                    main@%.01.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.08.i.lcssa_1
                    main@%.17.i5_1
                    main@%_1_0
                    main@%_3_0
                    main@%.15.i6_1))))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_9_0
                               main@%_13_0
                               main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.06.i11_0
                               main@%.04.i12_0
                               main@%.0.i14_0
                               main@%.08.i10_0
                               main@%.01.i13_0)
                true
                (= main@%_31_0 (+ main@%_30_0 main@%_3_0))
                (= main@%_32_0 (+ main@%_31_0 main@%.04.i12_0))
                (= main@%_33_0 (+ main@%.06.i11_0 1))
                (= main@%_34_0 (+ main@%.0.i14_0 main@%.08.i10_0))
                (= main@%_35_0 (+ main@%.0.i14_0 main@%_9_0))
                (= main@%_36_0 (+ main@%.01.i13_0 1))
                (= main@%_37_0 (< main@%_36_0 main@%_13_0))
                (= main@%_38_0 (+ main@%.01.i13_0 2))
                (= main@%_39_0 (ite main@%_37_0 main@%_35_0 0))
                (= main@%.19.i_0 (+ main@%_34_0 main@%_39_0))
                (= main@%.12.i_0 (ite main@%_37_0 main@%_38_0 main@%_36_0))
                (= main@%_40_0 (ite main@%_37_0 main@%_9_0 0))
                (= main@%.1.i_0 (+ main@%_40_0 main@%_35_0))
                (= main@%_41_0 (< main@%_33_0 main@%_5_0))
                (= main@%_42_0 (< main@%.12.i_0 main@%_13_0))
                (= main@%_43_0 (ite main@%_41_0 main@%_42_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_43_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_0 main@%.19.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%_32_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_29_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_0 main@%.06.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_0 main@%.08.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_1 main@%.210.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.15.i.lcssa_1
        main@%.2.i4.us_1
        main@%.210.i2.us_1
        main@%_9_0
        main@%.23.i3.us_1
        main@%_13_0))))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_9_0
                               main@%_13_0
                               main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.06.i11_0
                               main@%.04.i12_0
                               main@%.0.i14_0
                               main@%.08.i10_0
                               main@%.01.i13_0)
                true
                (= main@%_31_0 (+ main@%_30_0 main@%_3_0))
                (= main@%_32_0 (+ main@%_31_0 main@%.04.i12_0))
                (= main@%_33_0 (+ main@%.06.i11_0 1))
                (= main@%_34_0 (+ main@%.0.i14_0 main@%.08.i10_0))
                (= main@%_35_0 (+ main@%.0.i14_0 main@%_9_0))
                (= main@%_36_0 (+ main@%.01.i13_0 1))
                (= main@%_37_0 (< main@%_36_0 main@%_13_0))
                (= main@%_38_0 (+ main@%.01.i13_0 2))
                (= main@%_39_0 (ite main@%_37_0 main@%_35_0 0))
                (= main@%.19.i_0 (+ main@%_34_0 main@%_39_0))
                (= main@%.12.i_0 (ite main@%_37_0 main@%_38_0 main@%_36_0))
                (= main@%_40_0 (ite main@%_37_0 main@%_9_0 0))
                (= main@%.1.i_0 (+ main@%_40_0 main@%_35_0))
                (= main@%_41_0 (< main@%_33_0 main@%_5_0))
                (= main@%_42_0 (< main@%.12.i_0 main@%_13_0))
                (= main@%_43_0 (ite main@%_41_0 main@%_42_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_43_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_0 main@%.19.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%_32_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.08.i.lcssa_1 main@%.08.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.06.i.lcssa_1 main@%.06.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_27_0 (>= main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader1_0
                    (= main@%_28_0 (< main@%.06.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_29_0 (ite main@%_28_0 main@%_27_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_29_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_0 main@%.06.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_1 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_0 main@%.08.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_1 main@%.210.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_56_0 (= main@%.15.i.lcssa_1 main@%.210.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_56_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph7 main@%_9_0
                       main@%_13_0
                       main@%_5_0
                       main@%.01.i.lcssa_0
                       main@%.0.i.lcssa_0
                       main@%.08.i.lcssa_0
                       main@%.17.i5_0
                       main@%_1_0
                       main@%_3_0
                       main@%.15.i6_0)
         true
         (= main@%_52_0 (+ main@%_51_0 main@%_3_0))
         (= main@%_53_0 (+ main@%_52_0 main@%.15.i6_0))
         (= main@%_54_0 (+ main@%.17.i5_0 1))
         (= main@%_55_0 (< main@%_54_0 main@%_5_0))
         (=> main@.lr.ph7_1 (and main@.lr.ph7_1 main@.lr.ph7_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0) main@%_55_0)
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0) (= main@%.15.i6_1 main@%_53_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0) (= main@%.17.i5_1 main@%_54_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
             (= main@%.15.i6_2 main@%.15.i6_1))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
             (= main@%.17.i5_2 main@%.17.i5_1))
         main@.lr.ph7_1)
    (main@.lr.ph7 main@%_9_0
                  main@%_13_0
                  main@%_5_0
                  main@%.01.i.lcssa_0
                  main@%.0.i.lcssa_0
                  main@%.08.i.lcssa_0
                  main@%.17.i5_2
                  main@%_1_0
                  main@%_3_0
                  main@%.15.i6_2)))
(rule (let ((a!1 (and (main@.lr.ph7 main@%_9_0
                              main@%_13_0
                              main@%_5_0
                              main@%.01.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.08.i.lcssa_0
                              main@%.17.i5_0
                              main@%_1_0
                              main@%_3_0
                              main@%.15.i6_0)
                true
                (= main@%_52_0 (+ main@%_51_0 main@%_3_0))
                (= main@%_53_0 (+ main@%_52_0 main@%.15.i6_0))
                (= main@%_54_0 (+ main@%.17.i5_0 1))
                (= main@%_55_0 (< main@%_54_0 main@%_5_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_55_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.17.i.lcssa_0 main@%_54_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.15.i.lcssa_0 main@%_53_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_0 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_0 main@%.08.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.210.i2.us_1 main@%.210.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.15.i.lcssa_1
        main@%.2.i4.us_1
        main@%.210.i2.us_1
        main@%_9_0
        main@%.23.i3.us_1
        main@%_13_0))))
(rule (let ((a!1 (and (main@.lr.ph7 main@%_9_0
                              main@%_13_0
                              main@%_5_0
                              main@%.01.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.08.i.lcssa_0
                              main@%.17.i5_0
                              main@%_1_0
                              main@%_3_0
                              main@%.15.i6_0)
                true
                (= main@%_52_0 (+ main@%_51_0 main@%_3_0))
                (= main@%_53_0 (+ main@%_52_0 main@%.15.i6_0))
                (= main@%_54_0 (+ main@%.17.i5_0 1))
                (= main@%_55_0 (< main@%_54_0 main@%_5_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_55_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.17.i.lcssa_0 main@%_54_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.15.i.lcssa_0 main@%_53_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.17.i.lcssa_1 main@%.17.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.15.i.lcssa_1 main@%.15.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_44_0 (>= main@%.17.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (< main@%.01.i.lcssa_0 main@%_13_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (ite main@%_44_0 main@%_45_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_0 main@%.08.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.210.i.lcssa_1 main@%.210.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_56_0 (= main@%.15.i.lcssa_1 main@%.210.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_56_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph.split.us
           main@%.15.i.lcssa_0
           main@%.2.i4.us_0
           main@%.210.i2.us_0
           main@%_9_0
           main@%.23.i3.us_0
           main@%_13_0)
         true
         (= main@%_47_0 (+ main@%.2.i4.us_0 main@%.210.i2.us_0))
         (= main@%_48_0 (+ main@%.2.i4.us_0 main@%_9_0))
         (= main@%_49_0 (+ main@%.23.i3.us_0 1))
         (= main@%_50_0 (< main@%_49_0 main@%_13_0))
         (=> main@.lr.ph.split.us_1
             (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0) main@%_50_0)
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.2.i4.us_1 main@%_48_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.23.i3.us_1 main@%_49_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.210.i2.us_1 main@%_47_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.2.i4.us_2 main@%.2.i4.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.23.i3.us_2 main@%.23.i3.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.210.i2.us_2 main@%.210.i2.us_1))
         main@.lr.ph.split.us_1)
    (main@.lr.ph.split.us
      main@%.15.i.lcssa_0
      main@%.2.i4.us_2
      main@%.210.i2.us_2
      main@%_9_0
      main@%.23.i3.us_2
      main@%_13_0)))
(rule (let ((a!1 (and (main@.lr.ph.split.us
                  main@%.15.i.lcssa_0
                  main@%.2.i4.us_0
                  main@%.210.i2.us_0
                  main@%_9_0
                  main@%.23.i3.us_0
                  main@%_13_0)
                true
                (= main@%_47_0 (+ main@%.2.i4.us_0 main@%.210.i2.us_0))
                (= main@%_48_0 (+ main@%.2.i4.us_0 main@%_9_0))
                (= main@%_49_0 (+ main@%.23.i3.us_0 1))
                (= main@%_50_0 (< main@%_49_0 main@%_13_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph.split.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (not main@%_50_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.210.i.lcssa_0 main@%_47_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.210.i.lcssa_1 main@%.210.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_56_0 (= main@%.15.i.lcssa_0 main@%.210.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_56_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

