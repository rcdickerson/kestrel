(set-info :original "./results/chc/bytecode/antonopoulos/count-loops/naumann.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph17 (Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph8 (Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph.split.us (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_49_0 Bool )
(declare-var main@%_37_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%_39_0 Int )
(declare-var main@%_40_0 Int )
(declare-var main@%_42_0 Bool )
(declare-var main@%_34_0 Bool )
(declare-var main@%_35_0 Bool )
(declare-var main@%_36_0 Bool )
(declare-var main@%.1.i4.us_2 Int )
(declare-var main@%.2.i3.us_2 Int )
(declare-var main@%.218.i2.us_2 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Bool )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%_48_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%.4.i7_2 Int )
(declare-var main@%.411.i6_2 Int )
(declare-var main@%.215.i5_2 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%_32_0 Bool )
(declare-var main@%_33_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%.0.i16_2 Int )
(declare-var main@%.01.i15_2 Int )
(declare-var main@%.03.i14_2 Int )
(declare-var main@%.07.i13_2 Int )
(declare-var main@%.016.i11_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@.lr.ph17_0 Bool )
(declare-var main@%.0.i16_0 Int )
(declare-var main@%.01.i15_0 Int )
(declare-var main@%.03.i14_0 Int )
(declare-var main@%.07.i13_0 Int )
(declare-var main@%.013.i12_0 Int )
(declare-var main@%.016.i11_0 Int )
(declare-var main@%.0.i16_1 Int )
(declare-var main@%.01.i15_1 Int )
(declare-var main@%.03.i14_1 Int )
(declare-var main@%.07.i13_1 Int )
(declare-var main@%.013.i12_1 Int )
(declare-var main@%.016.i11_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.016.i.lcssa_0 Int )
(declare-var main@%.013.i.lcssa_0 Int )
(declare-var main@%.07.i.lcssa_0 Int )
(declare-var main@%.03.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.016.i.lcssa_1 Int )
(declare-var main@%.013.i.lcssa_1 Int )
(declare-var main@%.07.i.lcssa_1 Int )
(declare-var main@%.03.i.lcssa_1 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@.lr.ph8_0 Bool )
(declare-var main@%.4.i7_0 Int )
(declare-var main@%.411.i6_0 Int )
(declare-var main@%.215.i5_0 Int )
(declare-var main@%.4.i7_1 Int )
(declare-var main@%.411.i6_1 Int )
(declare-var main@%.215.i5_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.411.i.lcssa_0 Int )
(declare-var main@%.4.i.lcssa_0 Int )
(declare-var main@%.411.i.lcssa_1 Int )
(declare-var main@%.4.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%.1.i4.us_0 Int )
(declare-var main@%.2.i3.us_0 Int )
(declare-var main@%.218.i2.us_0 Int )
(declare-var main@%.1.i4.us_1 Int )
(declare-var main@%.2.i3.us_1 Int )
(declare-var main@%.218.i2.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.2.i.lcssa_0 Int )
(declare-var main@%.2.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%.18.i_0 Int )
(declare-var main@%.14.i_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@_19_0 Bool )
(declare-var main@%.29.i_0 Int )
(declare-var main@%.25.i_0 Int )
(declare-var main@%_24_0 Int )
(declare-var main@_25_0 Bool )
(declare-var |tuple(main@.lr.ph17_0, main@_25_0)| Bool )
(declare-var main@%.114.i_0 Int )
(declare-var main@%.310.i_0 Int )
(declare-var main@%.36.i_0 Int )
(declare-var main@%.114.i_1 Int )
(declare-var main@%.310.i_1 Int )
(declare-var main@%.36.i_1 Int )
(declare-var main@%.114.i_2 Int )
(declare-var main@%.310.i_2 Int )
(declare-var main@%.36.i_2 Int )
(declare-var main@%.117.i_0 Int )
(declare-var main@%.12.i_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@.lr.ph17_1 Bool )
(declare-var main@%.013.i12_2 Int )
(declare-var main@%.512.i_0 Int )
(declare-var main@%.5.i_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@.lr.ph8_1 Bool )
(declare-var main@%.319.i.us_0 Int )
(declare-var main@%.3.i.us_0 Int )
(declare-var main@%_41_0 Int )
(declare-var main@.lr.ph.split.us_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (=> (and (main@entry @arb_int_0)
         true
         (= main@%_0_0 (= main@%loop.bound_0 4))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 4))
         main@%_1_0
         (= main@%_2_0 @arb_int_0)
         (= main@%_4_0 @arb_int_0)
         (= main@%_6_0 (= main@%_3_0 main@%_5_0))
         main@%_6_0
         (= main@%_7_0 (> main@%_3_0 4))
         (= main@%_8_0 (> main@%_5_0 4))
         (= main@%_9_0 (ite main@%_7_0 main@%_8_0 false))
         (=> main@.lr.ph17_0 (and main@.lr.ph17_0 main@entry_0))
         (=> (and main@.lr.ph17_0 main@entry_0) main@%_9_0)
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.0.i16_0 0))
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.01.i15_0 16))
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.03.i14_0 main@%_3_0))
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.07.i13_0 24))
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.013.i12_0 0))
         (=> (and main@.lr.ph17_0 main@entry_0) (= main@%.016.i11_0 main@%_5_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.0.i16_1 main@%.0.i16_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.01.i15_1 main@%.01.i15_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.03.i14_1 main@%.03.i14_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.07.i13_1 main@%.07.i13_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.013.i12_1 main@%.013.i12_0))
         (=> (and main@.lr.ph17_0 main@entry_0)
             (= main@%.016.i11_1 main@%.016.i11_0))
         main@.lr.ph17_0)
    (main@.lr.ph17 main@%loop.bound_0
                   main@%loop.bound1_0
                   main@%.0.i16_1
                   main@%.01.i15_1
                   main@%.016.i11_1
                   main@%.03.i14_1
                   main@%.07.i13_1
                   main@%.013.i12_1)))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 4))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 4))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 4))
                (= main@%_8_0 (> main@%_5_0 4))
                (= main@%_9_0 (ite main@%_7_0 main@%_8_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_9_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_0 main@%_5_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 24))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 main@%_3_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 16))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.lr.ph8_0 (and main@.lr.ph8_0 main@.preheader1_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0) main@%_12_0)
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.4.i7_0 main@%.03.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.411.i6_0 main@%.07.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.215.i5_0 main@%.013.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.4.i7_1 main@%.4.i7_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.411.i6_1 main@%.411.i6_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.215.i5_1 main@%.215.i5_0))
                main@.lr.ph8_0)))
  (=> a!1
      (main@.lr.ph8 main@%loop.bound_0
                    main@%.016.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.01.i.lcssa_1
                    main@%.215.i5_1
                    main@%.4.i7_1
                    main@%.411.i6_1
                    main@%loop.bound1_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 4))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 4))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 4))
                (= main@%_8_0 (> main@%_5_0 4))
                (= main@%_9_0 (ite main@%_7_0 main@%_8_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_9_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_0 main@%_5_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 24))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 main@%_3_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 16))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_12_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_1 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_36_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_0 main@%.016.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_1 main@%.1.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_1 main@%.2.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_1 main@%.218.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.411.i.lcssa_1
        main@%.1.i4.us_1
        main@%.2.i3.us_1
        main@%.218.i2.us_1
        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 4))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 4))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 4))
                (= main@%_8_0 (> main@%_5_0 4))
                (= main@%_9_0 (ite main@%_7_0 main@%_8_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_9_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_0 main@%_5_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 24))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 main@%_3_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 16))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_12_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_1 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_36_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_0 main@%.01.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_49_0 (> main@%.411.i.lcssa_1 main@%.2.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_49_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (=> main@_25_0
               (= main@%_31_0
                  (ite (>= main@%.36.i_2 0) (< 4 main@%.36.i_2) true))))
      (a!2 (=> main@_25_0
               (= main@%_32_0
                  (ite (>= main@%.117.i_0 0) (< 4 main@%.117.i_0) true)))))
(let ((a!3 (and (main@.lr.ph17 main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.0.i16_0
                               main@%.01.i15_0
                               main@%.016.i11_0
                               main@%.03.i14_0
                               main@%.07.i13_0
                               main@%.013.i12_0)
                true
                (= main@%_13_0 (mod main@%.013.i12_0 2))
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%_15_0 (ite main@%_14_0 main@%.03.i14_0 1))
                (= main@%_16_0 (ite main@%_14_0 (- 1) 0))
                (= main@%.14.i_0 (+ main@%.03.i14_0 main@%_16_0))
                (= main@%_17_0 (+ main@%.013.i12_0 1))
                (= main@%_18_0
                   (ite (>= main@%.14.i_0 0) (< 4 main@%.14.i_0) true))
                (=> main@_19_0 (and main@_19_0 main@.lr.ph17_0))
                (=> (and main@_19_0 main@.lr.ph17_0) main@%_18_0)
                (=> main@_19_0 (= main@%_20_0 (mod main@%_17_0 2)))
                (=> main@_19_0 (= main@%_21_0 (= main@%_20_0 0)))
                (=> main@_19_0
                    (= main@%_22_0 (ite main@%_21_0 main@%.14.i_0 1)))
                (=> main@_19_0 (= main@%_23_0 (ite main@%_21_0 (- 1) 0)))
                (=> main@_19_0 (= main@%.25.i_0 (+ main@%.14.i_0 main@%_23_0)))
                (=> main@_19_0 (= main@%_24_0 (+ main@%.013.i12_0 2)))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| main@.lr.ph17_0)
                (=> main@_25_0
                    (or (and main@_25_0 main@_19_0)
                        |tuple(main@.lr.ph17_0, main@_25_0)|))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (not main@%_18_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.114.i_0 main@%_24_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_0 main@%.29.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_0 main@%.25.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_1 main@%_17_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_1 main@%.18.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (= main@%.36.i_1 4))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.114.i_2 main@%.114.i_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_2 main@%.310.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_2 main@%.36.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_2 main@%.114.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_2 main@%.310.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.36.i_2 main@%.36.i_1))
                (=> main@_25_0 (= main@%_26_0 (rem main@%.0.i16_0 3)))
                (=> main@_25_0 (= main@%_27_0 (= main@%_26_0 0)))
                (=> main@_25_0 (= main@%_28_0 (* main@%.01.i15_0 2)))
                (=> main@_25_0 (= main@%_29_0 (ite main@%_27_0 (- 1) 0)))
                (=> main@_25_0
                    (= main@%.117.i_0 (+ main@%.016.i11_0 main@%_29_0)))
                (=> main@_25_0
                    (= main@%.12.i_0
                       (ite main@%_27_0 main@%_28_0 main@%.01.i15_0)))
                (=> main@_25_0 (= main@%_30_0 (+ main@%.0.i16_0 1)))
                a!1
                a!2
                (=> main@_25_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.lr.ph17_1 (and main@.lr.ph17_1 main@_25_0))
                (=> (and main@.lr.ph17_1 main@_25_0) main@%_33_0)
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.0.i16_1 main@%_30_0))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.01.i15_1 main@%.12.i_0))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.03.i14_1 main@%.36.i_2))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.07.i13_1 main@%.310.i_2))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.013.i12_1 main@%.114.i_2))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.016.i11_1 main@%.117.i_0))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.0.i16_2 main@%.0.i16_1))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.01.i15_2 main@%.01.i15_1))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.03.i14_2 main@%.03.i14_1))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.07.i13_2 main@%.07.i13_1))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.013.i12_2 main@%.013.i12_1))
                (=> (and main@.lr.ph17_1 main@_25_0)
                    (= main@%.016.i11_2 main@%.016.i11_1))
                main@.lr.ph17_1)))
  (=> a!3
      (main@.lr.ph17 main@%loop.bound_0
                     main@%loop.bound1_0
                     main@%.0.i16_2
                     main@%.01.i15_2
                     main@%.016.i11_2
                     main@%.03.i14_2
                     main@%.07.i13_2
                     main@%.013.i12_2)))))
(rule (let ((a!1 (=> main@_25_0
               (= main@%_31_0
                  (ite (>= main@%.36.i_2 0) (< 4 main@%.36.i_2) true))))
      (a!2 (=> main@_25_0
               (= main@%_32_0
                  (ite (>= main@%.117.i_0 0) (< 4 main@%.117.i_0) true)))))
(let ((a!3 (and (main@.lr.ph17 main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.0.i16_0
                               main@%.01.i15_0
                               main@%.016.i11_0
                               main@%.03.i14_0
                               main@%.07.i13_0
                               main@%.013.i12_0)
                true
                (= main@%_13_0 (mod main@%.013.i12_0 2))
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%_15_0 (ite main@%_14_0 main@%.03.i14_0 1))
                (= main@%_16_0 (ite main@%_14_0 (- 1) 0))
                (= main@%.14.i_0 (+ main@%.03.i14_0 main@%_16_0))
                (= main@%_17_0 (+ main@%.013.i12_0 1))
                (= main@%_18_0
                   (ite (>= main@%.14.i_0 0) (< 4 main@%.14.i_0) true))
                (=> main@_19_0 (and main@_19_0 main@.lr.ph17_0))
                (=> (and main@_19_0 main@.lr.ph17_0) main@%_18_0)
                (=> main@_19_0 (= main@%_20_0 (mod main@%_17_0 2)))
                (=> main@_19_0 (= main@%_21_0 (= main@%_20_0 0)))
                (=> main@_19_0
                    (= main@%_22_0 (ite main@%_21_0 main@%.14.i_0 1)))
                (=> main@_19_0 (= main@%_23_0 (ite main@%_21_0 (- 1) 0)))
                (=> main@_19_0 (= main@%.25.i_0 (+ main@%.14.i_0 main@%_23_0)))
                (=> main@_19_0 (= main@%_24_0 (+ main@%.013.i12_0 2)))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| main@.lr.ph17_0)
                (=> main@_25_0
                    (or (and main@_25_0 main@_19_0)
                        |tuple(main@.lr.ph17_0, main@_25_0)|))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (not main@%_18_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.114.i_0 main@%_24_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_0 main@%.29.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_0 main@%.25.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_1 main@%_17_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_1 main@%.18.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (= main@%.36.i_1 4))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.114.i_2 main@%.114.i_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_2 main@%.310.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_2 main@%.36.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_2 main@%.114.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_2 main@%.310.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.36.i_2 main@%.36.i_1))
                (=> main@_25_0 (= main@%_26_0 (rem main@%.0.i16_0 3)))
                (=> main@_25_0 (= main@%_27_0 (= main@%_26_0 0)))
                (=> main@_25_0 (= main@%_28_0 (* main@%.01.i15_0 2)))
                (=> main@_25_0 (= main@%_29_0 (ite main@%_27_0 (- 1) 0)))
                (=> main@_25_0
                    (= main@%.117.i_0 (+ main@%.016.i11_0 main@%_29_0)))
                (=> main@_25_0
                    (= main@%.12.i_0
                       (ite main@%_27_0 main@%_28_0 main@%.01.i15_0)))
                (=> main@_25_0 (= main@%_30_0 (+ main@%.0.i16_0 1)))
                a!1
                a!2
                (=> main@_25_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_25_0))
                (=> (and main@.preheader1_0 main@_25_0) (not main@%_33_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_0 main@%.117.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_0 main@%.114.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_0 main@%.310.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_0 main@%.36.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_0 main@%_30_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.lr.ph8_0 (and main@.lr.ph8_0 main@.preheader1_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0) main@%_12_0)
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.4.i7_0 main@%.03.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.411.i6_0 main@%.07.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.215.i5_0 main@%.013.i.lcssa_1))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.4.i7_1 main@%.4.i7_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.411.i6_1 main@%.411.i6_0))
                (=> (and main@.lr.ph8_0 main@.preheader1_0)
                    (= main@%.215.i5_1 main@%.215.i5_0))
                main@.lr.ph8_0)))
  (=> a!3
      (main@.lr.ph8 main@%loop.bound_0
                    main@%.016.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.01.i.lcssa_1
                    main@%.215.i5_1
                    main@%.4.i7_1
                    main@%.411.i6_1
                    main@%loop.bound1_0)))))
(rule (let ((a!1 (=> main@_25_0
               (= main@%_31_0
                  (ite (>= main@%.36.i_2 0) (< 4 main@%.36.i_2) true))))
      (a!2 (=> main@_25_0
               (= main@%_32_0
                  (ite (>= main@%.117.i_0 0) (< 4 main@%.117.i_0) true)))))
(let ((a!3 (and (main@.lr.ph17 main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.0.i16_0
                               main@%.01.i15_0
                               main@%.016.i11_0
                               main@%.03.i14_0
                               main@%.07.i13_0
                               main@%.013.i12_0)
                true
                (= main@%_13_0 (mod main@%.013.i12_0 2))
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%_15_0 (ite main@%_14_0 main@%.03.i14_0 1))
                (= main@%_16_0 (ite main@%_14_0 (- 1) 0))
                (= main@%.14.i_0 (+ main@%.03.i14_0 main@%_16_0))
                (= main@%_17_0 (+ main@%.013.i12_0 1))
                (= main@%_18_0
                   (ite (>= main@%.14.i_0 0) (< 4 main@%.14.i_0) true))
                (=> main@_19_0 (and main@_19_0 main@.lr.ph17_0))
                (=> (and main@_19_0 main@.lr.ph17_0) main@%_18_0)
                (=> main@_19_0 (= main@%_20_0 (mod main@%_17_0 2)))
                (=> main@_19_0 (= main@%_21_0 (= main@%_20_0 0)))
                (=> main@_19_0
                    (= main@%_22_0 (ite main@%_21_0 main@%.14.i_0 1)))
                (=> main@_19_0 (= main@%_23_0 (ite main@%_21_0 (- 1) 0)))
                (=> main@_19_0 (= main@%.25.i_0 (+ main@%.14.i_0 main@%_23_0)))
                (=> main@_19_0 (= main@%_24_0 (+ main@%.013.i12_0 2)))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| main@.lr.ph17_0)
                (=> main@_25_0
                    (or (and main@_25_0 main@_19_0)
                        |tuple(main@.lr.ph17_0, main@_25_0)|))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (not main@%_18_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.114.i_0 main@%_24_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_0 main@%.29.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_0 main@%.25.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_1 main@%_17_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_1 main@%.18.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (= main@%.36.i_1 4))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.114.i_2 main@%.114.i_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_2 main@%.310.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_2 main@%.36.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_2 main@%.114.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_2 main@%.310.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.36.i_2 main@%.36.i_1))
                (=> main@_25_0 (= main@%_26_0 (rem main@%.0.i16_0 3)))
                (=> main@_25_0 (= main@%_27_0 (= main@%_26_0 0)))
                (=> main@_25_0 (= main@%_28_0 (* main@%.01.i15_0 2)))
                (=> main@_25_0 (= main@%_29_0 (ite main@%_27_0 (- 1) 0)))
                (=> main@_25_0
                    (= main@%.117.i_0 (+ main@%.016.i11_0 main@%_29_0)))
                (=> main@_25_0
                    (= main@%.12.i_0
                       (ite main@%_27_0 main@%_28_0 main@%.01.i15_0)))
                (=> main@_25_0 (= main@%_30_0 (+ main@%.0.i16_0 1)))
                a!1
                a!2
                (=> main@_25_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_25_0))
                (=> (and main@.preheader1_0 main@_25_0) (not main@%_33_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_0 main@%.117.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_0 main@%.114.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_0 main@%.310.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_0 main@%.36.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_0 main@%_30_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_12_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_1 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_36_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_0 main@%.016.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_1 main@%.1.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_1 main@%.2.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_1 main@%.218.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!3
      (main@.lr.ph.split.us
        main@%.411.i.lcssa_1
        main@%.1.i4.us_1
        main@%.2.i3.us_1
        main@%.218.i2.us_1
        main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@_25_0
               (= main@%_31_0
                  (ite (>= main@%.36.i_2 0) (< 4 main@%.36.i_2) true))))
      (a!2 (=> main@_25_0
               (= main@%_32_0
                  (ite (>= main@%.117.i_0 0) (< 4 main@%.117.i_0) true)))))
(let ((a!3 (and (main@.lr.ph17 main@%loop.bound_0
                               main@%loop.bound1_0
                               main@%.0.i16_0
                               main@%.01.i15_0
                               main@%.016.i11_0
                               main@%.03.i14_0
                               main@%.07.i13_0
                               main@%.013.i12_0)
                true
                (= main@%_13_0 (mod main@%.013.i12_0 2))
                (= main@%_14_0 (= main@%_13_0 0))
                (= main@%_15_0 (ite main@%_14_0 main@%.03.i14_0 1))
                (= main@%_16_0 (ite main@%_14_0 (- 1) 0))
                (= main@%.14.i_0 (+ main@%.03.i14_0 main@%_16_0))
                (= main@%_17_0 (+ main@%.013.i12_0 1))
                (= main@%_18_0
                   (ite (>= main@%.14.i_0 0) (< 4 main@%.14.i_0) true))
                (=> main@_19_0 (and main@_19_0 main@.lr.ph17_0))
                (=> (and main@_19_0 main@.lr.ph17_0) main@%_18_0)
                (=> main@_19_0 (= main@%_20_0 (mod main@%_17_0 2)))
                (=> main@_19_0 (= main@%_21_0 (= main@%_20_0 0)))
                (=> main@_19_0
                    (= main@%_22_0 (ite main@%_21_0 main@%.14.i_0 1)))
                (=> main@_19_0 (= main@%_23_0 (ite main@%_21_0 (- 1) 0)))
                (=> main@_19_0 (= main@%.25.i_0 (+ main@%.14.i_0 main@%_23_0)))
                (=> main@_19_0 (= main@%_24_0 (+ main@%.013.i12_0 2)))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| main@.lr.ph17_0)
                (=> main@_25_0
                    (or (and main@_25_0 main@_19_0)
                        |tuple(main@.lr.ph17_0, main@_25_0)|))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (not main@%_18_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.114.i_0 main@%_24_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_0 main@%.29.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_0 main@%.25.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_1 main@%_17_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_1 main@%.18.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)| (= main@%.36.i_1 4))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.114.i_2 main@%.114.i_0))
                (=> (and main@_25_0 main@_19_0)
                    (= main@%.310.i_2 main@%.310.i_0))
                (=> (and main@_25_0 main@_19_0) (= main@%.36.i_2 main@%.36.i_0))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.114.i_2 main@%.114.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.310.i_2 main@%.310.i_1))
                (=> |tuple(main@.lr.ph17_0, main@_25_0)|
                    (= main@%.36.i_2 main@%.36.i_1))
                (=> main@_25_0 (= main@%_26_0 (rem main@%.0.i16_0 3)))
                (=> main@_25_0 (= main@%_27_0 (= main@%_26_0 0)))
                (=> main@_25_0 (= main@%_28_0 (* main@%.01.i15_0 2)))
                (=> main@_25_0 (= main@%_29_0 (ite main@%_27_0 (- 1) 0)))
                (=> main@_25_0
                    (= main@%.117.i_0 (+ main@%.016.i11_0 main@%_29_0)))
                (=> main@_25_0
                    (= main@%.12.i_0
                       (ite main@%_27_0 main@%_28_0 main@%.01.i15_0)))
                (=> main@_25_0 (= main@%_30_0 (+ main@%.0.i16_0 1)))
                a!1
                a!2
                (=> main@_25_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@_25_0))
                (=> (and main@.preheader1_0 main@_25_0) (not main@%_33_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_0 main@%.117.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_0 main@%.114.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_0 main@%.310.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_0 main@%.36.i_2))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_0 main@%_30_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.016.i.lcssa_1 main@%.016.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.013.i.lcssa_1 main@%.013.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@_25_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_10_0 (< main@%.016.i.lcssa_1 5)))
                (=> main@.preheader1_0
                    (= main@%_11_0 (> main@%.03.i.lcssa_1 4)))
                (=> main@.preheader1_0
                    (= main@%_12_0 (ite main@%_11_0 main@%_10_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_12_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_1 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_36_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_0 main@%.01.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_49_0 (> main@%.411.i.lcssa_1 main@%.2.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_49_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!3 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_48_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        true)
                   (ite (< main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        false)))))
  (=> (and (main@.lr.ph8 main@%loop.bound_0
                         main@%.016.i.lcssa_0
                         main@%.0.i.lcssa_0
                         main@%.01.i.lcssa_0
                         main@%.215.i5_0
                         main@%.4.i7_0
                         main@%.411.i6_0
                         main@%loop.bound1_0)
           true
           (= main@%_43_0 (mod main@%.215.i5_0 2))
           (= main@%_44_0 (= main@%_43_0 0))
           (= main@%_45_0 (ite main@%_44_0 main@%.4.i7_0 1))
           (= main@%_46_0 (ite main@%_44_0 (- 1) 0))
           (= main@%.5.i_0 (+ main@%.4.i7_0 main@%_46_0))
           (= main@%_47_0 (+ main@%.215.i5_0 1))
           a!1
           (=> main@.lr.ph8_1 (and main@.lr.ph8_1 main@.lr.ph8_0))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0) main@%_48_0)
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.4.i7_1 main@%.5.i_0))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.411.i6_1 main@%.512.i_0))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.215.i5_1 main@%_47_0))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.4.i7_2 main@%.4.i7_1))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.411.i6_2 main@%.411.i6_1))
           (=> (and main@.lr.ph8_1 main@.lr.ph8_0)
               (= main@%.215.i5_2 main@%.215.i5_1))
           main@.lr.ph8_1)
      (main@.lr.ph8 main@%loop.bound_0
                    main@%.016.i.lcssa_0
                    main@%.0.i.lcssa_0
                    main@%.01.i.lcssa_0
                    main@%.215.i5_2
                    main@%.4.i7_2
                    main@%.411.i6_2
                    main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_48_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        true)
                   (ite (< main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph8 main@%loop.bound_0
                              main@%.016.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.01.i.lcssa_0
                              main@%.215.i5_0
                              main@%.4.i7_0
                              main@%.411.i6_0
                              main@%loop.bound1_0)
                true
                (= main@%_43_0 (mod main@%.215.i5_0 2))
                (= main@%_44_0 (= main@%_43_0 0))
                (= main@%_45_0 (ite main@%_44_0 main@%.4.i7_0 1))
                (= main@%_46_0 (ite main@%_44_0 (- 1) 0))
                (= main@%.5.i_0 (+ main@%.4.i7_0 main@%_46_0))
                (= main@%_47_0 (+ main@%.215.i5_0 1))
                a!1
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph8_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0) (not main@%_48_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.411.i.lcssa_0 main@%.512.i_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.4.i.lcssa_0 4))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_0 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_36_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_0 main@%.0.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_0 main@%.01.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_0 main@%.016.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i4.us_1 main@%.1.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i3.us_1 main@%.2.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.218.i2.us_1 main@%.218.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!2
      (main@.lr.ph.split.us
        main@%.411.i.lcssa_1
        main@%.1.i4.us_1
        main@%.2.i3.us_1
        main@%.218.i2.us_1
        main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_48_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        true)
                   (ite (< main@%.5.i_0 0)
                        (< main@%loop.bound1_0 main@%.5.i_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph8 main@%loop.bound_0
                              main@%.016.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.01.i.lcssa_0
                              main@%.215.i5_0
                              main@%.4.i7_0
                              main@%.411.i6_0
                              main@%loop.bound1_0)
                true
                (= main@%_43_0 (mod main@%.215.i5_0 2))
                (= main@%_44_0 (= main@%_43_0 0))
                (= main@%_45_0 (ite main@%_44_0 main@%.4.i7_0 1))
                (= main@%_46_0 (ite main@%_44_0 (- 1) 0))
                (= main@%.5.i_0 (+ main@%.4.i7_0 main@%_46_0))
                (= main@%_47_0 (+ main@%.215.i5_0 1))
                a!1
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph8_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0) (not main@%_48_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.411.i.lcssa_0 main@%.512.i_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.4.i.lcssa_0 4))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.411.i.lcssa_1 main@%.411.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph8_0)
                    (= main@%.4.i.lcssa_1 main@%.4.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_34_0 (< main@%.4.i.lcssa_1 5)))
                (=> main@.preheader_0
                    (= main@%_35_0 (> main@%.016.i.lcssa_0 4)))
                (=> main@.preheader_0
                    (= main@%_36_0 (ite main@%_34_0 main@%_35_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_36_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_0 main@%.01.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_49_0 (> main@%.411.i.lcssa_1 main@%.2.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_49_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!2 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_42_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.319.i.us_0 0)
                        (< main@%loop.bound_0 main@%.319.i.us_0)
                        true)
                   (ite (< main@%.319.i.us_0 0)
                        (< main@%loop.bound_0 main@%.319.i.us_0)
                        false)))))
  (=> (and (main@.lr.ph.split.us
             main@%.411.i.lcssa_0
             main@%.1.i4.us_0
             main@%.2.i3.us_0
             main@%.218.i2.us_0
             main@%loop.bound_0)
           true
           (= main@%_37_0 (rem main@%.1.i4.us_0 3))
           (= main@%_38_0 (= main@%_37_0 0))
           (= main@%_39_0 (* main@%.2.i3.us_0 2))
           (= main@%_40_0 (ite main@%_38_0 (- 1) 0))
           (= main@%.319.i.us_0 (+ main@%.218.i2.us_0 main@%_40_0))
           (= main@%.3.i.us_0 (ite main@%_38_0 main@%_39_0 main@%.2.i3.us_0))
           (= main@%_41_0 (+ main@%.1.i4.us_0 1))
           a!1
           (=> main@.lr.ph.split.us_1
               (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0) main@%_42_0)
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.1.i4.us_1 main@%_41_0))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.2.i3.us_1 main@%.3.i.us_0))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.218.i2.us_1 main@%.319.i.us_0))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.1.i4.us_2 main@%.1.i4.us_1))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.2.i3.us_2 main@%.2.i3.us_1))
           (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
               (= main@%.218.i2.us_2 main@%.218.i2.us_1))
           main@.lr.ph.split.us_1)
      (main@.lr.ph.split.us
        main@%.411.i.lcssa_0
        main@%.1.i4.us_2
        main@%.2.i3.us_2
        main@%.218.i2.us_2
        main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_42_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.319.i.us_0 0)
                        (< main@%loop.bound_0 main@%.319.i.us_0)
                        true)
                   (ite (< main@%.319.i.us_0 0)
                        (< main@%loop.bound_0 main@%.319.i.us_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph.split.us
                  main@%.411.i.lcssa_0
                  main@%.1.i4.us_0
                  main@%.2.i3.us_0
                  main@%.218.i2.us_0
                  main@%loop.bound_0)
                true
                (= main@%_37_0 (rem main@%.1.i4.us_0 3))
                (= main@%_38_0 (= main@%_37_0 0))
                (= main@%_39_0 (* main@%.2.i3.us_0 2))
                (= main@%_40_0 (ite main@%_38_0 (- 1) 0))
                (= main@%.319.i.us_0 (+ main@%.218.i2.us_0 main@%_40_0))
                (= main@%.3.i.us_0
                   (ite main@%_38_0 main@%_39_0 main@%.2.i3.us_0))
                (= main@%_41_0 (+ main@%.1.i4.us_0 1))
                a!1
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph.split.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (not main@%_42_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.2.i.lcssa_0 main@%.3.i.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_49_0 (> main@%.411.i.lcssa_0 main@%.2.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_49_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!2 main@verifier.error.split))))
(query main@verifier.error.split)

