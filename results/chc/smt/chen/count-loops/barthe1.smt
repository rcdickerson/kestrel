(set-info :original "./results/chc/bytecode/chen/count-loops/barthe1.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph15 (Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph7 (Int Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph.split.us (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_43_0 Bool )
(declare-var main@%_37_0 Bool )
(declare-var main@%_31_0 Bool )
(declare-var main@%_32_0 Bool )
(declare-var main@%_33_0 Bool )
(declare-var main@%.2.i4.us_2 Int )
(declare-var main@%.23.i3.us_2 Int )
(declare-var main@%.26.i2.us_2 Int )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%_42_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@%_16_0 Bool )
(declare-var main@%.18.i6_2 Int )
(declare-var main@%.110.i5_2 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%_29_0 Bool )
(declare-var main@%_30_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%_13_0 Bool )
(declare-var main@%.0.i14_2 Int )
(declare-var main@%.01.i13_2 Int )
(declare-var main@%.04.i12_2 Int )
(declare-var main@%.07.i11_2 Int )
(declare-var main@%.09.i10_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@.lr.ph15_0 Bool )
(declare-var main@%.0.i14_0 Int )
(declare-var main@%.01.i13_0 Int )
(declare-var main@%.04.i12_0 Int )
(declare-var main@%.07.i11_0 Int )
(declare-var main@%.09.i10_0 Int )
(declare-var main@%.0.i14_1 Int )
(declare-var main@%.01.i13_1 Int )
(declare-var main@%.04.i12_1 Int )
(declare-var main@%.07.i11_1 Int )
(declare-var main@%.09.i10_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.09.i.lcssa_0 Int )
(declare-var main@%.07.i.lcssa_0 Int )
(declare-var main@%.04.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.09.i.lcssa_1 Int )
(declare-var main@%.07.i.lcssa_1 Int )
(declare-var main@%.04.i.lcssa_1 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@.lr.ph7_0 Bool )
(declare-var main@%.18.i6_0 Int )
(declare-var main@%.110.i5_0 Int )
(declare-var main@%.18.i6_1 Int )
(declare-var main@%.110.i5_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.110.i.lcssa_0 Int )
(declare-var main@%.18.i.lcssa_0 Int )
(declare-var main@%.110.i.lcssa_1 Int )
(declare-var main@%.18.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%.2.i4.us_0 Int )
(declare-var main@%.23.i3.us_0 Int )
(declare-var main@%.26.i2.us_0 Int )
(declare-var main@%.2.i4.us_1 Int )
(declare-var main@%.23.i3.us_1 Int )
(declare-var main@%.26.i2.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.26.i.lcssa_0 Int )
(declare-var main@%.26.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%.15.i_0 Int )
(declare-var main@%.12.i_0 Int )
(declare-var main@%.1.i_0 Int )
(declare-var main@.lr.ph15_1 Bool )
(declare-var main@%_40_0 Int )
(declare-var main@%_41_0 Int )
(declare-var main@.lr.ph7_1 Bool )
(declare-var main@%_34_0 Int )
(declare-var main@%_35_0 Int )
(declare-var main@%_36_0 Int )
(declare-var main@.lr.ph.split.us_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (=> (and (main@entry @arb_int_0)
         true
         (= main@%_0_0 @arb_int_0)
         (= main@%_2_0 @arb_int_0)
         (= main@%_4_0 @arb_int_0)
         (= main@%_6_0 @arb_int_0)
         (= main@%_8_0 (= main@%_1_0 main@%_5_0))
         (= main@%_9_0 (= main@%_3_0 main@%_7_0))
         (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
         main@%_10_0
         (= main@%_11_0 (> main@%_1_0 0))
         (= main@%_12_0 (> main@%_5_0 0))
         (= main@%_13_0 (ite main@%_11_0 main@%_12_0 false))
         (=> main@.lr.ph15_0 (and main@.lr.ph15_0 main@entry_0))
         (=> (and main@.lr.ph15_0 main@entry_0) main@%_13_0)
         (=> (and main@.lr.ph15_0 main@entry_0) (= main@%.0.i14_0 main@%_7_0))
         (=> (and main@.lr.ph15_0 main@entry_0) (= main@%.01.i13_0 0))
         (=> (and main@.lr.ph15_0 main@entry_0) (= main@%.04.i12_0 0))
         (=> (and main@.lr.ph15_0 main@entry_0) (= main@%.07.i11_0 0))
         (=> (and main@.lr.ph15_0 main@entry_0) (= main@%.09.i10_0 0))
         (=> (and main@.lr.ph15_0 main@entry_0)
             (= main@%.0.i14_1 main@%.0.i14_0))
         (=> (and main@.lr.ph15_0 main@entry_0)
             (= main@%.01.i13_1 main@%.01.i13_0))
         (=> (and main@.lr.ph15_0 main@entry_0)
             (= main@%.04.i12_1 main@%.04.i12_0))
         (=> (and main@.lr.ph15_0 main@entry_0)
             (= main@%.07.i11_1 main@%.07.i11_0))
         (=> (and main@.lr.ph15_0 main@entry_0)
             (= main@%.09.i10_1 main@%.09.i10_0))
         main@.lr.ph15_0)
    (main@.lr.ph15 main@%_5_0
                   main@%_1_0
                   main@%_3_0
                   main@%.09.i10_1
                   main@%.07.i11_1
                   main@%.0.i14_1
                   main@%.04.i12_1
                   main@%.01.i13_1)))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (= main@%_9_0 (= main@%_3_0 main@%_7_0))
                (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
                main@%_10_0
                (= main@%_11_0 (> main@%_1_0 0))
                (= main@%_12_0 (> main@%_5_0 0))
                (= main@%_13_0 (ite main@%_11_0 main@%_12_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_13_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@.preheader1_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0) main@%_16_0)
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.18.i6_0 main@%.07.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.110.i5_0 main@%.09.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.18.i6_1 main@%.18.i6_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.110.i5_1 main@%.110.i5_0))
                main@.lr.ph7_0)))
  (=> a!1
      (main@.lr.ph7 main@%_5_0
                    main@%_1_0
                    main@%.01.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.04.i.lcssa_1
                    main@%.110.i5_1
                    main@%_3_0
                    main@%.18.i6_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (= main@%_9_0 (= main@%_3_0 main@%_7_0))
                (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
                main@%_10_0
                (= main@%_11_0 (> main@%_1_0 0))
                (= main@%_12_0 (> main@%_5_0 0))
                (= main@%_13_0 (ite main@%_11_0 main@%_12_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_13_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_0 main@%.09.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_33_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_0 main@%.04.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_1 main@%.26.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.18.i.lcssa_1
        main@%.2.i4.us_1
        main@%.26.i2.us_1
        main@%.23.i3.us_1
        main@%_5_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (= main@%_9_0 (= main@%_3_0 main@%_7_0))
                (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
                main@%_10_0
                (= main@%_11_0 (> main@%_1_0 0))
                (= main@%_12_0 (> main@%_5_0 0))
                (= main@%_13_0 (ite main@%_11_0 main@%_12_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_13_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_0 main@%.09.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_33_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_1 main@%.26.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_43_0 (= main@%.18.i.lcssa_1 main@%.26.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_43_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph15 main@%_5_0
                        main@%_1_0
                        main@%_3_0
                        main@%.09.i10_0
                        main@%.07.i11_0
                        main@%.0.i14_0
                        main@%.04.i12_0
                        main@%.01.i13_0)
         true
         (= main@%_17_0 (* main@%.09.i10_0 5))
         (= main@%_18_0 (+ main@%_17_0 main@%_3_0))
         (= main@%_19_0 (+ main@%_18_0 main@%.07.i11_0))
         (= main@%_20_0 (+ main@%.09.i10_0 1))
         (= main@%_21_0 (+ main@%.0.i14_0 main@%.04.i12_0))
         (= main@%_22_0 (+ main@%.0.i14_0 5))
         (= main@%_23_0 (+ main@%.01.i13_0 1))
         (= main@%_24_0 (< main@%_23_0 main@%_5_0))
         (= main@%_25_0 (+ main@%.0.i14_0 10))
         (= main@%_26_0 (+ main@%.01.i13_0 2))
         (= main@%_27_0 (ite main@%_24_0 main@%_22_0 0))
         (= main@%.15.i_0 (+ main@%_21_0 main@%_27_0))
         (= main@%.12.i_0 (ite main@%_24_0 main@%_26_0 main@%_23_0))
         (= main@%.1.i_0 (ite main@%_24_0 main@%_25_0 main@%_22_0))
         (= main@%_28_0 (< main@%_20_0 main@%_1_0))
         (= main@%_29_0 (< main@%.12.i_0 main@%_5_0))
         (= main@%_30_0 (ite main@%_28_0 main@%_29_0 false))
         (=> main@.lr.ph15_1 (and main@.lr.ph15_1 main@.lr.ph15_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0) main@%_30_0)
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.0.i14_1 main@%.1.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.01.i13_1 main@%.12.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.04.i12_1 main@%.15.i_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.07.i11_1 main@%_19_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.09.i10_1 main@%_20_0))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.0.i14_2 main@%.0.i14_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.01.i13_2 main@%.01.i13_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.04.i12_2 main@%.04.i12_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.07.i11_2 main@%.07.i11_1))
         (=> (and main@.lr.ph15_1 main@.lr.ph15_0)
             (= main@%.09.i10_2 main@%.09.i10_1))
         main@.lr.ph15_1)
    (main@.lr.ph15 main@%_5_0
                   main@%_1_0
                   main@%_3_0
                   main@%.09.i10_2
                   main@%.07.i11_2
                   main@%.0.i14_2
                   main@%.04.i12_2
                   main@%.01.i13_2)))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.09.i10_0
                               main@%.07.i11_0
                               main@%.0.i14_0
                               main@%.04.i12_0
                               main@%.01.i13_0)
                true
                (= main@%_17_0 (* main@%.09.i10_0 5))
                (= main@%_18_0 (+ main@%_17_0 main@%_3_0))
                (= main@%_19_0 (+ main@%_18_0 main@%.07.i11_0))
                (= main@%_20_0 (+ main@%.09.i10_0 1))
                (= main@%_21_0 (+ main@%.0.i14_0 main@%.04.i12_0))
                (= main@%_22_0 (+ main@%.0.i14_0 5))
                (= main@%_23_0 (+ main@%.01.i13_0 1))
                (= main@%_24_0 (< main@%_23_0 main@%_5_0))
                (= main@%_25_0 (+ main@%.0.i14_0 10))
                (= main@%_26_0 (+ main@%.01.i13_0 2))
                (= main@%_27_0 (ite main@%_24_0 main@%_22_0 0))
                (= main@%.15.i_0 (+ main@%_21_0 main@%_27_0))
                (= main@%.12.i_0 (ite main@%_24_0 main@%_26_0 main@%_23_0))
                (= main@%.1.i_0 (ite main@%_24_0 main@%_25_0 main@%_22_0))
                (= main@%_28_0 (< main@%_20_0 main@%_1_0))
                (= main@%_29_0 (< main@%.12.i_0 main@%_5_0))
                (= main@%_30_0 (ite main@%_28_0 main@%_29_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_30_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%.15.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@.preheader1_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0) main@%_16_0)
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.18.i6_0 main@%.07.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.110.i5_0 main@%.09.i.lcssa_1))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.18.i6_1 main@%.18.i6_0))
                (=> (and main@.lr.ph7_0 main@.preheader1_0)
                    (= main@%.110.i5_1 main@%.110.i5_0))
                main@.lr.ph7_0)))
  (=> a!1
      (main@.lr.ph7 main@%_5_0
                    main@%_1_0
                    main@%.01.i.lcssa_1
                    main@%.0.i.lcssa_1
                    main@%.04.i.lcssa_1
                    main@%.110.i5_1
                    main@%_3_0
                    main@%.18.i6_1))))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.09.i10_0
                               main@%.07.i11_0
                               main@%.0.i14_0
                               main@%.04.i12_0
                               main@%.01.i13_0)
                true
                (= main@%_17_0 (* main@%.09.i10_0 5))
                (= main@%_18_0 (+ main@%_17_0 main@%_3_0))
                (= main@%_19_0 (+ main@%_18_0 main@%.07.i11_0))
                (= main@%_20_0 (+ main@%.09.i10_0 1))
                (= main@%_21_0 (+ main@%.0.i14_0 main@%.04.i12_0))
                (= main@%_22_0 (+ main@%.0.i14_0 5))
                (= main@%_23_0 (+ main@%.01.i13_0 1))
                (= main@%_24_0 (< main@%_23_0 main@%_5_0))
                (= main@%_25_0 (+ main@%.0.i14_0 10))
                (= main@%_26_0 (+ main@%.01.i13_0 2))
                (= main@%_27_0 (ite main@%_24_0 main@%_22_0 0))
                (= main@%.15.i_0 (+ main@%_21_0 main@%_27_0))
                (= main@%.12.i_0 (ite main@%_24_0 main@%_26_0 main@%_23_0))
                (= main@%.1.i_0 (ite main@%_24_0 main@%_25_0 main@%_22_0))
                (= main@%_28_0 (< main@%_20_0 main@%_1_0))
                (= main@%_29_0 (< main@%.12.i_0 main@%_5_0))
                (= main@%_30_0 (ite main@%_28_0 main@%_29_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_30_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%.15.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_0 main@%.09.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_33_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_0 main@%.04.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_1 main@%.26.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.18.i.lcssa_1
        main@%.2.i4.us_1
        main@%.26.i2.us_1
        main@%.23.i3.us_1
        main@%_5_0))))
(rule (let ((a!1 (and (main@.lr.ph15 main@%_5_0
                               main@%_1_0
                               main@%_3_0
                               main@%.09.i10_0
                               main@%.07.i11_0
                               main@%.0.i14_0
                               main@%.04.i12_0
                               main@%.01.i13_0)
                true
                (= main@%_17_0 (* main@%.09.i10_0 5))
                (= main@%_18_0 (+ main@%_17_0 main@%_3_0))
                (= main@%_19_0 (+ main@%_18_0 main@%.07.i11_0))
                (= main@%_20_0 (+ main@%.09.i10_0 1))
                (= main@%_21_0 (+ main@%.0.i14_0 main@%.04.i12_0))
                (= main@%_22_0 (+ main@%.0.i14_0 5))
                (= main@%_23_0 (+ main@%.01.i13_0 1))
                (= main@%_24_0 (< main@%_23_0 main@%_5_0))
                (= main@%_25_0 (+ main@%.0.i14_0 10))
                (= main@%_26_0 (+ main@%.01.i13_0 2))
                (= main@%_27_0 (ite main@%_24_0 main@%_22_0 0))
                (= main@%.15.i_0 (+ main@%_21_0 main@%_27_0))
                (= main@%.12.i_0 (ite main@%_24_0 main@%_26_0 main@%_23_0))
                (= main@%.1.i_0 (ite main@%_24_0 main@%_25_0 main@%_22_0))
                (= main@%_28_0 (< main@%_20_0 main@%_1_0))
                (= main@%_29_0 (< main@%.12.i_0 main@%_5_0))
                (= main@%_30_0 (ite main@%_28_0 main@%_29_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph15_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0) (not main@%_30_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_0 main@%.15.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_0 main@%.12.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_0 main@%.1.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.09.i.lcssa_1 main@%.09.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.07.i.lcssa_1 main@%.07.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph15_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_14_0 (>= main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader1_0
                    (= main@%_15_0 (< main@%.09.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_16_0 (ite main@%_15_0 main@%_14_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_0 main@%.09.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_0 main@%.07.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_1 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_33_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_0 main@%.04.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_1 main@%.26.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_43_0 (= main@%.18.i.lcssa_1 main@%.26.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_43_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph7 main@%_5_0
                       main@%_1_0
                       main@%.01.i.lcssa_0
                       main@%.0.i.lcssa_0
                       main@%.04.i.lcssa_0
                       main@%.110.i5_0
                       main@%_3_0
                       main@%.18.i6_0)
         true
         (= main@%_38_0 (* main@%.110.i5_0 5))
         (= main@%_39_0 (+ main@%_38_0 main@%_3_0))
         (= main@%_40_0 (+ main@%_39_0 main@%.18.i6_0))
         (= main@%_41_0 (+ main@%.110.i5_0 1))
         (= main@%_42_0 (< main@%_41_0 main@%_1_0))
         (=> main@.lr.ph7_1 (and main@.lr.ph7_1 main@.lr.ph7_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0) main@%_42_0)
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0) (= main@%.18.i6_1 main@%_40_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
             (= main@%.110.i5_1 main@%_41_0))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
             (= main@%.18.i6_2 main@%.18.i6_1))
         (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
             (= main@%.110.i5_2 main@%.110.i5_1))
         main@.lr.ph7_1)
    (main@.lr.ph7 main@%_5_0
                  main@%_1_0
                  main@%.01.i.lcssa_0
                  main@%.0.i.lcssa_0
                  main@%.04.i.lcssa_0
                  main@%.110.i5_2
                  main@%_3_0
                  main@%.18.i6_2)))
(rule (let ((a!1 (and (main@.lr.ph7 main@%_5_0
                              main@%_1_0
                              main@%.01.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.04.i.lcssa_0
                              main@%.110.i5_0
                              main@%_3_0
                              main@%.18.i6_0)
                true
                (= main@%_38_0 (* main@%.110.i5_0 5))
                (= main@%_39_0 (+ main@%_38_0 main@%_3_0))
                (= main@%_40_0 (+ main@%_39_0 main@%.18.i6_0))
                (= main@%_41_0 (+ main@%.110.i5_0 1))
                (= main@%_42_0 (< main@%_41_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_42_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.110.i.lcssa_0 main@%_41_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.18.i.lcssa_0 main@%_40_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_0 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_33_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_0 main@%.0.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_0 main@%.01.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_0 main@%.04.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i4.us_1 main@%.2.i4.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.23.i3.us_1 main@%.23.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.26.i2.us_1 main@%.26.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.18.i.lcssa_1
        main@%.2.i4.us_1
        main@%.26.i2.us_1
        main@%.23.i3.us_1
        main@%_5_0))))
(rule (let ((a!1 (and (main@.lr.ph7 main@%_5_0
                              main@%_1_0
                              main@%.01.i.lcssa_0
                              main@%.0.i.lcssa_0
                              main@%.04.i.lcssa_0
                              main@%.110.i5_0
                              main@%_3_0
                              main@%.18.i6_0)
                true
                (= main@%_38_0 (* main@%.110.i5_0 5))
                (= main@%_39_0 (+ main@%_38_0 main@%_3_0))
                (= main@%_40_0 (+ main@%_39_0 main@%.18.i6_0))
                (= main@%_41_0 (+ main@%.110.i5_0 1))
                (= main@%_42_0 (< main@%_41_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_42_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.110.i.lcssa_0 main@%_41_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.18.i.lcssa_0 main@%_40_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.18.i.lcssa_1 main@%.18.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%_31_0 (>= main@%.110.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_32_0 (< main@%.01.i.lcssa_0 main@%_5_0)))
                (=> main@.preheader_0
                    (= main@%_33_0 (ite main@%_31_0 main@%_32_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_33_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_0 main@%.04.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.26.i.lcssa_1 main@%.26.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_43_0 (= main@%.18.i.lcssa_1 main@%.26.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_43_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph.split.us
           main@%.18.i.lcssa_0
           main@%.2.i4.us_0
           main@%.26.i2.us_0
           main@%.23.i3.us_0
           main@%_5_0)
         true
         (= main@%_34_0 (+ main@%.2.i4.us_0 main@%.26.i2.us_0))
         (= main@%_35_0 (+ main@%.2.i4.us_0 5))
         (= main@%_36_0 (+ main@%.23.i3.us_0 1))
         (= main@%_37_0 (< main@%_36_0 main@%_5_0))
         (=> main@.lr.ph.split.us_1
             (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0) main@%_37_0)
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.2.i4.us_1 main@%_35_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.23.i3.us_1 main@%_36_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.26.i2.us_1 main@%_34_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.2.i4.us_2 main@%.2.i4.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.23.i3.us_2 main@%.23.i3.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.26.i2.us_2 main@%.26.i2.us_1))
         main@.lr.ph.split.us_1)
    (main@.lr.ph.split.us
      main@%.18.i.lcssa_0
      main@%.2.i4.us_2
      main@%.26.i2.us_2
      main@%.23.i3.us_2
      main@%_5_0)))
(rule (let ((a!1 (and (main@.lr.ph.split.us
                  main@%.18.i.lcssa_0
                  main@%.2.i4.us_0
                  main@%.26.i2.us_0
                  main@%.23.i3.us_0
                  main@%_5_0)
                true
                (= main@%_34_0 (+ main@%.2.i4.us_0 main@%.26.i2.us_0))
                (= main@%_35_0 (+ main@%.2.i4.us_0 5))
                (= main@%_36_0 (+ main@%.23.i3.us_0 1))
                (= main@%_37_0 (< main@%_36_0 main@%_5_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph.split.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (not main@%_37_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.26.i.lcssa_0 main@%_34_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.26.i.lcssa_1 main@%.26.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_43_0 (= main@%.18.i.lcssa_0 main@%.26.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_43_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

