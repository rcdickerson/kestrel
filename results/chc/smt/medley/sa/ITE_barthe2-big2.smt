(set-info :original "./results/chc/bytecode/medley/sa/ITE_barthe2-big2.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph27 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph20 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph16.split.us (Int Int Int Int Int ))
(declare-rel main@.lr.ph12 (Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_28_0 Bool )
(declare-var main@%.not17.i.not_0 Bool )
(declare-var main@%.not17.i6_0 Bool )
(declare-var main@%.3.i8_2 Int )
(declare-var main@%.34.i7_2 Int )
(declare-var main@%.not16.i.not_0 Bool )
(declare-var main@%.not16.i9_0 Bool )
(declare-var main@%.38.i11_2 Int )
(declare-var main@%.312.i10_2 Int )
(declare-var main@%.not.not_0 Bool )
(declare-var main@%.not15.i_0 Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%_18_0 Bool )
(declare-var main@%.2.i15.us_2 Int )
(declare-var main@%.23.i14.us_2 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%.not14.i_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%.27.i19_2 Int )
(declare-var main@%.211.i18_2 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@%_16_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Bool )
(declare-var main@%.1.i26_2 Int )
(declare-var main@%.12.i25_2 Int )
(declare-var main@%.16.i24_2 Int )
(declare-var main@%.110.i23_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@.lr.ph27_0 Bool )
(declare-var main@%.1.i26_0 Int )
(declare-var main@%.12.i25_0 Int )
(declare-var main@%.16.i24_0 Int )
(declare-var main@%.110.i23_0 Int )
(declare-var main@%.1.i26_1 Int )
(declare-var main@%.12.i25_1 Int )
(declare-var main@%.16.i24_1 Int )
(declare-var main@%.110.i23_1 Int )
(declare-var main@.preheader3_0 Bool )
(declare-var main@%.110.i.lcssa_0 Int )
(declare-var main@%.16.i.lcssa_0 Int )
(declare-var main@%.12.i.lcssa_0 Int )
(declare-var main@%.1.i.lcssa_0 Int )
(declare-var main@%.110.i.lcssa_1 Int )
(declare-var main@%.16.i.lcssa_1 Int )
(declare-var main@%.12.i.lcssa_1 Int )
(declare-var main@%.1.i.lcssa_1 Int )
(declare-var main@.lr.ph20_0 Bool )
(declare-var main@%.27.i19_0 Int )
(declare-var main@%.211.i18_0 Int )
(declare-var main@%.27.i19_1 Int )
(declare-var main@%.211.i18_1 Int )
(declare-var main@.preheader2_0 Bool )
(declare-var main@%.211.i.lcssa_0 Int )
(declare-var main@%.27.i.lcssa_0 Int )
(declare-var main@%.211.i.lcssa_1 Int )
(declare-var main@%.27.i.lcssa_1 Int )
(declare-var main@.lr.ph16.split.us_0 Bool )
(declare-var main@%.2.i15.us_0 Int )
(declare-var main@%.23.i14.us_0 Int )
(declare-var main@%.2.i15.us_1 Int )
(declare-var main@%.23.i14.us_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.2.i.lcssa_0 Int )
(declare-var main@%.2.i.lcssa_1 Int )
(declare-var main@.lr.ph12_0 Bool )
(declare-var main@%.38.i11_0 Int )
(declare-var main@%.312.i10_0 Int )
(declare-var main@%.38.i11_1 Int )
(declare-var main@%.312.i10_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.312.i.lcssa_0 Int )
(declare-var main@%.312.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.3.i8_0 Int )
(declare-var main@%.34.i7_0 Int )
(declare-var main@%.3.i8_1 Int )
(declare-var main@%.34.i7_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.3.i.lcssa_0 Int )
(declare-var main@%.3.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@.lr.ph27_1 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@.lr.ph20_1 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@.lr.ph16.split.us_1 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@.lr.ph12_1 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@.lr.ph_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (=> (and (main@entry @arb_int_0)
         true
         (= main@%_0_0 @arb_int_0)
         (= main@%_2_0 @arb_int_0)
         (= main@%_4_0 (= main@%_1_0 main@%_3_0))
         main@%_4_0
         (= main@%_5_0 (> main@%_1_0 (- 1)))
         (= main@%_6_0 (> main@%_3_0 0))
         (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
         (=> main@.lr.ph27_0 (and main@.lr.ph27_0 main@entry_0))
         (=> (and main@.lr.ph27_0 main@entry_0) main@%_7_0)
         (=> (and main@.lr.ph27_0 main@entry_0) (= main@%.1.i26_0 1))
         (=> (and main@.lr.ph27_0 main@entry_0) (= main@%.12.i25_0 1))
         (=> (and main@.lr.ph27_0 main@entry_0) (= main@%.16.i24_0 0))
         (=> (and main@.lr.ph27_0 main@entry_0) (= main@%.110.i23_0 1))
         (=> (and main@.lr.ph27_0 main@entry_0)
             (= main@%.1.i26_1 main@%.1.i26_0))
         (=> (and main@.lr.ph27_0 main@entry_0)
             (= main@%.12.i25_1 main@%.12.i25_0))
         (=> (and main@.lr.ph27_0 main@entry_0)
             (= main@%.16.i24_1 main@%.16.i24_0))
         (=> (and main@.lr.ph27_0 main@entry_0)
             (= main@%.110.i23_1 main@%.110.i23_0))
         main@.lr.ph27_0)
    (main@.lr.ph27 main@%_3_0
                   main@%_1_0
                   main@%.16.i24_1
                   main@%.110.i23_1
                   main@%.1.i26_1
                   main@%.12.i25_1)))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@entry_0))
                (=> (and main@.preheader3_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_0 0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.lr.ph20_0 (and main@.lr.ph20_0 main@.preheader3_0))
                (=> (and main@.lr.ph20_0 main@.preheader3_0) main@%_9_0)
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.27.i19_0 main@%.16.i.lcssa_1))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.211.i18_0 main@%.110.i.lcssa_1))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.27.i19_1 main@%.27.i19_0))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.211.i18_1 main@%.211.i18_0))
                main@.lr.ph20_0)))
  (=> a!1
      (main@.lr.ph20 main@%_3_0
                     main@%_1_0
                     main@%.12.i.lcssa_1
                     main@%.1.i.lcssa_1
                     main@%.27.i19_1
                     main@%.211.i18_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@entry_0))
                (=> (and main@.preheader3_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_0 0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.lr.ph16.split.us_0
                    (and main@.lr.ph16.split.us_0 main@.preheader2_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    main@%_18_0)
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_0 main@%.1.i.lcssa_1))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_0 main@%.12.i.lcssa_1))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_1 main@%.2.i15.us_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_1 main@%.23.i14.us_0))
                main@.lr.ph16.split.us_0)))
  (=> a!1
      (main@.lr.ph16.split.us
        main@%_3_0
        main@%_1_0
        main@%.211.i.lcssa_1
        main@%.2.i15.us_1
        main@%.23.i14.us_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@entry_0))
                (=> (and main@.preheader3_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_0 0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (not main@%.not16.i9_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_0 1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_0 main@%.211.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_1 main@%.38.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_1 main@%.312.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%.2.i.lcssa_1
                     main@%.312.i10_1
                     main@%.38.i11_1
                     main@%_1_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@entry_0))
                (=> (and main@.preheader3_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_0 0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (not main@%.not17.i6_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_0 main@%.2.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.34.i7_0 1))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_1 main@%.3.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.34.i7_1 main@%.34.i7_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.312.i.lcssa_1 main@%.3.i8_1 main@%.34.i7_1 main@%_3_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@entry_0))
                (=> (and main@.preheader3_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_0 0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_0 1))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@entry_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    main@%.not17.i6_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_1 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph27 main@%_3_0
                        main@%_1_0
                        main@%.16.i24_0
                        main@%.110.i23_0
                        main@%.1.i26_0
                        main@%.12.i25_0)
         true
         (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
         (= main@%_11_0 (+ main@%.16.i24_0 1))
         (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
         (= main@%_13_0 (+ main@%.12.i25_0 1))
         (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
         (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
         (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
         (=> main@.lr.ph27_1 (and main@.lr.ph27_1 main@.lr.ph27_0))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0) main@%_16_0)
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.1.i26_1 main@%_12_0))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.12.i25_1 main@%_13_0))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.16.i24_1 main@%_11_0))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.110.i23_1 main@%_10_0))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.1.i26_2 main@%.1.i26_1))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.12.i25_2 main@%.12.i25_1))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.16.i24_2 main@%.16.i24_1))
         (=> (and main@.lr.ph27_1 main@.lr.ph27_0)
             (= main@%.110.i23_2 main@%.110.i23_1))
         main@.lr.ph27_1)
    (main@.lr.ph27 main@%_3_0
                   main@%_1_0
                   main@%.16.i24_2
                   main@%.110.i23_2
                   main@%.1.i26_2
                   main@%.12.i25_2)))
(rule (let ((a!1 (and (main@.lr.ph27 main@%_3_0
                               main@%_1_0
                               main@%.16.i24_0
                               main@%.110.i23_0
                               main@%.1.i26_0
                               main@%.12.i25_0)
                true
                (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
                (= main@%_11_0 (+ main@%.16.i24_0 1))
                (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
                (= main@%_13_0 (+ main@%.12.i25_0 1))
                (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
                (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph27_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0) (not main@%_16_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.lr.ph20_0 (and main@.lr.ph20_0 main@.preheader3_0))
                (=> (and main@.lr.ph20_0 main@.preheader3_0) main@%_9_0)
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.27.i19_0 main@%.16.i.lcssa_1))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.211.i18_0 main@%.110.i.lcssa_1))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.27.i19_1 main@%.27.i19_0))
                (=> (and main@.lr.ph20_0 main@.preheader3_0)
                    (= main@%.211.i18_1 main@%.211.i18_0))
                main@.lr.ph20_0)))
  (=> a!1
      (main@.lr.ph20 main@%_3_0
                     main@%_1_0
                     main@%.12.i.lcssa_1
                     main@%.1.i.lcssa_1
                     main@%.27.i19_1
                     main@%.211.i18_1))))
(rule (let ((a!1 (and (main@.lr.ph27 main@%_3_0
                               main@%_1_0
                               main@%.16.i24_0
                               main@%.110.i23_0
                               main@%.1.i26_0
                               main@%.12.i25_0)
                true
                (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
                (= main@%_11_0 (+ main@%.16.i24_0 1))
                (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
                (= main@%_13_0 (+ main@%.12.i25_0 1))
                (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
                (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph27_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0) (not main@%_16_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.lr.ph16.split.us_0
                    (and main@.lr.ph16.split.us_0 main@.preheader2_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    main@%_18_0)
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_0 main@%.1.i.lcssa_1))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_0 main@%.12.i.lcssa_1))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_1 main@%.2.i15.us_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_1 main@%.23.i14.us_0))
                main@.lr.ph16.split.us_0)))
  (=> a!1
      (main@.lr.ph16.split.us
        main@%_3_0
        main@%_1_0
        main@%.211.i.lcssa_1
        main@%.2.i15.us_1
        main@%.23.i14.us_1))))
(rule (let ((a!1 (and (main@.lr.ph27 main@%_3_0
                               main@%_1_0
                               main@%.16.i24_0
                               main@%.110.i23_0
                               main@%.1.i26_0
                               main@%.12.i25_0)
                true
                (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
                (= main@%_11_0 (+ main@%.16.i24_0 1))
                (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
                (= main@%_13_0 (+ main@%.12.i25_0 1))
                (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
                (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph27_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0) (not main@%_16_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (not main@%.not16.i9_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_0 1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_0 main@%.211.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_1 main@%.38.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_1 main@%.312.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%.2.i.lcssa_1
                     main@%.312.i10_1
                     main@%.38.i11_1
                     main@%_1_0))))
(rule (let ((a!1 (and (main@.lr.ph27 main@%_3_0
                               main@%_1_0
                               main@%.16.i24_0
                               main@%.110.i23_0
                               main@%.1.i26_0
                               main@%.12.i25_0)
                true
                (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
                (= main@%_11_0 (+ main@%.16.i24_0 1))
                (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
                (= main@%_13_0 (+ main@%.12.i25_0 1))
                (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
                (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph27_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0) (not main@%_16_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (not main@%.not17.i6_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_0 main@%.2.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.34.i7_0 1))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_1 main@%.3.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.34.i7_1 main@%.34.i7_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.312.i.lcssa_1 main@%.3.i8_1 main@%.34.i7_1 main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph27 main@%_3_0
                               main@%_1_0
                               main@%.16.i24_0
                               main@%.110.i23_0
                               main@%.1.i26_0
                               main@%.12.i25_0)
                true
                (= main@%_10_0 (+ main@%.16.i24_0 main@%.110.i23_0))
                (= main@%_11_0 (+ main@%.16.i24_0 1))
                (= main@%_12_0 (+ main@%.1.i26_0 main@%.12.i25_0))
                (= main@%_13_0 (+ main@%.12.i25_0 1))
                (= main@%_14_0 (< main@%.16.i24_0 main@%_1_0))
                (= main@%_15_0 (< main@%.12.i25_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph27_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0) (not main@%_16_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.110.i.lcssa_1 main@%.110.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph27_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not14.i_0 (> main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_8_0 (<= main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not14.i_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_9_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_0 main@%.110.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_0 main@%.16.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    main@%.not17.i6_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_1 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph20 main@%_3_0
                        main@%_1_0
                        main@%.12.i.lcssa_0
                        main@%.1.i.lcssa_0
                        main@%.27.i19_0
                        main@%.211.i18_0)
         true
         (= main@%_21_0 (+ main@%.27.i19_0 main@%.211.i18_0))
         (= main@%_22_0 (+ main@%.27.i19_0 1))
         (= main@%_23_0 (< main@%.27.i19_0 main@%_1_0))
         (=> main@.lr.ph20_1 (and main@.lr.ph20_1 main@.lr.ph20_0))
         (=> (and main@.lr.ph20_1 main@.lr.ph20_0) main@%_23_0)
         (=> (and main@.lr.ph20_1 main@.lr.ph20_0)
             (= main@%.27.i19_1 main@%_22_0))
         (=> (and main@.lr.ph20_1 main@.lr.ph20_0)
             (= main@%.211.i18_1 main@%_21_0))
         (=> (and main@.lr.ph20_1 main@.lr.ph20_0)
             (= main@%.27.i19_2 main@%.27.i19_1))
         (=> (and main@.lr.ph20_1 main@.lr.ph20_0)
             (= main@%.211.i18_2 main@%.211.i18_1))
         main@.lr.ph20_1)
    (main@.lr.ph20 main@%_3_0
                   main@%_1_0
                   main@%.12.i.lcssa_0
                   main@%.1.i.lcssa_0
                   main@%.27.i19_2
                   main@%.211.i18_2)))
(rule (let ((a!1 (and (main@.lr.ph20 main@%_3_0
                               main@%_1_0
                               main@%.12.i.lcssa_0
                               main@%.1.i.lcssa_0
                               main@%.27.i19_0
                               main@%.211.i18_0)
                true
                (= main@%_21_0 (+ main@%.27.i19_0 main@%.211.i18_0))
                (= main@%_22_0 (+ main@%.27.i19_0 1))
                (= main@%_23_0 (< main@%.27.i19_0 main@%_1_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph20_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0) (not main@%_23_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.lr.ph16.split.us_0
                    (and main@.lr.ph16.split.us_0 main@.preheader2_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    main@%_18_0)
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_0 main@%.1.i.lcssa_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_0 main@%.12.i.lcssa_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.2.i15.us_1 main@%.2.i15.us_0))
                (=> (and main@.lr.ph16.split.us_0 main@.preheader2_0)
                    (= main@%.23.i14.us_1 main@%.23.i14.us_0))
                main@.lr.ph16.split.us_0)))
  (=> a!1
      (main@.lr.ph16.split.us
        main@%_3_0
        main@%_1_0
        main@%.211.i.lcssa_1
        main@%.2.i15.us_1
        main@%.23.i14.us_1))))
(rule (let ((a!1 (and (main@.lr.ph20 main@%_3_0
                               main@%_1_0
                               main@%.12.i.lcssa_0
                               main@%.1.i.lcssa_0
                               main@%.27.i19_0
                               main@%.211.i18_0)
                true
                (= main@%_21_0 (+ main@%.27.i19_0 main@%.211.i18_0))
                (= main@%_22_0 (+ main@%.27.i19_0 1))
                (= main@%_23_0 (< main@%.27.i19_0 main@%_1_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph20_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0) (not main@%_23_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (not main@%.not16.i9_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_0 1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_0 main@%.211.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_1 main@%.38.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_1 main@%.312.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%.2.i.lcssa_1
                     main@%.312.i10_1
                     main@%.38.i11_1
                     main@%_1_0))))
(rule (let ((a!1 (and (main@.lr.ph20 main@%_3_0
                               main@%_1_0
                               main@%.12.i.lcssa_0
                               main@%.1.i.lcssa_0
                               main@%.27.i19_0
                               main@%.211.i18_0)
                true
                (= main@%_21_0 (+ main@%.27.i19_0 main@%.211.i18_0))
                (= main@%_22_0 (+ main@%.27.i19_0 1))
                (= main@%_23_0 (< main@%.27.i19_0 main@%_1_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph20_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0) (not main@%_23_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (not main@%.not17.i6_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_0 main@%.2.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.34.i7_0 1))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_1 main@%.3.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.34.i7_1 main@%.34.i7_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.312.i.lcssa_1 main@%.3.i8_1 main@%.34.i7_1 main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph20 main@%_3_0
                               main@%_1_0
                               main@%.12.i.lcssa_0
                               main@%.1.i.lcssa_0
                               main@%.27.i19_0
                               main@%.211.i18_0)
                true
                (= main@%_21_0 (+ main@%.27.i19_0 main@%.211.i18_0))
                (= main@%_22_0 (+ main@%.27.i19_0 1))
                (= main@%_23_0 (< main@%.27.i19_0 main@%_1_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph20_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0) (not main@%_23_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.211.i.lcssa_1 main@%.211.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.lr.ph20_0)
                    (= main@%.27.i.lcssa_1 main@%.27.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%.not15.i_0 (> main@%.27.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader2_0
                    (= main@%_17_0 (<= main@%.12.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader2_0
                    (= main@%_18_0 (ite main@%.not15.i_0 main@%_17_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_18_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_0 main@%.1.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    main@%.not17.i6_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_1 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph16.split.us
           main@%_3_0
           main@%_1_0
           main@%.211.i.lcssa_0
           main@%.2.i15.us_0
           main@%.23.i14.us_0)
         true
         (= main@%_19_0 (+ main@%.2.i15.us_0 main@%.23.i14.us_0))
         (= main@%_20_0 (+ main@%.23.i14.us_0 1))
         (= main@%.not.not_0 (< main@%.23.i14.us_0 main@%_3_0))
         (=> main@.lr.ph16.split.us_1
             (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0))
         (=> (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0)
             main@%.not.not_0)
         (=> (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0)
             (= main@%.2.i15.us_1 main@%_19_0))
         (=> (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0)
             (= main@%.23.i14.us_1 main@%_20_0))
         (=> (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0)
             (= main@%.2.i15.us_2 main@%.2.i15.us_1))
         (=> (and main@.lr.ph16.split.us_1 main@.lr.ph16.split.us_0)
             (= main@%.23.i14.us_2 main@%.23.i14.us_1))
         main@.lr.ph16.split.us_1)
    (main@.lr.ph16.split.us
      main@%_3_0
      main@%_1_0
      main@%.211.i.lcssa_0
      main@%.2.i15.us_2
      main@%.23.i14.us_2)))
(rule (let ((a!1 (and (main@.lr.ph16.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%.211.i.lcssa_0
                  main@%.2.i15.us_0
                  main@%.23.i14.us_0)
                true
                (= main@%_19_0 (+ main@%.2.i15.us_0 main@%.23.i14.us_0))
                (= main@%_20_0 (+ main@%.23.i14.us_0 1))
                (= main@%.not.not_0 (< main@%.23.i14.us_0 main@%_3_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.lr.ph16.split.us_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (not main@%.not.not_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (not main@%.not16.i9_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_0 1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_0 main@%.211.i.lcssa_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.38.i11_1 main@%.38.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.312.i10_1 main@%.312.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%.2.i.lcssa_1
                     main@%.312.i10_1
                     main@%.38.i11_1
                     main@%_1_0))))
(rule (let ((a!1 (and (main@.lr.ph16.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%.211.i.lcssa_0
                  main@%.2.i15.us_0
                  main@%.23.i14.us_0)
                true
                (= main@%_19_0 (+ main@%.2.i15.us_0 main@%.23.i14.us_0))
                (= main@%_20_0 (+ main@%.23.i14.us_0 1))
                (= main@%.not.not_0 (< main@%.23.i14.us_0 main@%_3_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.lr.ph16.split.us_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (not main@%.not.not_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (not main@%.not17.i6_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_0 main@%.2.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.34.i7_0 1))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_1 main@%.3.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.34.i7_1 main@%.34.i7_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.312.i.lcssa_1 main@%.3.i8_1 main@%.34.i7_1 main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph16.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%.211.i.lcssa_0
                  main@%.2.i15.us_0
                  main@%.23.i14.us_0)
                true
                (= main@%_19_0 (+ main@%.2.i15.us_0 main@%.23.i14.us_0))
                (= main@%_20_0 (+ main@%.23.i14.us_0 1))
                (= main@%.not.not_0 (< main@%.23.i14.us_0 main@%_3_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.lr.ph16.split.us_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (not main@%.not.not_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_0 main@%_19_0))
                (=> (and main@.preheader1_0 main@.lr.ph16.split.us_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.preheader1_0 (= main@%.not16.i9_0 (< main@%_1_0 1)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    main@%.not16.i9_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_0 main@%.211.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    main@%.not17.i6_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_1 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph12 main@%_3_0
                        main@%.2.i.lcssa_0
                        main@%.312.i10_0
                        main@%.38.i11_0
                        main@%_1_0)
         true
         (= main@%_24_0 (* main@%.312.i10_0 2))
         (= main@%_25_0 (+ main@%.38.i11_0 1))
         (= main@%.not16.i.not_0 (< main@%.38.i11_0 main@%_1_0))
         (=> main@.lr.ph12_1 (and main@.lr.ph12_1 main@.lr.ph12_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0) main@%.not16.i.not_0)
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.38.i11_1 main@%_25_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.312.i10_1 main@%_24_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.38.i11_2 main@%.38.i11_1))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.312.i10_2 main@%.312.i10_1))
         main@.lr.ph12_1)
    (main@.lr.ph12 main@%_3_0
                   main@%.2.i.lcssa_0
                   main@%.312.i10_2
                   main@%.38.i11_2
                   main@%_1_0)))
(rule (let ((a!1 (and (main@.lr.ph12 main@%_3_0
                               main@%.2.i.lcssa_0
                               main@%.312.i10_0
                               main@%.38.i11_0
                               main@%_1_0)
                true
                (= main@%_24_0 (* main@%.312.i10_0 2))
                (= main@%_25_0 (+ main@%.38.i11_0 1))
                (= main@%.not16.i.not_0 (< main@%.38.i11_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph12_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (not main@%.not16.i.not_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.312.i.lcssa_0 main@%_24_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (not main@%.not17.i6_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_0 main@%.2.i.lcssa_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.34.i7_0 1))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.3.i8_1 main@%.3.i8_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.34.i7_1 main@%.34.i7_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.312.i.lcssa_1 main@%.3.i8_1 main@%.34.i7_1 main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph12 main@%_3_0
                               main@%.2.i.lcssa_0
                               main@%.312.i10_0
                               main@%.38.i11_0
                               main@%_1_0)
                true
                (= main@%_24_0 (* main@%.312.i10_0 2))
                (= main@%_25_0 (+ main@%.38.i11_0 1))
                (= main@%.not16.i.not_0 (< main@%.38.i11_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph12_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (not main@%.not16.i.not_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.312.i.lcssa_0 main@%_24_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.312.i.lcssa_1 main@%.312.i.lcssa_0))
                (=> main@.preheader_0 (= main@%.not17.i6_0 (< main@%_3_0 1)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    main@%.not17.i6_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_1 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph main@%.312.i.lcssa_0
                      main@%.3.i8_0
                      main@%.34.i7_0
                      main@%_3_0)
         true
         (= main@%_26_0 (* main@%.3.i8_0 2))
         (= main@%_27_0 (+ main@%.34.i7_0 1))
         (= main@%.not17.i.not_0 (< main@%.34.i7_0 main@%_3_0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%.not17.i.not_0)
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.3.i8_1 main@%_26_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.34.i7_1 main@%_27_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.3.i8_2 main@%.3.i8_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.34.i7_2 main@%.34.i7_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%.312.i.lcssa_0 main@%.3.i8_2 main@%.34.i7_2 main@%_3_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%.312.i.lcssa_0
                             main@%.3.i8_0
                             main@%.34.i7_0
                             main@%_3_0)
                true
                (= main@%_26_0 (* main@%.3.i8_0 2))
                (= main@%_27_0 (+ main@%.34.i7_0 1))
                (= main@%.not17.i.not_0 (< main@%.34.i7_0 main@%_3_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (not main@%.not17.i.not_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.3.i.lcssa_0 main@%_26_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_28_0 (= main@%.312.i.lcssa_0 main@%.3.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_28_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

