(set-info :original "./results/chc/bytecode/antonopoulos/sa/simple.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph13 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph6 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph.split.us (Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_24_0 Bool )
(declare-var main@%.not.not_0 Bool )
(declare-var main@%.not7.i_0 Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%_18_0 Bool )
(declare-var main@%.1.i3.us_2 Int )
(declare-var main@%.12.i2.us_2 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%.not.i_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%.14.i5_2 Int )
(declare-var main@%.16.i4_2 Int )
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
(declare-var main@%.0.i12_2 Int )
(declare-var main@%.01.i11_2 Int )
(declare-var main@%.03.i10_2 Int )
(declare-var main@%.05.i9_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@.lr.ph13_0 Bool )
(declare-var main@%.0.i12_0 Int )
(declare-var main@%.01.i11_0 Int )
(declare-var main@%.03.i10_0 Int )
(declare-var main@%.05.i9_0 Int )
(declare-var main@%.0.i12_1 Int )
(declare-var main@%.01.i11_1 Int )
(declare-var main@%.03.i10_1 Int )
(declare-var main@%.05.i9_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.05.i.lcssa_0 Int )
(declare-var main@%.03.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.05.i.lcssa_1 Int )
(declare-var main@%.03.i.lcssa_1 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@.lr.ph6_0 Bool )
(declare-var main@%.14.i5_0 Int )
(declare-var main@%.16.i4_0 Int )
(declare-var main@%.14.i5_1 Int )
(declare-var main@%.16.i4_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.16.i.lcssa_0 Int )
(declare-var main@%.14.i.lcssa_0 Int )
(declare-var main@%.16.i.lcssa_1 Int )
(declare-var main@%.14.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%.1.i3.us_0 Int )
(declare-var main@%.12.i2.us_0 Int )
(declare-var main@%.1.i3.us_1 Int )
(declare-var main@%.12.i2.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.12.i.lcssa_0 Int )
(declare-var main@%.12.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@.lr.ph13_1 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@.lr.ph6_1 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
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
         (= main@%_4_0 (= main@%_1_0 main@%_3_0))
         main@%_4_0
         (= main@%_5_0 (> main@%_1_0 (- 1)))
         (= main@%_6_0 (> main@%_3_0 (- 1)))
         (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
         (=> main@.lr.ph13_0 (and main@.lr.ph13_0 main@entry_0))
         (=> (and main@.lr.ph13_0 main@entry_0) main@%_7_0)
         (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.0.i12_0 0))
         (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.01.i11_0 0))
         (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.03.i10_0 0))
         (=> (and main@.lr.ph13_0 main@entry_0) (= main@%.05.i9_0 0))
         (=> (and main@.lr.ph13_0 main@entry_0)
             (= main@%.0.i12_1 main@%.0.i12_0))
         (=> (and main@.lr.ph13_0 main@entry_0)
             (= main@%.01.i11_1 main@%.01.i11_0))
         (=> (and main@.lr.ph13_0 main@entry_0)
             (= main@%.03.i10_1 main@%.03.i10_0))
         (=> (and main@.lr.ph13_0 main@entry_0)
             (= main@%.05.i9_1 main@%.05.i9_0))
         main@.lr.ph13_0)
    (main@.lr.ph13 main@%_3_0
                   main@%_1_0
                   main@%.03.i10_1
                   main@%.05.i9_1
                   main@%.01.i11_1
                   main@%.0.i12_1)))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 (- 1)))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@.preheader1_0))
                (=> (and main@.lr.ph6_0 main@.preheader1_0) main@%_9_0)
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.14.i5_0 main@%.03.i.lcssa_1))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.16.i4_0 main@%.05.i.lcssa_1))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.14.i5_1 main@%.14.i5_0))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.16.i4_1 main@%.16.i4_0))
                main@.lr.ph6_0)))
  (=> a!1
      (main@.lr.ph6 main@%_3_0
                    main@%_1_0
                    main@%.0.i.lcssa_1
                    main@%.01.i.lcssa_1
                    main@%.14.i5_1
                    main@%.16.i4_1))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 (- 1)))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) (not main@%_9_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_0 main@%.05.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_18_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_1 main@%.1.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_1 main@%.12.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.14.i.lcssa_1
        main@%.12.i2.us_1
        main@%.1.i3.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 (- 1)))
                (= main@%_6_0 (> main@%_3_0 (- 1)))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@entry_0))
                (=> (and main@.preheader1_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@entry_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) (not main@%_9_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_0 main@%.05.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_18_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_0 main@%.01.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_24_0 (= main@%.14.i.lcssa_1 main@%.12.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_24_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph13 main@%_3_0
                        main@%_1_0
                        main@%.03.i10_0
                        main@%.05.i9_0
                        main@%.01.i11_0
                        main@%.0.i12_0)
         true
         (= main@%_10_0 (+ main@%.03.i10_0 1))
         (= main@%_11_0 (+ main@%.05.i9_0 1))
         (= main@%_12_0 (+ main@%.01.i11_0 1))
         (= main@%_13_0 (+ main@%.0.i12_0 1))
         (= main@%_14_0 (< main@%.05.i9_0 main@%_1_0))
         (= main@%_15_0 (< main@%.0.i12_0 main@%_3_0))
         (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
         (=> main@.lr.ph13_1 (and main@.lr.ph13_1 main@.lr.ph13_0))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0) main@%_16_0)
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.0.i12_1 main@%_13_0))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.01.i11_1 main@%_12_0))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.03.i10_1 main@%_10_0))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.05.i9_1 main@%_11_0))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.0.i12_2 main@%.0.i12_1))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.01.i11_2 main@%.01.i11_1))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.03.i10_2 main@%.03.i10_1))
         (=> (and main@.lr.ph13_1 main@.lr.ph13_0)
             (= main@%.05.i9_2 main@%.05.i9_1))
         main@.lr.ph13_1)
    (main@.lr.ph13 main@%_3_0
                   main@%_1_0
                   main@%.03.i10_2
                   main@%.05.i9_2
                   main@%.01.i11_2
                   main@%.0.i12_2)))
(rule (let ((a!1 (and (main@.lr.ph13 main@%_3_0
                               main@%_1_0
                               main@%.03.i10_0
                               main@%.05.i9_0
                               main@%.01.i11_0
                               main@%.0.i12_0)
                true
                (= main@%_10_0 (+ main@%.03.i10_0 1))
                (= main@%_11_0 (+ main@%.05.i9_0 1))
                (= main@%_12_0 (+ main@%.01.i11_0 1))
                (= main@%_13_0 (+ main@%.0.i12_0 1))
                (= main@%_14_0 (< main@%.05.i9_0 main@%_1_0))
                (= main@%_15_0 (< main@%.0.i12_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0) (not main@%_16_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@.preheader1_0))
                (=> (and main@.lr.ph6_0 main@.preheader1_0) main@%_9_0)
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.14.i5_0 main@%.03.i.lcssa_1))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.16.i4_0 main@%.05.i.lcssa_1))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.14.i5_1 main@%.14.i5_0))
                (=> (and main@.lr.ph6_0 main@.preheader1_0)
                    (= main@%.16.i4_1 main@%.16.i4_0))
                main@.lr.ph6_0)))
  (=> a!1
      (main@.lr.ph6 main@%_3_0
                    main@%_1_0
                    main@%.0.i.lcssa_1
                    main@%.01.i.lcssa_1
                    main@%.14.i5_1
                    main@%.16.i4_1))))
(rule (let ((a!1 (and (main@.lr.ph13 main@%_3_0
                               main@%_1_0
                               main@%.03.i10_0
                               main@%.05.i9_0
                               main@%.01.i11_0
                               main@%.0.i12_0)
                true
                (= main@%_10_0 (+ main@%.03.i10_0 1))
                (= main@%_11_0 (+ main@%.05.i9_0 1))
                (= main@%_12_0 (+ main@%.01.i11_0 1))
                (= main@%_13_0 (+ main@%.0.i12_0 1))
                (= main@%_14_0 (< main@%.05.i9_0 main@%_1_0))
                (= main@%_15_0 (< main@%.0.i12_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0) (not main@%_16_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) (not main@%_9_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_0 main@%.05.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_18_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_0 main@%.0.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_0 main@%.01.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_1 main@%.1.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_1 main@%.12.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.14.i.lcssa_1
        main@%.12.i2.us_1
        main@%.1.i3.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph13 main@%_3_0
                               main@%_1_0
                               main@%.03.i10_0
                               main@%.05.i9_0
                               main@%.01.i11_0
                               main@%.0.i12_0)
                true
                (= main@%_10_0 (+ main@%.03.i10_0 1))
                (= main@%_11_0 (+ main@%.05.i9_0 1))
                (= main@%_12_0 (+ main@%.01.i11_0 1))
                (= main@%_13_0 (+ main@%.0.i12_0 1))
                (= main@%_14_0 (< main@%.05.i9_0 main@%_1_0))
                (= main@%_15_0 (< main@%.0.i12_0 main@%_3_0))
                (= main@%_16_0 (ite main@%_14_0 main@%_15_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0) (not main@%_16_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_0 main@%_10_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_0 main@%_12_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.05.i.lcssa_1 main@%.05.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph13_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not.i_0 (> main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_8_0 (<= main@%.05.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_9_0 (ite main@%_8_0 main@%.not.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) (not main@%_9_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_0 main@%.05.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_0 main@%.03.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_18_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_0 main@%.01.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_24_0 (= main@%.14.i.lcssa_1 main@%.12.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_24_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph6 main@%_3_0
                       main@%_1_0
                       main@%.0.i.lcssa_0
                       main@%.01.i.lcssa_0
                       main@%.14.i5_0
                       main@%.16.i4_0)
         true
         (= main@%_21_0 (+ main@%.14.i5_0 1))
         (= main@%_22_0 (+ main@%.16.i4_0 1))
         (= main@%_23_0 (< main@%.16.i4_0 main@%_1_0))
         (=> main@.lr.ph6_1 (and main@.lr.ph6_1 main@.lr.ph6_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) main@%_23_0)
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (= main@%.14.i5_1 main@%_21_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (= main@%.16.i4_1 main@%_22_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%.14.i5_2 main@%.14.i5_1))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%.16.i4_2 main@%.16.i4_1))
         main@.lr.ph6_1)
    (main@.lr.ph6 main@%_3_0
                  main@%_1_0
                  main@%.0.i.lcssa_0
                  main@%.01.i.lcssa_0
                  main@%.14.i5_2
                  main@%.16.i4_2)))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_3_0
                              main@%_1_0
                              main@%.0.i.lcssa_0
                              main@%.01.i.lcssa_0
                              main@%.14.i5_0
                              main@%.16.i4_0)
                true
                (= main@%_21_0 (+ main@%.14.i5_0 1))
                (= main@%_22_0 (+ main@%.16.i4_0 1))
                (= main@%_23_0 (< main@%.16.i4_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_23_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.16.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.14.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_18_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_0 main@%.0.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_0 main@%.01.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.1.i3.us_1 main@%.1.i3.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.12.i2.us_1 main@%.12.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.14.i.lcssa_1
        main@%.12.i2.us_1
        main@%.1.i3.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_3_0
                              main@%_1_0
                              main@%.0.i.lcssa_0
                              main@%.01.i.lcssa_0
                              main@%.14.i5_0
                              main@%.16.i4_0)
                true
                (= main@%_21_0 (+ main@%.14.i5_0 1))
                (= main@%_22_0 (+ main@%.16.i4_0 1))
                (= main@%_23_0 (< main@%.16.i4_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_23_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.16.i.lcssa_0 main@%_22_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.14.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.16.i.lcssa_1 main@%.16.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.14.i.lcssa_1 main@%.14.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not7.i_0 (> main@%.16.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_17_0 (<= main@%.0.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_18_0 (ite main@%.not7.i_0 main@%_17_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_18_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_0 main@%.01.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_24_0 (= main@%.14.i.lcssa_1 main@%.12.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_24_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph.split.us
           main@%.14.i.lcssa_0
           main@%.12.i2.us_0
           main@%.1.i3.us_0
           main@%_3_0)
         true
         (= main@%_19_0 (+ main@%.12.i2.us_0 1))
         (= main@%_20_0 (+ main@%.1.i3.us_0 1))
         (= main@%.not.not_0 (< main@%.1.i3.us_0 main@%_3_0))
         (=> main@.lr.ph.split.us_1
             (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             main@%.not.not_0)
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.1.i3.us_1 main@%_20_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.12.i2.us_1 main@%_19_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.1.i3.us_2 main@%.1.i3.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.12.i2.us_2 main@%.12.i2.us_1))
         main@.lr.ph.split.us_1)
    (main@.lr.ph.split.us
      main@%.14.i.lcssa_0
      main@%.12.i2.us_2
      main@%.1.i3.us_2
      main@%_3_0)))
(rule (let ((a!1 (and (main@.lr.ph.split.us
                  main@%.14.i.lcssa_0
                  main@%.12.i2.us_0
                  main@%.1.i3.us_0
                  main@%_3_0)
                true
                (= main@%_19_0 (+ main@%.12.i2.us_0 1))
                (= main@%_20_0 (+ main@%.1.i3.us_0 1))
                (= main@%.not.not_0 (< main@%.1.i3.us_0 main@%_3_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph.split.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (not main@%.not.not_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.12.i.lcssa_0 main@%_19_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.12.i.lcssa_1 main@%.12.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_24_0 (= main@%.14.i.lcssa_0 main@%.12.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_24_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

