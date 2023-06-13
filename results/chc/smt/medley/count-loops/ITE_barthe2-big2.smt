(set-info :original "./results/chc/bytecode/medley/count-loops/ITE_barthe2-big2.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph44 (Int Int Bool Bool Int Int ))
(declare-rel main@_12 (Int Int Bool Bool Int Bool ))
(declare-rel main@.lr.ph37 (Int Int Bool Int Int Int Int ))
(declare-rel main@.lr.ph30 (Int Int Bool Int Int Int Int ))
(declare-rel main@.lr.ph26.split.us (Int Int Bool Int Int Int ))
(declare-rel main@.lr.ph19 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph12 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph.split.us (Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_50_0 Bool )
(declare-var main@%.not.not_0 Bool )
(declare-var main@%.not26.i_0 Bool )
(declare-var main@%_43_0 Bool )
(declare-var main@%_44_0 Bool )
(declare-var main@%.8.i9.us_2 Int )
(declare-var main@%.89.i8.us_2 Int )
(declare-var main@%_49_0 Bool )
(declare-var main@%.not25.i_0 Bool )
(declare-var main@%_36_0 Bool )
(declare-var main@%_37_0 Bool )
(declare-var main@%.515.i11_2 Int )
(declare-var main@%.521.i10_2 Int )
(declare-var main@%.not27.not.i_0 Bool )
(declare-var main@%.78.v.i_0 Int )
(declare-var main@%.7.v.i_0 Int )
(declare-var main@%_40_0 Bool )
(declare-var main@%_41_0 Bool )
(declare-var main@%_42_0 Bool )
(declare-var main@%.6.i18_2 Int )
(declare-var main@%.67.i17_2 Int )
(declare-var main@%.414.i16_2 Int )
(declare-var main@%.420.i15_2 Int )
(declare-var main@%.not.not47_0 Bool )
(declare-var main@%.not24.i_0 Bool )
(declare-var main@%_29_0 Bool )
(declare-var main@%_30_0 Bool )
(declare-var main@%.5.i25.us_2 Int )
(declare-var main@%.56.i24.us_2 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%.not23.i_0 Bool )
(declare-var main@%_18_0 Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%.313.i29_2 Int )
(declare-var main@%.319.i28_2 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%.not28.not.i_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Bool )
(declare-var main@%_16_0 Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%.3.i36_2 Int )
(declare-var main@%.34.i35_2 Int )
(declare-var main@%.212.i34_2 Int )
(declare-var main@%.218.i33_2 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%.111.i_2 Int )
(declare-var main@%.not29.not.i_0 Bool )
(declare-var main@%spec.select.v.i_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%.01.i43_2 Int )
(declare-var main@%.010.i42_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Bool )
(declare-var main@.lr.ph44_0 Bool )
(declare-var main@%.01.i43_0 Int )
(declare-var main@%.010.i42_0 Int )
(declare-var main@%.01.i43_1 Int )
(declare-var main@%.010.i42_1 Int )
(declare-var main@.preheader7_0 Bool )
(declare-var main@%.010.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.010.i.lcssa_1 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@%.not.i_0 Bool )
(declare-var main@_12_0 Bool )
(declare-var main@%.111.i_0 Int )
(declare-var main@%.111.i_1 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%spec.select.i_0 Int )
(declare-var main@.lr.ph44_1 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@_12_1 Bool )
(declare-var main@.preheader5_0 Bool )
(declare-var main@.lr.ph37_0 Bool )
(declare-var main@%.3.i36_0 Int )
(declare-var main@%.34.i35_0 Int )
(declare-var main@%.212.i34_0 Int )
(declare-var main@%.218.i33_0 Int )
(declare-var main@%.3.i36_1 Int )
(declare-var main@%.34.i35_1 Int )
(declare-var main@%.212.i34_1 Int )
(declare-var main@%.218.i33_1 Int )
(declare-var main@.preheader4_0 Bool )
(declare-var main@%.218.i.lcssa_0 Int )
(declare-var main@%.212.i.lcssa_0 Int )
(declare-var main@%.34.i.lcssa_0 Int )
(declare-var main@%.3.i.lcssa_0 Int )
(declare-var main@%.218.i.lcssa_1 Int )
(declare-var main@%.212.i.lcssa_1 Int )
(declare-var main@%.34.i.lcssa_1 Int )
(declare-var main@%.3.i.lcssa_1 Int )
(declare-var main@.lr.ph30_0 Bool )
(declare-var main@%.313.i29_0 Int )
(declare-var main@%.319.i28_0 Int )
(declare-var main@%.313.i29_1 Int )
(declare-var main@%.319.i28_1 Int )
(declare-var main@.preheader3_0 Bool )
(declare-var main@%.319.i.lcssa_0 Int )
(declare-var main@%.313.i.lcssa_0 Int )
(declare-var main@%.319.i.lcssa_1 Int )
(declare-var main@%.313.i.lcssa_1 Int )
(declare-var main@.lr.ph26.split.us_0 Bool )
(declare-var main@%.5.i25.us_0 Int )
(declare-var main@%.56.i24.us_0 Int )
(declare-var main@%.5.i25.us_1 Int )
(declare-var main@%.56.i24.us_1 Int )
(declare-var main@.preheader2_0 Bool )
(declare-var main@%.5.i.lcssa_0 Int )
(declare-var main@%.5.i.lcssa_1 Int )
(declare-var main@.lr.ph19_0 Bool )
(declare-var main@%.6.i18_0 Int )
(declare-var main@%.67.i17_0 Int )
(declare-var main@%.414.i16_0 Int )
(declare-var main@%.420.i15_0 Int )
(declare-var main@%.6.i18_1 Int )
(declare-var main@%.67.i17_1 Int )
(declare-var main@%.414.i16_1 Int )
(declare-var main@%.420.i15_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.420.i.lcssa_0 Int )
(declare-var main@%.414.i.lcssa_0 Int )
(declare-var main@%.67.i.lcssa_0 Int )
(declare-var main@%.6.i.lcssa_0 Int )
(declare-var main@%.420.i.lcssa_1 Int )
(declare-var main@%.414.i.lcssa_1 Int )
(declare-var main@%.67.i.lcssa_1 Int )
(declare-var main@%.6.i.lcssa_1 Int )
(declare-var main@.lr.ph12_0 Bool )
(declare-var main@%.515.i11_0 Int )
(declare-var main@%.521.i10_0 Int )
(declare-var main@%.515.i11_1 Int )
(declare-var main@%.521.i10_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.521.i.lcssa_0 Int )
(declare-var main@%.515.i.lcssa_0 Int )
(declare-var main@%.521.i.lcssa_1 Int )
(declare-var main@%.515.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%.8.i9.us_0 Int )
(declare-var main@%.89.i8.us_0 Int )
(declare-var main@%.8.i9.us_1 Int )
(declare-var main@%.89.i8.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.8.i.lcssa_0 Int )
(declare-var main@%.8.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%.45.i_0 Int )
(declare-var main@%.4.i_0 Int )
(declare-var main@.lr.ph37_1 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@.lr.ph30_1 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%_32_0 Int )
(declare-var main@.lr.ph26.split.us_1 Bool )
(declare-var main@%_38_0 Int )
(declare-var main@%_39_0 Int )
(declare-var main@%.78.i_0 Int )
(declare-var main@%.7.i_0 Int )
(declare-var main@.lr.ph19_1 Bool )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@.lr.ph12_1 Bool )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Int )
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
         (= main@%_5_0 (> main@%_1_0 0))
         (= main@%_6_0 (> main@%_3_0 0))
         (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
         (=> main@.lr.ph44_0 (and main@.lr.ph44_0 main@entry_0))
         (=> (and main@.lr.ph44_0 main@entry_0) main@%_7_0)
         (=> (and main@.lr.ph44_0 main@entry_0) (= main@%.01.i43_0 1))
         (=> (and main@.lr.ph44_0 main@entry_0) (= main@%.010.i42_0 1))
         (=> (and main@.lr.ph44_0 main@entry_0)
             (= main@%.01.i43_1 main@%.01.i43_0))
         (=> (and main@.lr.ph44_0 main@entry_0)
             (= main@%.010.i42_1 main@%.010.i42_0))
         main@.lr.ph44_0)
    (main@.lr.ph44 main@%_3_0
                   main@%_1_0
                   main@%_7_0
                   main@%_6_0
                   main@%.010.i42_1
                   main@%.01.i43_1)))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                main@%_4_0
                (= main@%_5_0 (> main@%_1_0 0))
                (= main@%_6_0 (> main@%_3_0 0))
                (= main@%_7_0 (ite main@%_5_0 main@%_6_0 false))
                (=> main@.preheader7_0 (and main@.preheader7_0 main@entry_0))
                (=> (and main@.preheader7_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader7_0 main@entry_0)
                    (= main@%.010.i.lcssa_0 1))
                (=> (and main@.preheader7_0 main@entry_0)
                    (= main@%.01.i.lcssa_0 1))
                (=> (and main@.preheader7_0 main@entry_0)
                    (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                (=> (and main@.preheader7_0 main@entry_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> main@.preheader7_0
                    (= main@%.not.i_0 (> main@%.01.i.lcssa_1 main@%_3_0)))
                (=> main@_12_0 (and main@_12_0 main@.preheader7_0))
                (=> (and main@_12_0 main@.preheader7_0)
                    (= main@%.111.i_0 main@%.010.i.lcssa_1))
                (=> (and main@_12_0 main@.preheader7_0)
                    (= main@%.111.i_1 main@%.111.i_0))
                main@_12_0)))
  (=> a!1
      (main@_12 main@%_3_0
                main@%_1_0
                main@%_7_0
                main@%_6_0
                main@%.111.i_1
                main@%.not.i_0))))
(rule (=> (and (main@.lr.ph44 main@%_3_0
                        main@%_1_0
                        main@%_7_0
                        main@%_6_0
                        main@%.010.i42_0
                        main@%.01.i43_0)
         true
         (= main@%_8_0 (+ main@%.010.i42_0 1))
         (= main@%.not29.not.i_0 (< main@%.01.i43_0 main@%_3_0))
         (= main@%spec.select.v.i_0 (ite main@%.not29.not.i_0 2 1))
         (= main@%spec.select.i_0 (+ main@%spec.select.v.i_0 main@%.01.i43_0))
         (= main@%_9_0 (< main@%.010.i42_0 main@%_1_0))
         (= main@%_10_0 (<= main@%spec.select.i_0 main@%_3_0))
         (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
         (=> main@.lr.ph44_1 (and main@.lr.ph44_1 main@.lr.ph44_0))
         (=> (and main@.lr.ph44_1 main@.lr.ph44_0) main@%_11_0)
         (=> (and main@.lr.ph44_1 main@.lr.ph44_0)
             (= main@%.01.i43_1 main@%spec.select.i_0))
         (=> (and main@.lr.ph44_1 main@.lr.ph44_0)
             (= main@%.010.i42_1 main@%_8_0))
         (=> (and main@.lr.ph44_1 main@.lr.ph44_0)
             (= main@%.01.i43_2 main@%.01.i43_1))
         (=> (and main@.lr.ph44_1 main@.lr.ph44_0)
             (= main@%.010.i42_2 main@%.010.i42_1))
         main@.lr.ph44_1)
    (main@.lr.ph44 main@%_3_0
                   main@%_1_0
                   main@%_7_0
                   main@%_6_0
                   main@%.010.i42_2
                   main@%.01.i43_2)))
(rule (let ((a!1 (and (main@.lr.ph44 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%_6_0
                               main@%.010.i42_0
                               main@%.01.i43_0)
                true
                (= main@%_8_0 (+ main@%.010.i42_0 1))
                (= main@%.not29.not.i_0 (< main@%.01.i43_0 main@%_3_0))
                (= main@%spec.select.v.i_0 (ite main@%.not29.not.i_0 2 1))
                (= main@%spec.select.i_0
                   (+ main@%spec.select.v.i_0 main@%.01.i43_0))
                (= main@%_9_0 (< main@%.010.i42_0 main@%_1_0))
                (= main@%_10_0 (<= main@%spec.select.i_0 main@%_3_0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                (=> main@.preheader7_0 (and main@.preheader7_0 main@.lr.ph44_0))
                (=> (and main@.preheader7_0 main@.lr.ph44_0) (not main@%_11_0))
                (=> (and main@.preheader7_0 main@.lr.ph44_0)
                    (= main@%.010.i.lcssa_0 main@%_8_0))
                (=> (and main@.preheader7_0 main@.lr.ph44_0)
                    (= main@%.01.i.lcssa_0 main@%spec.select.i_0))
                (=> (and main@.preheader7_0 main@.lr.ph44_0)
                    (= main@%.010.i.lcssa_1 main@%.010.i.lcssa_0))
                (=> (and main@.preheader7_0 main@.lr.ph44_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> main@.preheader7_0
                    (= main@%.not.i_0 (> main@%.01.i.lcssa_1 main@%_3_0)))
                (=> main@_12_0 (and main@_12_0 main@.preheader7_0))
                (=> (and main@_12_0 main@.preheader7_0)
                    (= main@%.111.i_0 main@%.010.i.lcssa_1))
                (=> (and main@_12_0 main@.preheader7_0)
                    (= main@%.111.i_1 main@%.111.i_0))
                main@_12_0)))
  (=> a!1
      (main@_12 main@%_3_0
                main@%_1_0
                main@%_7_0
                main@%_6_0
                main@%.111.i_1
                main@%.not.i_0))))
(rule (=> (and (main@_12 main@%_3_0
                   main@%_1_0
                   main@%_7_0
                   main@%_6_0
                   main@%.111.i_0
                   main@%.not.i_0)
         true
         (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
         (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
         (= main@%_15_0 (+ main@%.111.i_0 1))
         (=> main@_12_1 (and main@_12_1 main@_12_0))
         (=> (and main@_12_1 main@_12_0) main@%_14_0)
         (=> (and main@_12_1 main@_12_0) (= main@%.111.i_1 main@%_15_0))
         (=> (and main@_12_1 main@_12_0) (= main@%.111.i_2 main@%.111.i_1))
         main@_12_1)
    (main@_12 main@%_3_0
              main@%_1_0
              main@%_7_0
              main@%_6_0
              main@%.111.i_2
              main@%.not.i_0)))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.lr.ph37_0 (and main@.lr.ph37_0 main@.preheader5_0))
                (=> (and main@.lr.ph37_0 main@.preheader5_0) main@%_17_0)
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.3.i36_0 1))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.34.i35_0 1))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.212.i34_0 0))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.218.i33_0 1))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.3.i36_1 main@%.3.i36_0))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.34.i35_1 main@%.34.i35_0))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.212.i34_1 main@%.212.i34_0))
                (=> (and main@.lr.ph37_0 main@.preheader5_0)
                    (= main@%.218.i33_1 main@%.218.i33_0))
                main@.lr.ph37_0)))
  (=> a!1
      (main@.lr.ph37 main@%_3_0
                     main@%_1_0
                     main@%_7_0
                     main@%.212.i34_1
                     main@%.218.i33_1
                     main@%.3.i36_1
                     main@%.34.i35_1))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.lr.ph30_0 (and main@.lr.ph30_0 main@.preheader4_0))
                (=> (and main@.lr.ph30_0 main@.preheader4_0) main@%_19_0)
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.313.i29_0 main@%.212.i.lcssa_1))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.319.i28_0 main@%.218.i.lcssa_1))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.313.i29_1 main@%.313.i29_0))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.319.i28_1 main@%.319.i28_0))
                main@.lr.ph30_0)))
  (=> a!1
      (main@.lr.ph30 main@%_3_0
                     main@%_1_0
                     main@%_7_0
                     main@%.34.i.lcssa_1
                     main@%.3.i.lcssa_1
                     main@%.313.i29_1
                     main@%.319.i28_1))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.lr.ph26.split.us_0
                    (and main@.lr.ph26.split.us_0 main@.preheader3_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    main@%_30_0)
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_0 main@%.3.i.lcssa_1))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_0 main@%.34.i.lcssa_1))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_1 main@%.5.i25.us_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_1 main@%.56.i24.us_0))
                main@.lr.ph26.split.us_0)))
  (=> a!1
      (main@.lr.ph26.split.us
        main@%_3_0
        main@%_1_0
        main@%_7_0
        main@%.319.i.lcssa_1
        main@%.5.i25.us_1
        main@%.56.i24.us_1))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.lr.ph19_0 (and main@.lr.ph19_0 main@.preheader2_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0) main@%_7_0)
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_0 main@%.5.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_0 main@%.319.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_1 main@%.6.i18_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_1 main@%.67.i17_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_1 main@%.414.i16_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_1 main@%.420.i15_0))
                main@.lr.ph19_0)))
  (=> a!1
      (main@.lr.ph19 main@%_3_0
                     main@%_1_0
                     main@%.420.i15_1
                     main@%.414.i16_1
                     main@%.67.i17_1
                     main@%.6.i18_1))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0) main@%_37_0)
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_0 main@%.414.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_0 main@%.420.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_1 main@%.515.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_1 main@%.521.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%_1_0
                     main@%.67.i.lcssa_1
                     main@%.6.i.lcssa_1
                     main@%.521.i10_1
                     main@%.515.i11_1))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@_12 main@%_3_0
                          main@%_1_0
                          main@%_7_0
                          main@%_6_0
                          main@%.111.i_0
                          main@%.not.i_0)
                true
                (= main@%_13_0 (<= main@%.111.i_0 main@%_1_0))
                (= main@%_14_0 (ite main@%_13_0 main@%.not.i_0 false))
                (= main@%_15_0 (+ main@%.111.i_0 1))
                (=> main@.preheader5_0 (and main@.preheader5_0 main@_12_0))
                (=> (and main@.preheader5_0 main@_12_0) (not main@%_14_0))
                (=> main@.preheader5_0 (= main@%_16_0 (> main@%_1_0 (- 1))))
                (=> main@.preheader5_0
                    (= main@%_17_0 (ite main@%_16_0 main@%_6_0 false)))
                (=> main@.preheader4_0
                    (and main@.preheader4_0 main@.preheader5_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (not main@%_17_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_0 0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_0 1))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.preheader5_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph37 main@%_3_0
                        main@%_1_0
                        main@%_7_0
                        main@%.212.i34_0
                        main@%.218.i33_0
                        main@%.3.i36_0
                        main@%.34.i35_0)
         true
         (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
         (= main@%_21_0 (+ main@%.212.i34_0 1))
         (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
         (= main@%_23_0 (+ main@%.34.i35_0 1))
         (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
         (= main@%_24_0 (+ main@%.34.i35_0 2))
         (= main@%.45.i_0 (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
         (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
         (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
         (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
         (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
         (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
         (=> main@.lr.ph37_1 (and main@.lr.ph37_1 main@.lr.ph37_0))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0) main@%_28_0)
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.3.i36_1 main@%.4.i_0))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.34.i35_1 main@%.45.i_0))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.212.i34_1 main@%_21_0))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.218.i33_1 main@%_20_0))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.3.i36_2 main@%.3.i36_1))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.34.i35_2 main@%.34.i35_1))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.212.i34_2 main@%.212.i34_1))
         (=> (and main@.lr.ph37_1 main@.lr.ph37_0)
             (= main@%.218.i33_2 main@%.218.i33_1))
         main@.lr.ph37_1)
    (main@.lr.ph37 main@%_3_0
                   main@%_1_0
                   main@%_7_0
                   main@%.212.i34_2
                   main@%.218.i33_2
                   main@%.3.i36_2
                   main@%.34.i35_2)))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.lr.ph30_0 (and main@.lr.ph30_0 main@.preheader4_0))
                (=> (and main@.lr.ph30_0 main@.preheader4_0) main@%_19_0)
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.313.i29_0 main@%.212.i.lcssa_1))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.319.i28_0 main@%.218.i.lcssa_1))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.313.i29_1 main@%.313.i29_0))
                (=> (and main@.lr.ph30_0 main@.preheader4_0)
                    (= main@%.319.i28_1 main@%.319.i28_0))
                main@.lr.ph30_0)))
  (=> a!1
      (main@.lr.ph30 main@%_3_0
                     main@%_1_0
                     main@%_7_0
                     main@%.34.i.lcssa_1
                     main@%.3.i.lcssa_1
                     main@%.313.i29_1
                     main@%.319.i28_1))))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.lr.ph26.split.us_0
                    (and main@.lr.ph26.split.us_0 main@.preheader3_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    main@%_30_0)
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_0 main@%.3.i.lcssa_1))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_0 main@%.34.i.lcssa_1))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_1 main@%.5.i25.us_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_1 main@%.56.i24.us_0))
                main@.lr.ph26.split.us_0)))
  (=> a!1
      (main@.lr.ph26.split.us
        main@%_3_0
        main@%_1_0
        main@%_7_0
        main@%.319.i.lcssa_1
        main@%.5.i25.us_1
        main@%.56.i24.us_1))))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.lr.ph19_0 (and main@.lr.ph19_0 main@.preheader2_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0) main@%_7_0)
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_0 main@%.5.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_0 main@%.319.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_1 main@%.6.i18_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_1 main@%.67.i17_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_1 main@%.414.i16_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_1 main@%.420.i15_0))
                main@.lr.ph19_0)))
  (=> a!1
      (main@.lr.ph19 main@%_3_0
                     main@%_1_0
                     main@%.420.i15_1
                     main@%.414.i16_1
                     main@%.67.i17_1
                     main@%.6.i18_1))))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0) main@%_37_0)
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_0 main@%.414.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_0 main@%.420.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_1 main@%.515.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_1 main@%.521.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%_1_0
                     main@%.67.i.lcssa_1
                     main@%.6.i.lcssa_1
                     main@%.521.i10_1
                     main@%.515.i11_1))))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph37 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.212.i34_0
                               main@%.218.i33_0
                               main@%.3.i36_0
                               main@%.34.i35_0)
                true
                (= main@%_20_0 (+ main@%.212.i34_0 main@%.218.i33_0))
                (= main@%_21_0 (+ main@%.212.i34_0 1))
                (= main@%_22_0 (+ main@%.3.i36_0 main@%.34.i35_0))
                (= main@%_23_0 (+ main@%.34.i35_0 1))
                (= main@%.not28.not.i_0 (< main@%.34.i35_0 main@%_3_0))
                (= main@%_24_0 (+ main@%.34.i35_0 2))
                (= main@%.45.i_0
                   (ite main@%.not28.not.i_0 main@%_24_0 main@%_23_0))
                (= main@%_25_0 (ite main@%.not28.not.i_0 main@%_23_0 0))
                (= main@%.4.i_0 (+ main@%_22_0 main@%_25_0))
                (= main@%_26_0 (< main@%.212.i34_0 main@%_1_0))
                (= main@%_27_0 (<= main@%.45.i_0 main@%_3_0))
                (= main@%_28_0 (ite main@%_26_0 main@%_27_0 false))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@.lr.ph37_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0) (not main@%_28_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_0 main@%_20_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_0 main@%_21_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_0 main@%.45.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_0 main@%.4.i_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.218.i.lcssa_1 main@%.218.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.34.i.lcssa_1 main@%.34.i.lcssa_0))
                (=> (and main@.preheader4_0 main@.lr.ph37_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader4_0
                    (= main@%.not23.i_0 (> main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader4_0
                    (= main@%_18_0 (<= main@%.212.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader4_0
                    (= main@%_19_0 (ite main@%_18_0 main@%.not23.i_0 false)))
                (=> main@.preheader3_0
                    (and main@.preheader3_0 main@.preheader4_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (not main@%_19_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_0 main@%.218.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_0 main@%.212.i.lcssa_1))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.preheader4_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_1))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph30 main@%_3_0
                        main@%_1_0
                        main@%_7_0
                        main@%.34.i.lcssa_0
                        main@%.3.i.lcssa_0
                        main@%.313.i29_0
                        main@%.319.i28_0)
         true
         (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
         (= main@%_34_0 (+ main@%.313.i29_0 1))
         (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
         (=> main@.lr.ph30_1 (and main@.lr.ph30_1 main@.lr.ph30_0))
         (=> (and main@.lr.ph30_1 main@.lr.ph30_0) main@%_35_0)
         (=> (and main@.lr.ph30_1 main@.lr.ph30_0)
             (= main@%.313.i29_1 main@%_34_0))
         (=> (and main@.lr.ph30_1 main@.lr.ph30_0)
             (= main@%.319.i28_1 main@%_33_0))
         (=> (and main@.lr.ph30_1 main@.lr.ph30_0)
             (= main@%.313.i29_2 main@%.313.i29_1))
         (=> (and main@.lr.ph30_1 main@.lr.ph30_0)
             (= main@%.319.i28_2 main@%.319.i28_1))
         main@.lr.ph30_1)
    (main@.lr.ph30 main@%_3_0
                   main@%_1_0
                   main@%_7_0
                   main@%.34.i.lcssa_0
                   main@%.3.i.lcssa_0
                   main@%.313.i29_2
                   main@%.319.i28_2)))
(rule (let ((a!1 (and (main@.lr.ph30 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.34.i.lcssa_0
                               main@%.3.i.lcssa_0
                               main@%.313.i29_0
                               main@%.319.i28_0)
                true
                (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
                (= main@%_34_0 (+ main@%.313.i29_0 1))
                (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph30_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0) (not main@%_35_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_0 main@%_34_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.lr.ph26.split.us_0
                    (and main@.lr.ph26.split.us_0 main@.preheader3_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    main@%_30_0)
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_0 main@%.3.i.lcssa_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_0 main@%.34.i.lcssa_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.5.i25.us_1 main@%.5.i25.us_0))
                (=> (and main@.lr.ph26.split.us_0 main@.preheader3_0)
                    (= main@%.56.i24.us_1 main@%.56.i24.us_0))
                main@.lr.ph26.split.us_0)))
  (=> a!1
      (main@.lr.ph26.split.us
        main@%_3_0
        main@%_1_0
        main@%_7_0
        main@%.319.i.lcssa_1
        main@%.5.i25.us_1
        main@%.56.i24.us_1))))
(rule (let ((a!1 (and (main@.lr.ph30 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.34.i.lcssa_0
                               main@%.3.i.lcssa_0
                               main@%.313.i29_0
                               main@%.319.i28_0)
                true
                (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
                (= main@%_34_0 (+ main@%.313.i29_0 1))
                (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph30_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0) (not main@%_35_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_0 main@%_34_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.lr.ph19_0 (and main@.lr.ph19_0 main@.preheader2_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0) main@%_7_0)
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_0 main@%.5.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_0 1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_0 main@%.319.i.lcssa_1))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.6.i18_1 main@%.6.i18_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.67.i17_1 main@%.67.i17_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.414.i16_1 main@%.414.i16_0))
                (=> (and main@.lr.ph19_0 main@.preheader2_0)
                    (= main@%.420.i15_1 main@%.420.i15_0))
                main@.lr.ph19_0)))
  (=> a!1
      (main@.lr.ph19 main@%_3_0
                     main@%_1_0
                     main@%.420.i15_1
                     main@%.414.i16_1
                     main@%.67.i17_1
                     main@%.6.i18_1))))
(rule (let ((a!1 (and (main@.lr.ph30 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.34.i.lcssa_0
                               main@%.3.i.lcssa_0
                               main@%.313.i29_0
                               main@%.319.i28_0)
                true
                (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
                (= main@%_34_0 (+ main@%.313.i29_0 1))
                (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph30_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0) (not main@%_35_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_0 main@%_34_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0) main@%_37_0)
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_0 main@%.414.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_0 main@%.420.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_1 main@%.515.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_1 main@%.521.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%_1_0
                     main@%.67.i.lcssa_1
                     main@%.6.i.lcssa_1
                     main@%.521.i10_1
                     main@%.515.i11_1))))
(rule (let ((a!1 (and (main@.lr.ph30 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.34.i.lcssa_0
                               main@%.3.i.lcssa_0
                               main@%.313.i29_0
                               main@%.319.i28_0)
                true
                (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
                (= main@%_34_0 (+ main@%.313.i29_0 1))
                (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph30_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0) (not main@%_35_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_0 main@%_34_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph30 main@%_3_0
                               main@%_1_0
                               main@%_7_0
                               main@%.34.i.lcssa_0
                               main@%.3.i.lcssa_0
                               main@%.313.i29_0
                               main@%.319.i28_0)
                true
                (= main@%_33_0 (+ main@%.313.i29_0 main@%.319.i28_0))
                (= main@%_34_0 (+ main@%.313.i29_0 1))
                (= main@%_35_0 (< main@%.313.i29_0 main@%_1_0))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.lr.ph30_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0) (not main@%_35_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_0 main@%_33_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_0 main@%_34_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.319.i.lcssa_1 main@%.319.i.lcssa_0))
                (=> (and main@.preheader3_0 main@.lr.ph30_0)
                    (= main@%.313.i.lcssa_1 main@%.313.i.lcssa_0))
                (=> main@.preheader3_0
                    (= main@%.not24.i_0 (> main@%.313.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader3_0
                    (= main@%_29_0 (<= main@%.34.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader3_0
                    (= main@%_30_0 (ite main@%.not24.i_0 main@%_29_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_30_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph26.split.us
           main@%_3_0
           main@%_1_0
           main@%_7_0
           main@%.319.i.lcssa_0
           main@%.5.i25.us_0
           main@%.56.i24.us_0)
         true
         (= main@%_31_0 (+ main@%.5.i25.us_0 main@%.56.i24.us_0))
         (= main@%_32_0 (+ main@%.56.i24.us_0 1))
         (= main@%.not.not47_0 (< main@%.56.i24.us_0 main@%_3_0))
         (=> main@.lr.ph26.split.us_1
             (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0))
         (=> (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0)
             main@%.not.not47_0)
         (=> (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0)
             (= main@%.5.i25.us_1 main@%_31_0))
         (=> (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0)
             (= main@%.56.i24.us_1 main@%_32_0))
         (=> (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0)
             (= main@%.5.i25.us_2 main@%.5.i25.us_1))
         (=> (and main@.lr.ph26.split.us_1 main@.lr.ph26.split.us_0)
             (= main@%.56.i24.us_2 main@%.56.i24.us_1))
         main@.lr.ph26.split.us_1)
    (main@.lr.ph26.split.us
      main@%_3_0
      main@%_1_0
      main@%_7_0
      main@%.319.i.lcssa_0
      main@%.5.i25.us_2
      main@%.56.i24.us_2)))
(rule (=> (and (main@.lr.ph26.split.us
           main@%_3_0
           main@%_1_0
           main@%_7_0
           main@%.319.i.lcssa_0
           main@%.5.i25.us_0
           main@%.56.i24.us_0)
         true
         (= main@%_31_0 (+ main@%.5.i25.us_0 main@%.56.i24.us_0))
         (= main@%_32_0 (+ main@%.56.i24.us_0 1))
         (= main@%.not.not47_0 (< main@%.56.i24.us_0 main@%_3_0))
         (=> main@.preheader2_0
             (and main@.preheader2_0 main@.lr.ph26.split.us_0))
         (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
             (not main@%.not.not47_0))
         (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
             (= main@%.5.i.lcssa_0 main@%_31_0))
         (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
             (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
         (=> main@.lr.ph19_0 (and main@.lr.ph19_0 main@.preheader2_0))
         (=> (and main@.lr.ph19_0 main@.preheader2_0) main@%_7_0)
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.6.i18_0 main@%.5.i.lcssa_1))
         (=> (and main@.lr.ph19_0 main@.preheader2_0) (= main@%.67.i17_0 1))
         (=> (and main@.lr.ph19_0 main@.preheader2_0) (= main@%.414.i16_0 1))
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.420.i15_0 main@%.319.i.lcssa_0))
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.6.i18_1 main@%.6.i18_0))
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.67.i17_1 main@%.67.i17_0))
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.414.i16_1 main@%.414.i16_0))
         (=> (and main@.lr.ph19_0 main@.preheader2_0)
             (= main@%.420.i15_1 main@%.420.i15_0))
         main@.lr.ph19_0)
    (main@.lr.ph19 main@%_3_0
                   main@%_1_0
                   main@%.420.i15_1
                   main@%.414.i16_1
                   main@%.67.i17_1
                   main@%.6.i18_1)))
(rule (let ((a!1 (and (main@.lr.ph26.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%_7_0
                  main@%.319.i.lcssa_0
                  main@%.5.i25.us_0
                  main@%.56.i24.us_0)
                true
                (= main@%_31_0 (+ main@%.5.i25.us_0 main@%.56.i24.us_0))
                (= main@%_32_0 (+ main@%.56.i24.us_0 1))
                (= main@%.not.not47_0 (< main@%.56.i24.us_0 main@%_3_0))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.lr.ph26.split.us_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (not main@%.not.not47_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_0 main@%_31_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0) main@%_37_0)
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_0 main@%.414.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_0 main@%.420.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_1 main@%.515.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_1 main@%.521.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%_1_0
                     main@%.67.i.lcssa_1
                     main@%.6.i.lcssa_1
                     main@%.521.i10_1
                     main@%.515.i11_1))))
(rule (let ((a!1 (and (main@.lr.ph26.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%_7_0
                  main@%.319.i.lcssa_0
                  main@%.5.i25.us_0
                  main@%.56.i24.us_0)
                true
                (= main@%_31_0 (+ main@%.5.i25.us_0 main@%.56.i24.us_0))
                (= main@%_32_0 (+ main@%.56.i24.us_0 1))
                (= main@%.not.not47_0 (< main@%.56.i24.us_0 main@%_3_0))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.lr.ph26.split.us_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (not main@%.not.not47_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_0 main@%_31_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph26.split.us
                  main@%_3_0
                  main@%_1_0
                  main@%_7_0
                  main@%.319.i.lcssa_0
                  main@%.5.i25.us_0
                  main@%.56.i24.us_0)
                true
                (= main@%_31_0 (+ main@%.5.i25.us_0 main@%.56.i24.us_0))
                (= main@%_32_0 (+ main@%.56.i24.us_0 1))
                (= main@%.not.not47_0 (< main@%.56.i24.us_0 main@%_3_0))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.lr.ph26.split.us_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (not main@%.not.not47_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_0 main@%_31_0))
                (=> (and main@.preheader2_0 main@.lr.ph26.split.us_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.preheader2_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_0 main@%.319.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_0 1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_0 main@%.5.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.preheader2_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph19 main@%_3_0
                        main@%_1_0
                        main@%.420.i15_0
                        main@%.414.i16_0
                        main@%.67.i17_0
                        main@%.6.i18_0)
         true
         (= main@%_38_0 (* main@%.420.i15_0 2))
         (= main@%_39_0 (+ main@%.414.i16_0 1))
         (= main@%.not27.not.i_0 (< main@%.67.i17_0 main@%_3_0))
         (= main@%.78.v.i_0 (ite main@%.not27.not.i_0 2 1))
         (= main@%.78.i_0 (+ main@%.78.v.i_0 main@%.67.i17_0))
         (= main@%.7.v.i_0 (ite main@%.not27.not.i_0 4 2))
         (= main@%_40_0 (< main@%.414.i16_0 main@%_1_0))
         (= main@%_41_0 (<= main@%.78.i_0 main@%_3_0))
         (= main@%_42_0 (ite main@%_40_0 main@%_41_0 false))
         (=> main@.lr.ph19_1 (and main@.lr.ph19_1 main@.lr.ph19_0))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0) main@%_42_0)
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.6.i18_1 main@%.7.i_0))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.67.i17_1 main@%.78.i_0))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.414.i16_1 main@%_39_0))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.420.i15_1 main@%_38_0))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.6.i18_2 main@%.6.i18_1))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.67.i17_2 main@%.67.i17_1))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.414.i16_2 main@%.414.i16_1))
         (=> (and main@.lr.ph19_1 main@.lr.ph19_0)
             (= main@%.420.i15_2 main@%.420.i15_1))
         main@.lr.ph19_1)
    (main@.lr.ph19 main@%_3_0
                   main@%_1_0
                   main@%.420.i15_2
                   main@%.414.i16_2
                   main@%.67.i17_2
                   main@%.6.i18_2)))
(rule (let ((a!1 (and (main@.lr.ph19 main@%_3_0
                               main@%_1_0
                               main@%.420.i15_0
                               main@%.414.i16_0
                               main@%.67.i17_0
                               main@%.6.i18_0)
                true
                (= main@%_38_0 (* main@%.420.i15_0 2))
                (= main@%_39_0 (+ main@%.414.i16_0 1))
                (= main@%.not27.not.i_0 (< main@%.67.i17_0 main@%_3_0))
                (= main@%.78.v.i_0 (ite main@%.not27.not.i_0 2 1))
                (= main@%.78.i_0 (+ main@%.78.v.i_0 main@%.67.i17_0))
                (= main@%.7.v.i_0 (ite main@%.not27.not.i_0 4 2))
                (= main@%_40_0 (< main@%.414.i16_0 main@%_1_0))
                (= main@%_41_0 (<= main@%.78.i_0 main@%_3_0))
                (= main@%_42_0 (ite main@%_40_0 main@%_41_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph19_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0) (not main@%_42_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_0 main@%_38_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_0 main@%_39_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_0 main@%.78.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_0 main@%.7.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.lr.ph12_0 (and main@.lr.ph12_0 main@.preheader1_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0) main@%_37_0)
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_0 main@%.414.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_0 main@%.420.i.lcssa_1))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.515.i11_1 main@%.515.i11_0))
                (=> (and main@.lr.ph12_0 main@.preheader1_0)
                    (= main@%.521.i10_1 main@%.521.i10_0))
                main@.lr.ph12_0)))
  (=> a!1
      (main@.lr.ph12 main@%_3_0
                     main@%_1_0
                     main@%.67.i.lcssa_1
                     main@%.6.i.lcssa_1
                     main@%.521.i10_1
                     main@%.515.i11_1))))
(rule (let ((a!1 (and (main@.lr.ph19 main@%_3_0
                               main@%_1_0
                               main@%.420.i15_0
                               main@%.414.i16_0
                               main@%.67.i17_0
                               main@%.6.i18_0)
                true
                (= main@%_38_0 (* main@%.420.i15_0 2))
                (= main@%_39_0 (+ main@%.414.i16_0 1))
                (= main@%.not27.not.i_0 (< main@%.67.i17_0 main@%_3_0))
                (= main@%.78.v.i_0 (ite main@%.not27.not.i_0 2 1))
                (= main@%.78.i_0 (+ main@%.78.v.i_0 main@%.67.i17_0))
                (= main@%.7.v.i_0 (ite main@%.not27.not.i_0 4 2))
                (= main@%_40_0 (< main@%.414.i16_0 main@%_1_0))
                (= main@%_41_0 (<= main@%.78.i_0 main@%_3_0))
                (= main@%_42_0 (ite main@%_40_0 main@%_41_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph19_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0) (not main@%_42_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_0 main@%_38_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_0 main@%_39_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_0 main@%.78.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_0 main@%.7.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_1))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph19 main@%_3_0
                               main@%_1_0
                               main@%.420.i15_0
                               main@%.414.i16_0
                               main@%.67.i17_0
                               main@%.6.i18_0)
                true
                (= main@%_38_0 (* main@%.420.i15_0 2))
                (= main@%_39_0 (+ main@%.414.i16_0 1))
                (= main@%.not27.not.i_0 (< main@%.67.i17_0 main@%_3_0))
                (= main@%.78.v.i_0 (ite main@%.not27.not.i_0 2 1))
                (= main@%.78.i_0 (+ main@%.78.v.i_0 main@%.67.i17_0))
                (= main@%.7.v.i_0 (ite main@%.not27.not.i_0 4 2))
                (= main@%_40_0 (< main@%.414.i16_0 main@%_1_0))
                (= main@%_41_0 (<= main@%.78.i_0 main@%_3_0))
                (= main@%_42_0 (ite main@%_40_0 main@%_41_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph19_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0) (not main@%_42_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_0 main@%_38_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_0 main@%_39_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_0 main@%.78.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_0 main@%.7.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.420.i.lcssa_1 main@%.420.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.414.i.lcssa_1 main@%.414.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.67.i.lcssa_1 main@%.67.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph19_0)
                    (= main@%.6.i.lcssa_1 main@%.6.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%.not25.i_0 (> main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader1_0
                    (= main@%_36_0 (<= main@%.414.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader1_0
                    (= main@%_37_0 (ite main@%_36_0 main@%.not25.i_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_37_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_0 main@%.420.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_0 main@%.414.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_1 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_1))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph12 main@%_3_0
                        main@%_1_0
                        main@%.67.i.lcssa_0
                        main@%.6.i.lcssa_0
                        main@%.521.i10_0
                        main@%.515.i11_0)
         true
         (= main@%_47_0 (* main@%.521.i10_0 2))
         (= main@%_48_0 (+ main@%.515.i11_0 1))
         (= main@%_49_0 (< main@%.515.i11_0 main@%_1_0))
         (=> main@.lr.ph12_1 (and main@.lr.ph12_1 main@.lr.ph12_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0) main@%_49_0)
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.515.i11_1 main@%_48_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.521.i10_1 main@%_47_0))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.515.i11_2 main@%.515.i11_1))
         (=> (and main@.lr.ph12_1 main@.lr.ph12_0)
             (= main@%.521.i10_2 main@%.521.i10_1))
         main@.lr.ph12_1)
    (main@.lr.ph12 main@%_3_0
                   main@%_1_0
                   main@%.67.i.lcssa_0
                   main@%.6.i.lcssa_0
                   main@%.521.i10_2
                   main@%.515.i11_2)))
(rule (let ((a!1 (and (main@.lr.ph12 main@%_3_0
                               main@%_1_0
                               main@%.67.i.lcssa_0
                               main@%.6.i.lcssa_0
                               main@%.521.i10_0
                               main@%.515.i11_0)
                true
                (= main@%_47_0 (* main@%.521.i10_0 2))
                (= main@%_48_0 (+ main@%.515.i11_0 1))
                (= main@%_49_0 (< main@%.515.i11_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph12_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0) (not main@%_49_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.521.i.lcssa_0 main@%_47_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.515.i.lcssa_0 main@%_48_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_44_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_0 main@%.6.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_0 main@%.67.i.lcssa_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.8.i9.us_1 main@%.8.i9.us_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.89.i8.us_1 main@%.89.i8.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        main@%.521.i.lcssa_1
        main@%.8.i9.us_1
        main@%.89.i8.us_1
        main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph12 main@%_3_0
                               main@%_1_0
                               main@%.67.i.lcssa_0
                               main@%.6.i.lcssa_0
                               main@%.521.i10_0
                               main@%.515.i11_0)
                true
                (= main@%_47_0 (* main@%.521.i10_0 2))
                (= main@%_48_0 (+ main@%.515.i11_0 1))
                (= main@%_49_0 (< main@%.515.i11_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph12_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0) (not main@%_49_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.521.i.lcssa_0 main@%_47_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.515.i.lcssa_0 main@%_48_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.521.i.lcssa_1 main@%.521.i.lcssa_0))
                (=> (and main@.preheader_0 main@.lr.ph12_0)
                    (= main@%.515.i.lcssa_1 main@%.515.i.lcssa_0))
                (=> main@.preheader_0
                    (= main@%.not26.i_0 (> main@%.515.i.lcssa_1 main@%_1_0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (<= main@%.67.i.lcssa_0 main@%_3_0)))
                (=> main@.preheader_0
                    (= main@%_44_0 (ite main@%.not26.i_0 main@%_43_0 false)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_44_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_0 main@%.6.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_1 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph.split.us
           main@%.521.i.lcssa_0
           main@%.8.i9.us_0
           main@%.89.i8.us_0
           main@%_3_0)
         true
         (= main@%_45_0 (* main@%.8.i9.us_0 2))
         (= main@%_46_0 (+ main@%.89.i8.us_0 1))
         (= main@%.not.not_0 (< main@%.89.i8.us_0 main@%_3_0))
         (=> main@.lr.ph.split.us_1
             (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             main@%.not.not_0)
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.8.i9.us_1 main@%_45_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.89.i8.us_1 main@%_46_0))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.8.i9.us_2 main@%.8.i9.us_1))
         (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
             (= main@%.89.i8.us_2 main@%.89.i8.us_1))
         main@.lr.ph.split.us_1)
    (main@.lr.ph.split.us
      main@%.521.i.lcssa_0
      main@%.8.i9.us_2
      main@%.89.i8.us_2
      main@%_3_0)))
(rule (let ((a!1 (and (main@.lr.ph.split.us
                  main@%.521.i.lcssa_0
                  main@%.8.i9.us_0
                  main@%.89.i8.us_0
                  main@%_3_0)
                true
                (= main@%_45_0 (* main@%.8.i9.us_0 2))
                (= main@%_46_0 (+ main@%.89.i8.us_0 1))
                (= main@%.not.not_0 (< main@%.89.i8.us_0 main@%_3_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph.split.us_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (not main@%.not.not_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.8.i.lcssa_0 main@%_45_0))
                (=> (and main@verifier.error_0 main@.lr.ph.split.us_0)
                    (= main@%.8.i.lcssa_1 main@%.8.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_50_0 (= main@%.521.i.lcssa_0 main@%.8.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_50_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

