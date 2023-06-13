(set-info :original "./results/chc/bytecode/antonopoulos/count-loops/array-insert.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) Int ))
(declare-rel main@.lr.ph87 (Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int Int Int Int Int ))
(declare-rel main@.critedge14.i (Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int Int Int ))
(declare-rel main@.critedge14.i.us (Int (Array Int Int) Int Int (Array Int Int) Int Int Int Bool Int Int Int ))
(declare-rel main@.lr.ph71 (Int (Array Int Int) Int Int (Array Int Int) Int Int Int Int Int ))
(declare-rel main@.lr.ph75 (Int (Array Int Int) Int Int (Array Int Int) Int Int Bool Int Int ))
(declare-rel main@.lr.ph (Int Int Int ))
(declare-rel main@_75 (Int Int Int Bool ))
(declare-rel main@.preheader.split.us (Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_82_0 Bool )
(declare-var main@%_80_0 Bool )
(declare-var main@%_79_0 Bool )
(declare-var main@%_76_0 Bool )
(declare-var main@%_77_0 Bool )
(declare-var main@%_71_0 Bool )
(declare-var main@%spec.select15.v.i_0 Int )
(declare-var main@%_72_0 Bool )
(declare-var main@%_73_0 Bool )
(declare-var main@%_74_0 Bool )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_65_0 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_66_0 Bool )
(declare-var main@%_67_0 Bool )
(declare-var main@%_68_0 Bool )
(declare-var main@%.3.i3_2 Int )
(declare-var main@%.212.i2_2 Int )
(declare-var main@%_59_0 Bool )
(declare-var main@%or.cond9.i.us_0 Bool )
(declare-var main@%_55_0 Int )
(declare-var main@%_56_0 Int )
(declare-var main@%_57_0 Bool )
(declare-var main@%.pre28_0 Int )
(declare-var main@%_54_0 Bool )
(declare-var main@%or.cond9.i.us73_0 Bool )
(declare-var main@%_41_0 Int )
(declare-var main@%_42_0 Int )
(declare-var main@%_43_0 Bool )
(declare-var main@%brmerge_0 Bool )
(declare-var main@%.old8.i_0 Bool )
(declare-var main@%_60_0 Int )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Bool )
(declare-var main@%.old8.i69_0 Bool )
(declare-var main@%_45_0 Bool )
(declare-var main@%.pre_0 Int )
(declare-var main@%.111.i5.us1878_2 Int )
(declare-var main@%_46_0 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Bool )
(declare-var main@%_50_0 Bool )
(declare-var main@%.111.i583_2 Int )
(declare-var main@%_35_0 Bool )
(declare-var main@%_36_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_33_0 Bool )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_31_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @A_left_0 Int )
(declare-var @A_right_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%loop.bound4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@.lr.ph87_0 Bool )
(declare-var main@%.010.i1686_0 Int )
(declare-var main@%.0.i1785_0 Int )
(declare-var main@%.010.i1686_1 Int )
(declare-var main@%.0.i1785_1 Int )
(declare-var main@.lr.ph7_0 Bool )
(declare-var main@%.0.i17.lcssa_0 Int )
(declare-var main@%.010.i16.lcssa_0 Int )
(declare-var main@%.0.i17.lcssa_1 Int )
(declare-var main@%.010.i16.lcssa_1 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@.lr.ph7.split.preheader_0 Bool )
(declare-var main@.critedge14.i_0 Bool )
(declare-var main@%.111.i583_0 Int )
(declare-var main@%.111.i583_1 Int )
(declare-var main@.lr.ph7.split.us_0 Bool )
(declare-var main@.lr.ph19.preheader_0 Bool )
(declare-var main@%_39_0 Bool )
(declare-var main@.critedge14.i.us_0 Bool )
(declare-var main@%.111.i5.us1878_0 Int )
(declare-var main@%.111.i5.us1878_1 Int )
(declare-var main@.critedge3.i.split.us.preheader_0 Bool )
(declare-var |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)| Bool )
(declare-var |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)| Bool )
(declare-var |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)| Bool )
(declare-var main@%.111.i.lcssa39_0 Int )
(declare-var main@%.111.i.lcssa39_1 Int )
(declare-var main@%.111.i.lcssa39_2 Int )
(declare-var main@%.111.i.lcssa39_3 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%_53_0 Bool )
(declare-var main@.lr.ph75_0 Bool )
(declare-var main@%.2.i.us74_0 Int )
(declare-var main@%.2.i.us74_1 Int )
(declare-var main@.critedge5.i_0 Bool )
(declare-var main@%_64_0 Int )
(declare-var main@%.111.i.lcssa38_0 Int )
(declare-var main@%.2.i.lcssa_0 Int )
(declare-var main@%_64_1 Int )
(declare-var main@%.111.i.lcssa38_1 Int )
(declare-var main@%.2.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.3.i3_0 Int )
(declare-var main@%.212.i2_0 Int )
(declare-var main@%.3.i3_1 Int )
(declare-var main@%.212.i2_1 Int )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%.212.i.lcssa_0 Int )
(declare-var main@%.3.i.lcssa_0 Int )
(declare-var main@%.212.i.lcssa_1 Int )
(declare-var main@%.3.i.lcssa_1 Int )
(declare-var main@%_69_0 Bool )
(declare-var main@_75_0 Bool )
(declare-var main@%.313.i_0 Int )
(declare-var main@%.313.i_1 Int )
(declare-var main@_23_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@_27_0 Bool )
(declare-var main@%spec.select.i_0 Int )
(declare-var main@_32_0 Bool )
(declare-var |tuple(main@_23_0, main@_32_0)| Bool )
(declare-var main@%.1.i_0 Int )
(declare-var main@%.1.i_1 Int )
(declare-var main@%.1.i_2 Int )
(declare-var main@_15_0 Bool )
(declare-var main@.lr.ph87_1 Bool )
(declare-var main@%.010.i1686_2 Int )
(declare-var main@%.0.i1785_2 Int )
(declare-var |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| Bool )
(declare-var |tuple(main@_15_0, main@.lr.ph7_0)| Bool )
(declare-var main@%.0.i17.lcssa_2 Int )
(declare-var main@%.010.i16.lcssa_2 Int )
(declare-var main@.critedge3.i.split.preheader_0 Bool )
(declare-var main@%.111.i.lcssa47_0 Int )
(declare-var main@%.0.i.lcssa3346_0 Int )
(declare-var main@%.111.i.lcssa47_1 Int )
(declare-var main@%.0.i.lcssa3346_1 Int )
(declare-var main@%_51_0 Int )
(declare-var main@.lr.ph71_0 Bool )
(declare-var main@%.2.i70_0 Int )
(declare-var main@%.2.i70_1 Int )
(declare-var |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)| Bool )
(declare-var |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)| Bool )
(declare-var main@%_64_2 Int )
(declare-var main@%.111.i.lcssa38_2 Int )
(declare-var main@%.2.i.lcssa_2 Int )
(declare-var main@%_49_0 Int )
(declare-var main@.lr.ph7.split_0 Bool )
(declare-var main@.critedge14.i_1 Bool )
(declare-var main@%_44_0 Int )
(declare-var main@_40_0 Bool )
(declare-var main@.critedge14.i.us_1 Bool )
(declare-var main@.critedge3.i.split_0 Bool )
(declare-var main@%_63_0 Int )
(declare-var main@.lr.ph71_1 Bool )
(declare-var main@%.2.i70_2 Int )
(declare-var |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)| Bool )
(declare-var |tuple(main@.lr.ph71_0, main@.critedge5.i_0)| Bool )
(declare-var main@.critedge3.i.split.us_0 Bool )
(declare-var main@%_58_0 Int )
(declare-var main@.lr.ph75_1 Bool )
(declare-var main@%.2.i.us74_2 Int )
(declare-var |tuple(main@.lr.ph75_0, main@.critedge5.i_0)| Bool )
(declare-var |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)| Bool )
(declare-var main@%_70_0 Int )
(declare-var main@%spec.select15.i_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@%_78_0 Int )
(declare-var main@_75_1 Bool )
(declare-var main@%.313.i_2 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@.preheader.split.us_0 Bool )
(declare-var main@%.5.i.us_0 Int )
(declare-var main@%.5.i.us_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.5.i.lcssa_0 Int )
(declare-var main@%.5.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_81_0 Int )
(declare-var main@.preheader.split.us_1 Bool )
(declare-var main@%.5.i.us_2 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0))
(rule (let ((a!1 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                (= main@%_12_0 (+ @A_left_0 (* 0 44) (* 0 4)))
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph87_0 (and main@.lr.ph87_0 main@entry_0))
                (=> (and main@.lr.ph87_0 main@entry_0) main@%_14_0)
                (=> (and main@.lr.ph87_0 main@entry_0) (= main@%.010.i1686_0 0))
                (=> (and main@.lr.ph87_0 main@entry_0) (= main@%.0.i1785_0 0))
                (=> (and main@.lr.ph87_0 main@entry_0)
                    (= main@%.010.i1686_1 main@%.010.i1686_0))
                (=> (and main@.lr.ph87_0 main@entry_0)
                    (= main@%.0.i1785_1 main@%.0.i1785_0))
                main@.lr.ph87_0)))
  (=> a!1
      (main@.lr.ph87 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     @A_left_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%.010.i1686_1
                     main@%.0.i1785_1
                     main@%loop.bound4_0))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (=> main@.lr.ph7_0
               (= main@%_34_0
                  (+ @A_right_0 (* 0 44) (* main@%.0.i17.lcssa_1 4)))))
      (a!3 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_1 4)))))
(let ((a!4 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                a!1
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) (not main@%_14_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_1 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_1 main@%.010.i16.lcssa_0))
                a!2
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.lr.ph7_0 a!3)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.critedge14.i_0
                    (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0))
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    main@%_38_0)
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    (= main@%.111.i583_0 main@%.010.i16.lcssa_1))
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    (= main@%.111.i583_1 main@%.111.i583_0))
                main@.critedge14.i_0)))
  (=> a!4
      (main@.critedge14.i
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_1
        main@%loop.bound1_0
        main@%.111.i583_1
        main@%loop.bound3_0)))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (=> main@.lr.ph7_0
               (= main@%_34_0
                  (+ @A_right_0 (* 0 44) (* main@%.0.i17.lcssa_1 4)))))
      (a!3 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_1 4)))))
(let ((a!4 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                a!1
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) (not main@%_14_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_1 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_1 main@%.010.i16.lcssa_0))
                a!2
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.lr.ph7_0 a!3)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> main@.critedge14.i.us_0
                    (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (not main@%_39_0))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (= main@%.111.i5.us1878_0 main@%.010.i16.lcssa_1))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (= main@%.111.i5.us1878_1 main@%.111.i5.us1878_0))
                main@.critedge14.i.us_0)))
  (=> a!4
      (main@.critedge14.i.us
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_1
        main@%_39_0
        main@%.111.i5.us1878_1
        main@%loop.bound1_0
        main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (=> main@.lr.ph7_0
               (= main@%_34_0
                  (+ @A_right_0 (* 0 44) (* main@%.0.i17.lcssa_1 4)))))
      (a!3 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_1 4))))
      (a!4 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4)))))
(let ((a!5 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                a!1
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) (not main@%_14_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_1 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_1 main@%.010.i16.lcssa_0))
                a!2
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.lr.ph7_0 a!3)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!4)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph75_0
                    (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    main@%or.cond9.i.us73_0)
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_0 main@%.0.i17.lcssa_1))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_1 main@%.2.i.us74_0))
                main@.lr.ph75_0)))
  (=> a!5
      (main@.lr.ph75 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i.us74_1
                     main@%_53_0
                     main@%_52_0
                     main@%.111.i.lcssa39_3)))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_1 4))))
      (a!3 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_1 4))))
      (a!4 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4))))
      (a!5 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_1 4)))))
(let ((a!6 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                a!1
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) (not main@%_14_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_1 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_1 main@%.010.i16.lcssa_0))
                (=> main@.lr.ph7_0 a!2)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.lr.ph7_0 a!3)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!4)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.critedge5.i_0
                    (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (not main@%or.cond9.i.us73_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%_64_0 main@%_52_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_3))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_1))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%_64_1 main@%_64_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa38_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_1 main@%_6_0)))
                (=> main@.critedge5.i_0 a!5)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_1 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_1 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_1))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_1))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!6 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_12_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_1 4))))
      (a!3 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_1 4))))
      (a!4 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4))))
      (a!5 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_1 4)))))
(let ((a!6 (and (main@entry main@%sm8_0 main@%sm9_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm8_0)
                (= main@%sm5_0 main@%sm9_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 9))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 (= main@%loop.bound4_0 9))
                main@%_4_0
                (= main@%_5_0 @arb_int_0)
                (= main@%_7_0 @arb_int_0)
                (= main@%_9_0 (> main@%_6_0 0))
                (= main@%_10_0 (> main@%_8_0 0))
                (= main@%_11_0 (ite main@%_9_0 main@%_10_0 false))
                main@%_11_0
                a!1
                (or (<= @A_left_0 0) (> main@%_12_0 0))
                (= main@%_13_0 (select main@%sm_0 main@%_12_0))
                (= main@%_14_0 (< main@%_13_0 main@%_6_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) (not main@%_14_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.0.i17.lcssa_1 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.010.i16.lcssa_1 main@%.010.i16.lcssa_0))
                (=> main@.lr.ph7_0 a!2)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.lr.ph7_0 a!3)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_1))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!4)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_1 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.critedge5.i_0
                    (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (not main@%or.cond9.i.us73_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%_64_0 main@%_52_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_3))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_1))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%_64_1 main@%_64_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa38_0))
                (=> (and main@.critedge5.i_0
                         main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.lcssa_1 main@%.2.i.lcssa_0))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_1 main@%_6_0)))
                (=> main@.critedge5.i_0 a!5)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_1 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_1 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_1))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!6
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (=> main@_15_0
               (= main@%_16_0 (+ @A_left_0 (* 0 44) (* main@%_24_0 4))))))
(let ((a!4 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                a!3
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> main@.lr.ph87_1 (and main@.lr.ph87_1 main@_15_0))
                (=> (and main@.lr.ph87_1 main@_15_0) main@%or.cond.i_0)
                (=> (and main@.lr.ph87_1 main@_15_0)
                    (= main@%.010.i1686_1 main@%_24_0))
                (=> (and main@.lr.ph87_1 main@_15_0)
                    (= main@%.0.i1785_1 main@%.1.i_2))
                (=> (and main@.lr.ph87_1 main@_15_0)
                    (= main@%.010.i1686_2 main@%.010.i1686_1))
                (=> (and main@.lr.ph87_1 main@_15_0)
                    (= main@%.0.i1785_2 main@%.0.i1785_1))
                main@.lr.ph87_1)))
  (=> a!4
      (main@.lr.ph87 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     @A_left_0
                     main@%loop.bound1_0
                     main@%loop.bound2_0
                     main@%loop.bound3_0
                     main@%.010.i1686_2
                     main@%.0.i1785_2
                     main@%loop.bound4_0)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (= main@%_16_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_24_0 4))))
      (a!4 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_2 4))))
      (a!5 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_2 4)))))
(let ((a!6 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                (=> main@_15_0 a!3)
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| main@.lr.ph87_0)
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| main@_15_0)
                (=> main@.lr.ph7_0
                    (or |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                        |tuple(main@_15_0, main@.lr.ph7_0)|))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| (not main@%_22_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_0 main@%.0.i1785_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_0 main@%.010.i1686_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_1 main@%.1.i_2))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_1 main@%_24_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_1))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_1))
                (=> main@.lr.ph7_0 a!4)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.lr.ph7_0 a!5)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.critedge14.i_0
                    (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0))
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    main@%_38_0)
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    (= main@%.111.i583_0 main@%.010.i16.lcssa_2))
                (=> (and main@.critedge14.i_0 main@.lr.ph7.split.preheader_0)
                    (= main@%.111.i583_1 main@%.111.i583_0))
                main@.critedge14.i_0)))
  (=> a!6
      (main@.critedge14.i
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_2
        main@%loop.bound1_0
        main@%.111.i583_1
        main@%loop.bound3_0)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (= main@%_16_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_24_0 4))))
      (a!4 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_2 4))))
      (a!5 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_2 4)))))
(let ((a!6 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                (=> main@_15_0 a!3)
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| main@.lr.ph87_0)
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| main@_15_0)
                (=> main@.lr.ph7_0
                    (or |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                        |tuple(main@_15_0, main@.lr.ph7_0)|))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| (not main@%_22_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_0 main@%.0.i1785_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_0 main@%.010.i1686_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_1 main@%.1.i_2))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_1 main@%_24_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_1))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_1))
                (=> main@.lr.ph7_0 a!4)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.lr.ph7_0 a!5)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> main@.critedge14.i.us_0
                    (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (not main@%_39_0))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (= main@%.111.i5.us1878_0 main@%.010.i16.lcssa_2))
                (=> (and main@.critedge14.i.us_0 main@.lr.ph19.preheader_0)
                    (= main@%.111.i5.us1878_1 main@%.111.i5.us1878_0))
                main@.critedge14.i.us_0)))
  (=> a!6
      (main@.critedge14.i.us
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_2
        main@%_39_0
        main@%.111.i5.us1878_1
        main@%loop.bound1_0
        main@%loop.bound2_0)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (=> main@.critedge3.i.split.preheader_0
               (= main@%_51_0
                  (+ @A_left_0 (* 0 44) (* main@%.111.i.lcssa47_1 4))))))
(let ((a!4 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0 main@_32_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (not main@%_33_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_0 main@%_24_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_0 main@%.1.i_2))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                a!3
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@.lr.ph71_0
                    (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    main@%.old8.i69_0)
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_0 main@%.0.i.lcssa3346_1))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_1 main@%.2.i70_0))
                main@.lr.ph71_0)))
  (=> a!4
      (main@.lr.ph71 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i70_1
                     main@%loop.bound1_0
                     main@%_51_0
                     main@%.111.i.lcssa47_1)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (= main@%_16_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_24_0 4))))
      (a!4 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_2 4))))
      (a!5 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_2 4))))
      (a!6 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4)))))
(let ((a!7 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                (=> main@_15_0 a!3)
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| main@.lr.ph87_0)
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| main@_15_0)
                (=> main@.lr.ph7_0
                    (or |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                        |tuple(main@_15_0, main@.lr.ph7_0)|))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| (not main@%_22_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_0 main@%.0.i1785_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_0 main@%.010.i1686_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_1 main@%.1.i_2))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_1 main@%_24_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_1))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_1))
                (=> main@.lr.ph7_0 a!4)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.lr.ph7_0 a!5)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!6)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph75_0
                    (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    main@%or.cond9.i.us73_0)
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_0 main@%.0.i17.lcssa_2))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_1 main@%.2.i.us74_0))
                main@.lr.ph75_0)))
  (=> a!7
      (main@.lr.ph75 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i.us74_1
                     main@%_53_0
                     main@%_52_0
                     main@%.111.i.lcssa39_3)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (= main@%_16_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_24_0 4))))
      (a!4 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_2 4))))
      (a!5 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_2 4))))
      (a!6 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!7 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4))))
      (a!8 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!9 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                (=> main@_15_0 a!3)
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| main@.lr.ph87_0)
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| main@_15_0)
                (=> main@.lr.ph7_0
                    (or |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                        |tuple(main@_15_0, main@.lr.ph7_0)|))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| (not main@%_22_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_0 main@%.0.i1785_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_0 main@%.010.i1686_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_1 main@%.1.i_2))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_1 main@%_24_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_1))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_1))
                (=> main@.lr.ph7_0 a!4)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.lr.ph7_0 a!5)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0 main@_32_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (not main@%_33_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_0 main@%_24_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_0 main@%.1.i_2))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!6)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!7)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_3))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_2))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!8)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!9 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_20_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i1785_0 4))))
      (a!2 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_25_0 4))))
      (a!3 (= main@%_16_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_24_0 4))))
      (a!4 (= main@%_34_0
              (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i17.lcssa_2 4))))
      (a!5 (= main@%_36_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.010.i16.lcssa_2 4))))
      (a!6 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!7 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_3 4))))
      (a!8 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!9 (and (main@.lr.ph87 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               @A_left_0
                               main@%loop.bound1_0
                               main@%loop.bound2_0
                               main@%loop.bound3_0
                               main@%.010.i1686_0
                               main@%.0.i1785_0
                               main@%loop.bound4_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_20_0 0))
                (> @A_right_0 0)
                (= main@%_21_0 (select main@%sm5_0 main@%_20_0))
                (= main@%_22_0 (< main@%_21_0 main@%_8_0))
                (=> main@_23_0 (and main@_23_0 main@.lr.ph87_0))
                (=> (and main@_23_0 main@.lr.ph87_0) main@%_22_0)
                (=> main@_23_0 (= main@%_24_0 (+ main@%.010.i1686_0 1)))
                (=> main@_23_0 (= main@%_25_0 (+ main@%.0.i1785_0 1)))
                (=> main@_23_0 (= main@%_26_0 (< main@%.0.i1785_0 9)))
                (=> main@_27_0 (and main@_27_0 main@_23_0))
                (=> (and main@_27_0 main@_23_0) main@%_26_0)
                (=> main@_27_0 a!2)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm5_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_8_0)))
                (=> main@_27_0 (= main@%_31_0 (+ main@%.0.i1785_0 2)))
                (=> main@_27_0
                    (= main@%spec.select.i_0
                       (ite main@%_30_0 main@%_31_0 main@%_25_0)))
                (=> |tuple(main@_23_0, main@_32_0)| main@_23_0)
                (=> main@_32_0
                    (or (and main@_32_0 main@_27_0)
                        |tuple(main@_23_0, main@_32_0)|))
                (=> |tuple(main@_23_0, main@_32_0)| (not main@%_26_0))
                (=> (and main@_32_0 main@_27_0)
                    (= main@%.1.i_0 main@%spec.select.i_0))
                (=> |tuple(main@_23_0, main@_32_0)| (= main@%.1.i_1 10))
                (=> (and main@_32_0 main@_27_0) (= main@%.1.i_2 main@%.1.i_0))
                (=> |tuple(main@_23_0, main@_32_0)|
                    (= main@%.1.i_2 main@%.1.i_1))
                (=> main@_32_0
                    (= main@%_33_0 (< main@%.010.i1686_0 main@%loop.bound4_0)))
                (=> main@_15_0 (and main@_15_0 main@_32_0))
                (=> (and main@_15_0 main@_32_0) main@%_33_0)
                (=> main@_15_0 a!3)
                (=> main@_15_0 (or (<= @A_left_0 0) (> main@%_16_0 0)))
                (=> main@_15_0 (> @A_left_0 0))
                (=> main@_15_0 (= main@%_17_0 (select main@%sm_0 main@%_16_0)))
                (=> main@_15_0 (= main@%_18_0 (< main@%_17_0 main@%_6_0)))
                (=> main@_15_0 (= main@%_19_0 (< main@%.1.i_2 10)))
                (=> main@_15_0
                    (= main@%or.cond.i_0 (ite main@%_18_0 main@%_19_0 false)))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| main@.lr.ph87_0)
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| main@_15_0)
                (=> main@.lr.ph7_0
                    (or |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                        |tuple(main@_15_0, main@.lr.ph7_0)|))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)| (not main@%_22_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_0 main@%.0.i1785_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_0 main@%.010.i1686_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_1 main@%.1.i_2))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_1 main@%_24_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.lr.ph87_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_0))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.0.i17.lcssa_2 main@%.0.i17.lcssa_1))
                (=> |tuple(main@_15_0, main@.lr.ph7_0)|
                    (= main@%.010.i16.lcssa_2 main@%.010.i16.lcssa_1))
                (=> main@.lr.ph7_0 a!4)
                (=> main@.lr.ph7_0 (or (<= @A_right_0 0) (> main@%_34_0 0)))
                (=> main@.lr.ph7_0 (= main@%_35_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.lr.ph7_0 a!5)
                (=> main@.lr.ph7_0 (or (<= @A_left_0 0) (> main@%_36_0 0)))
                (=> main@.lr.ph7_0 (> @A_left_0 0))
                (=> main@.lr.ph7_0
                    (= main@%_37_0 (select main@%sm_0 main@%_36_0)))
                (=> main@.lr.ph7_0 (= main@%_38_0 (< main@%_37_0 main@%_6_0)))
                (=> main@.lr.ph7.split.preheader_0
                    (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.preheader_0 main@.lr.ph7_0)
                    (not main@%_35_0))
                (=> main@.lr.ph7.split.us_0
                    (and main@.lr.ph7.split.us_0 main@.lr.ph7_0))
                (=> (and main@.lr.ph7.split.us_0 main@.lr.ph7_0) main@%_35_0)
                (=> main@.lr.ph19.preheader_0
                    (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0))
                (=> (and main@.lr.ph19.preheader_0 main@.lr.ph7.split.us_0)
                    main@%_38_0)
                (=> main@.lr.ph19.preheader_0 (> @A_right_0 0))
                (=> main@.lr.ph19.preheader_0
                    (= main@%.pre_0 (select main@%sm5_0 main@%_34_0)))
                (=> main@.lr.ph19.preheader_0
                    (= main@%_39_0 (< main@%.pre_0 main@%_8_0)))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0 main@_32_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (not main@%_33_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_0 main@%_24_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_0 main@%.1.i_2))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0 main@_32_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!6)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.us_0)
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph19.preheader_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@.lr.ph7.split.preheader_0)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                        |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    main@%_39_0)
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (not main@%_38_0))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_0 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_1 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_2 main@%.010.i16.lcssa_2))
                (=> |tuple(main@.lr.ph7.split.us_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph19.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.lr.ph7.split.preheader_0, main@.critedge3.i.split.us.preheader_0)|
                    (= main@%.111.i.lcssa39_3 main@%.111.i.lcssa39_2))
                (=> main@.critedge3.i.split.us.preheader_0 a!7)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_2 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_3))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_2))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!8)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!9
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (let ((a!1 (=> main@.lr.ph7.split_0
               (= main@%_46_0 (+ @A_left_0 (* 0 44) (* main@%_49_0 4))))))
(let ((a!2 (and (main@.critedge14.i
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%loop.bound1_0
                  main@%.111.i583_0
                  main@%loop.bound3_0)
                true
                (= main@%_49_0 (+ main@%.111.i583_0 1))
                (= main@%_50_0 (< main@%.111.i583_0 main@%loop.bound3_0))
                (=> main@.lr.ph7.split_0
                    (and main@.lr.ph7.split_0 main@.critedge14.i_0))
                (=> (and main@.lr.ph7.split_0 main@.critedge14.i_0) main@%_50_0)
                a!1
                (=> main@.lr.ph7.split_0
                    (or (<= @A_left_0 0) (> main@%_46_0 0)))
                (=> main@.lr.ph7.split_0 (> @A_left_0 0))
                (=> main@.lr.ph7.split_0
                    (= main@%_47_0 (select main@%sm_0 main@%_46_0)))
                (=> main@.lr.ph7.split_0
                    (= main@%_48_0 (< main@%_47_0 main@%_6_0)))
                (=> main@.critedge14.i_1
                    (and main@.critedge14.i_1 main@.lr.ph7.split_0))
                (=> (and main@.critedge14.i_1 main@.lr.ph7.split_0) main@%_48_0)
                (=> (and main@.critedge14.i_1 main@.lr.ph7.split_0)
                    (= main@%.111.i583_1 main@%_49_0))
                (=> (and main@.critedge14.i_1 main@.lr.ph7.split_0)
                    (= main@%.111.i583_2 main@%.111.i583_1))
                main@.critedge14.i_1)))
  (=> a!2
      (main@.critedge14.i
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_0
        main@%loop.bound1_0
        main@%.111.i583_2
        main@%loop.bound3_0)))))
(rule (let ((a!1 (=> main@.critedge3.i.split.preheader_0
               (= main@%_51_0
                  (+ @A_left_0 (* 0 44) (* main@%.111.i.lcssa47_1 4))))))
(let ((a!2 (and (main@.critedge14.i
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%loop.bound1_0
                  main@%.111.i583_0
                  main@%loop.bound3_0)
                true
                (= main@%_49_0 (+ main@%.111.i583_0 1))
                (= main@%_50_0 (< main@%.111.i583_0 main@%loop.bound3_0))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (not main@%_50_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                a!1
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@.lr.ph71_0
                    (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    main@%.old8.i69_0)
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_0 main@%.0.i.lcssa3346_1))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_1 main@%.2.i70_0))
                main@.lr.ph71_0)))
  (=> a!2
      (main@.lr.ph71 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i70_1
                     main@%loop.bound1_0
                     main@%_51_0
                     main@%.111.i.lcssa47_1)))))
(rule (let ((a!1 (= main@%_46_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_49_0 4))))
      (a!2 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4)))))
(let ((a!3 (and (main@.critedge14.i
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%loop.bound1_0
                  main@%.111.i583_0
                  main@%loop.bound3_0)
                true
                (= main@%_49_0 (+ main@%.111.i583_0 1))
                (= main@%_50_0 (< main@%.111.i583_0 main@%loop.bound3_0))
                (=> main@.lr.ph7.split_0
                    (and main@.lr.ph7.split_0 main@.critedge14.i_0))
                (=> (and main@.lr.ph7.split_0 main@.critedge14.i_0) main@%_50_0)
                (=> main@.lr.ph7.split_0 a!1)
                (=> main@.lr.ph7.split_0
                    (or (<= @A_left_0 0) (> main@%_46_0 0)))
                (=> main@.lr.ph7.split_0 (> @A_left_0 0))
                (=> main@.lr.ph7.split_0
                    (= main@%_47_0 (select main@%sm_0 main@%_46_0)))
                (=> main@.lr.ph7.split_0
                    (= main@%_48_0 (< main@%_47_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (not main@%_48_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!2)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph75_0
                    (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    main@%or.cond9.i.us73_0)
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_0 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_1 main@%.2.i.us74_0))
                main@.lr.ph75_0)))
  (=> a!3
      (main@.lr.ph75 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i.us74_1
                     main@%_53_0
                     main@%_52_0
                     main@%.111.i.lcssa39_1)))))
(rule (let ((a!1 (= main@%_46_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_49_0 4))))
      (a!2 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!3 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4))))
      (a!4 (=> main@.critedge5.i_0
               (= main@%_65_0 (+ @A_right_0 (* 0 44) (* main@%.2.i.lcssa_2 4))))))
(let ((a!5 (and (main@.critedge14.i
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%loop.bound1_0
                  main@%.111.i583_0
                  main@%loop.bound3_0)
                true
                (= main@%_49_0 (+ main@%.111.i583_0 1))
                (= main@%_50_0 (< main@%.111.i583_0 main@%loop.bound3_0))
                (=> main@.lr.ph7.split_0
                    (and main@.lr.ph7.split_0 main@.critedge14.i_0))
                (=> (and main@.lr.ph7.split_0 main@.critedge14.i_0) main@%_50_0)
                (=> main@.lr.ph7.split_0 a!1)
                (=> main@.lr.ph7.split_0
                    (or (<= @A_left_0 0) (> main@%_46_0 0)))
                (=> main@.lr.ph7.split_0 (> @A_left_0 0))
                (=> main@.lr.ph7.split_0
                    (= main@%_47_0 (select main@%sm_0 main@%_46_0)))
                (=> main@.lr.ph7.split_0
                    (= main@%_48_0 (< main@%_47_0 main@%_6_0)))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (not main@%_50_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!2)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (not main@%_48_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!3)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                a!4
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!5 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_46_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_49_0 4))))
      (a!2 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!3 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4))))
      (a!4 (=> main@.critedge5.i_0
               (= main@%_65_0 (+ @A_right_0 (* 0 44) (* main@%.2.i.lcssa_2 4))))))
(let ((a!5 (and (main@.critedge14.i
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%loop.bound1_0
                  main@%.111.i583_0
                  main@%loop.bound3_0)
                true
                (= main@%_49_0 (+ main@%.111.i583_0 1))
                (= main@%_50_0 (< main@%.111.i583_0 main@%loop.bound3_0))
                (=> main@.lr.ph7.split_0
                    (and main@.lr.ph7.split_0 main@.critedge14.i_0))
                (=> (and main@.lr.ph7.split_0 main@.critedge14.i_0) main@%_50_0)
                (=> main@.lr.ph7.split_0 a!1)
                (=> main@.lr.ph7.split_0
                    (or (<= @A_left_0 0) (> main@%_46_0 0)))
                (=> main@.lr.ph7.split_0 (> @A_left_0 0))
                (=> main@.lr.ph7.split_0
                    (= main@%_47_0 (select main@%sm_0 main@%_46_0)))
                (=> main@.lr.ph7.split_0
                    (= main@%_48_0 (< main@%_47_0 main@%_6_0)))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (not main@%_50_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!2)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (not main@%_48_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_0 main@%_49_0))
                (=> (and main@.critedge3.i.split.us.preheader_0
                         main@.lr.ph7.split_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!3)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                a!4
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!5
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (let ((a!1 (=> main@_40_0
               (= main@%_41_0 (+ @A_left_0 (* 0 44) (* main@%_44_0 4))))))
(let ((a!2 (and (main@.critedge14.i.us
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%_39_0
                  main@%.111.i5.us1878_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0)
                true
                (= main@%_44_0 (+ main@%.111.i5.us1878_0 1))
                (= main@%_45_0 (< main@%.111.i5.us1878_0 main@%loop.bound2_0))
                (=> main@_40_0 (and main@_40_0 main@.critedge14.i.us_0))
                (=> (and main@_40_0 main@.critedge14.i.us_0) main@%_45_0)
                a!1
                (=> main@_40_0 (or (<= @A_left_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @A_left_0 0))
                (=> main@_40_0 (= main@%_42_0 (select main@%sm_0 main@%_41_0)))
                (=> main@_40_0 (= main@%_43_0 (>= main@%_42_0 main@%_6_0)))
                (=> main@_40_0
                    (= main@%brmerge_0 (ite main@%_43_0 true main@%_39_0)))
                (=> main@.critedge14.i.us_1
                    (and main@.critedge14.i.us_1 main@_40_0))
                (=> (and main@.critedge14.i.us_1 main@_40_0)
                    (not main@%brmerge_0))
                (=> (and main@.critedge14.i.us_1 main@_40_0)
                    (= main@%.111.i5.us1878_1 main@%_44_0))
                (=> (and main@.critedge14.i.us_1 main@_40_0)
                    (= main@%.111.i5.us1878_2 main@%.111.i5.us1878_1))
                main@.critedge14.i.us_1)))
  (=> a!2
      (main@.critedge14.i.us
        main@%loop.bound_0
        main@%sm_0
        main@%_6_0
        @A_right_0
        main@%sm5_0
        main@%_8_0
        @A_left_0
        main@%.0.i17.lcssa_0
        main@%_39_0
        main@%.111.i5.us1878_2
        main@%loop.bound1_0
        main@%loop.bound2_0)))))
(rule (let ((a!1 (=> main@.critedge3.i.split.preheader_0
               (= main@%_51_0
                  (+ @A_left_0 (* 0 44) (* main@%.111.i.lcssa47_1 4))))))
(let ((a!2 (and (main@.critedge14.i.us
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%_39_0
                  main@%.111.i5.us1878_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0)
                true
                (= main@%_44_0 (+ main@%.111.i5.us1878_0 1))
                (= main@%_45_0 (< main@%.111.i5.us1878_0 main@%loop.bound2_0))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (not main@%_45_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                a!1
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@.lr.ph71_0
                    (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    main@%.old8.i69_0)
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_0 main@%.0.i.lcssa3346_1))
                (=> (and main@.lr.ph71_0 main@.critedge3.i.split.preheader_0)
                    (= main@%.2.i70_1 main@%.2.i70_0))
                main@.lr.ph71_0)))
  (=> a!2
      (main@.lr.ph71 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i70_1
                     main@%loop.bound1_0
                     main@%_51_0
                     main@%.111.i.lcssa47_1)))))
(rule (let ((a!1 (= main@%_41_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_44_0 4))))
      (a!2 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4)))))
(let ((a!3 (and (main@.critedge14.i.us
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%_39_0
                  main@%.111.i5.us1878_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0)
                true
                (= main@%_44_0 (+ main@%.111.i5.us1878_0 1))
                (= main@%_45_0 (< main@%.111.i5.us1878_0 main@%loop.bound2_0))
                (=> main@_40_0 (and main@_40_0 main@.critedge14.i.us_0))
                (=> (and main@_40_0 main@.critedge14.i.us_0) main@%_45_0)
                (=> main@_40_0 a!1)
                (=> main@_40_0 (or (<= @A_left_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @A_left_0 0))
                (=> main@_40_0 (= main@%_42_0 (select main@%sm_0 main@%_41_0)))
                (=> main@_40_0 (= main@%_43_0 (>= main@%_42_0 main@%_6_0)))
                (=> main@_40_0
                    (= main@%brmerge_0 (ite main@%_43_0 true main@%_39_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0 main@_40_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    main@%brmerge_0)
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!2)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> main@.lr.ph75_0
                    (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    main@%or.cond9.i.us73_0)
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_0 main@%.0.i17.lcssa_0))
                (=> (and main@.lr.ph75_0 main@.critedge3.i.split.us.preheader_0)
                    (= main@%.2.i.us74_1 main@%.2.i.us74_0))
                main@.lr.ph75_0)))
  (=> a!3
      (main@.lr.ph75 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i.us74_1
                     main@%_53_0
                     main@%_52_0
                     main@%.111.i.lcssa39_1)))))
(rule (let ((a!1 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!2 (= main@%_41_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_44_0 4))))
      (a!3 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4))))
      (a!4 (=> main@.critedge5.i_0
               (= main@%_65_0 (+ @A_right_0 (* 0 44) (* main@%.2.i.lcssa_2 4))))))
(let ((a!5 (and (main@.critedge14.i.us
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%_39_0
                  main@%.111.i5.us1878_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0)
                true
                (= main@%_44_0 (+ main@%.111.i5.us1878_0 1))
                (= main@%_45_0 (< main@%.111.i5.us1878_0 main@%loop.bound2_0))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (not main@%_45_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!1)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@_40_0 (and main@_40_0 main@.critedge14.i.us_0))
                (=> (and main@_40_0 main@.critedge14.i.us_0) main@%_45_0)
                (=> main@_40_0 a!2)
                (=> main@_40_0 (or (<= @A_left_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @A_left_0 0))
                (=> main@_40_0 (= main@%_42_0 (select main@%sm_0 main@%_41_0)))
                (=> main@_40_0 (= main@%_43_0 (>= main@%_42_0 main@%_6_0)))
                (=> main@_40_0
                    (= main@%brmerge_0 (ite main@%_43_0 true main@%_39_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0 main@_40_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    main@%brmerge_0)
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!3)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                a!4
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!5 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_51_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa47_1 4))))
      (a!2 (= main@%_41_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_44_0 4))))
      (a!3 (= main@%_52_0
              (+ (+ @A_left_0 (* 0 44)) (* main@%.111.i.lcssa39_1 4))))
      (a!4 (=> main@.critedge5.i_0
               (= main@%_65_0 (+ @A_right_0 (* 0 44) (* main@%.2.i.lcssa_2 4))))))
(let ((a!5 (and (main@.critedge14.i.us
                  main@%loop.bound_0
                  main@%sm_0
                  main@%_6_0
                  @A_right_0
                  main@%sm5_0
                  main@%_8_0
                  @A_left_0
                  main@%.0.i17.lcssa_0
                  main@%_39_0
                  main@%.111.i5.us1878_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0)
                true
                (= main@%_44_0 (+ main@%.111.i5.us1878_0 1))
                (= main@%_45_0 (< main@%.111.i5.us1878_0 main@%loop.bound2_0))
                (=> main@.critedge3.i.split.preheader_0
                    (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (not main@%_45_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_0 main@%.0.i17.lcssa_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.111.i.lcssa47_1 main@%.111.i.lcssa47_0))
                (=> (and main@.critedge3.i.split.preheader_0
                         main@.critedge14.i.us_0)
                    (= main@%.0.i.lcssa3346_1 main@%.0.i.lcssa3346_0))
                (=> main@.critedge3.i.split.preheader_0 a!1)
                (=> main@.critedge3.i.split.preheader_0
                    (or (<= @A_left_0 0) (> main@%_51_0 0)))
                (=> main@.critedge3.i.split.preheader_0
                    (= main@%.old8.i69_0 (< main@%.0.i.lcssa3346_1 10)))
                (=> main@_40_0 (and main@_40_0 main@.critedge14.i.us_0))
                (=> (and main@_40_0 main@.critedge14.i.us_0) main@%_45_0)
                (=> main@_40_0 a!2)
                (=> main@_40_0 (or (<= @A_left_0 0) (> main@%_41_0 0)))
                (=> main@_40_0 (> @A_left_0 0))
                (=> main@_40_0 (= main@%_42_0 (select main@%sm_0 main@%_41_0)))
                (=> main@_40_0 (= main@%_43_0 (>= main@%_42_0 main@%_6_0)))
                (=> main@_40_0
                    (= main@%brmerge_0 (ite main@%_43_0 true main@%_39_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (and main@.critedge3.i.split.us.preheader_0 main@_40_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    main@%brmerge_0)
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_0 main@%_44_0))
                (=> (and main@.critedge3.i.split.us.preheader_0 main@_40_0)
                    (= main@%.111.i.lcssa39_1 main@%.111.i.lcssa39_0))
                (=> main@.critedge3.i.split.us.preheader_0 a!3)
                (=> main@.critedge3.i.split.us.preheader_0
                    (or (<= @A_left_0 0) (> main@%_52_0 0)))
                (=> main@.critedge3.i.split.us.preheader_0 (> @A_left_0 0))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%.pre28_0 (select main@%sm_0 main@%_52_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_53_0 (>= main@%.pre28_0 main@%_6_0)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%_54_0 (< main@%.0.i17.lcssa_0 10)))
                (=> main@.critedge3.i.split.us.preheader_0
                    (= main@%or.cond9.i.us73_0
                       (ite main@%_53_0 main@%_54_0 false)))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us.preheader_0)
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.preheader_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us73_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (not main@%.old8.i69_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.0.i17.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.0.i.lcssa3346_1))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split.us.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.preheader_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                a!4
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!5
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (let ((a!1 (and (main@.lr.ph71 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i70_0
                               main@%loop.bound1_0
                               main@%_51_0
                               main@%.111.i.lcssa47_0)
                true
                (= main@%_60_0 (+ @A_right_0 (* 0 44) (* main@%.2.i70_0 4)))
                (or (<= @A_right_0 0) (> main@%_60_0 0))
                (> @A_right_0 0)
                (= main@%_61_0 (select main@%sm5_0 main@%_60_0))
                (= main@%_62_0 (< main@%_61_0 main@%_8_0))
                (=> main@.critedge3.i.split_0
                    (and main@.critedge3.i.split_0 main@.lr.ph71_0))
                (=> (and main@.critedge3.i.split_0 main@.lr.ph71_0) main@%_62_0)
                (=> main@.critedge3.i.split_0
                    (= main@%_63_0 (+ main@%.2.i70_0 1)))
                (=> main@.critedge3.i.split_0
                    (= main@%.old8.i_0 (< main@%.2.i70_0 main@%loop.bound1_0)))
                (=> main@.lr.ph71_1
                    (and main@.lr.ph71_1 main@.critedge3.i.split_0))
                (=> (and main@.lr.ph71_1 main@.critedge3.i.split_0)
                    main@%.old8.i_0)
                (=> (and main@.lr.ph71_1 main@.critedge3.i.split_0)
                    (= main@%.2.i70_1 main@%_63_0))
                (=> (and main@.lr.ph71_1 main@.critedge3.i.split_0)
                    (= main@%.2.i70_2 main@%.2.i70_1))
                main@.lr.ph71_1)))
  (=> a!1
      (main@.lr.ph71 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i70_2
                     main@%loop.bound1_0
                     main@%_51_0
                     main@%.111.i.lcssa47_0))))
(rule (let ((a!1 (= main@%_60_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i70_0 4))))
      (a!2 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph71 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i70_0
                               main@%loop.bound1_0
                               main@%_51_0
                               main@%.111.i.lcssa47_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_60_0 0))
                (> @A_right_0 0)
                (= main@%_61_0 (select main@%sm5_0 main@%_60_0))
                (= main@%_62_0 (< main@%_61_0 main@%_8_0))
                (=> main@.critedge3.i.split_0
                    (and main@.critedge3.i.split_0 main@.lr.ph71_0))
                (=> (and main@.critedge3.i.split_0 main@.lr.ph71_0) main@%_62_0)
                (=> main@.critedge3.i.split_0
                    (= main@%_63_0 (+ main@%.2.i70_0 1)))
                (=> main@.critedge3.i.split_0
                    (= main@%.old8.i_0 (< main@%.2.i70_0 main@%loop.bound1_0)))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split_0)
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    main@.lr.ph71_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                        |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (not main@%.old8.i_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (not main@%_62_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa47_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%_63_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.2.i70_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!2)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!3 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_60_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i70_0 4))))
      (a!2 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph71 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i70_0
                               main@%loop.bound1_0
                               main@%_51_0
                               main@%.111.i.lcssa47_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_60_0 0))
                (> @A_right_0 0)
                (= main@%_61_0 (select main@%sm5_0 main@%_60_0))
                (= main@%_62_0 (< main@%_61_0 main@%_8_0))
                (=> main@.critedge3.i.split_0
                    (and main@.critedge3.i.split_0 main@.lr.ph71_0))
                (=> (and main@.critedge3.i.split_0 main@.lr.ph71_0) main@%_62_0)
                (=> main@.critedge3.i.split_0
                    (= main@%_63_0 (+ main@%.2.i70_0 1)))
                (=> main@.critedge3.i.split_0
                    (= main@%.old8.i_0 (< main@%.2.i70_0 main@%loop.bound1_0)))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split_0)
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    main@.lr.ph71_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                        |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (not main@%.old8.i_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (not main@%_62_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_51_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa47_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%_63_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_51_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa47_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%.2.i70_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.critedge3.i.split_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.lr.ph71_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!2)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!3
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (let ((a!1 (and (main@.lr.ph75 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i.us74_0
                               main@%_53_0
                               main@%_52_0
                               main@%.111.i.lcssa39_0)
                true
                (= main@%_55_0 (+ @A_right_0 (* 0 44) (* main@%.2.i.us74_0 4)))
                (or (<= @A_right_0 0) (> main@%_55_0 0))
                (> @A_right_0 0)
                (= main@%_56_0 (select main@%sm5_0 main@%_55_0))
                (= main@%_57_0 (< main@%_56_0 main@%_8_0))
                (=> main@.critedge3.i.split.us_0
                    (and main@.critedge3.i.split.us_0 main@.lr.ph75_0))
                (=> (and main@.critedge3.i.split.us_0 main@.lr.ph75_0)
                    main@%_57_0)
                (=> main@.critedge3.i.split.us_0
                    (= main@%_58_0 (+ main@%.2.i.us74_0 1)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%_59_0 (< main@%.2.i.us74_0 9)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%or.cond9.i.us_0
                       (ite main@%_53_0 main@%_59_0 false)))
                (=> main@.lr.ph75_1
                    (and main@.lr.ph75_1 main@.critedge3.i.split.us_0))
                (=> (and main@.lr.ph75_1 main@.critedge3.i.split.us_0)
                    main@%or.cond9.i.us_0)
                (=> (and main@.lr.ph75_1 main@.critedge3.i.split.us_0)
                    (= main@%.2.i.us74_1 main@%_58_0))
                (=> (and main@.lr.ph75_1 main@.critedge3.i.split.us_0)
                    (= main@%.2.i.us74_2 main@%.2.i.us74_1))
                main@.lr.ph75_1)))
  (=> a!1
      (main@.lr.ph75 main@%loop.bound_0
                     main@%sm_0
                     main@%_6_0
                     @A_right_0
                     main@%sm5_0
                     main@%_8_0
                     main@%.2.i.us74_2
                     main@%_53_0
                     main@%_52_0
                     main@%.111.i.lcssa39_0))))
(rule (let ((a!1 (= main@%_55_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.us74_0 4))))
      (a!2 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph75 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i.us74_0
                               main@%_53_0
                               main@%_52_0
                               main@%.111.i.lcssa39_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_55_0 0))
                (> @A_right_0 0)
                (= main@%_56_0 (select main@%sm5_0 main@%_55_0))
                (= main@%_57_0 (< main@%_56_0 main@%_8_0))
                (=> main@.critedge3.i.split.us_0
                    (and main@.critedge3.i.split.us_0 main@.lr.ph75_0))
                (=> (and main@.critedge3.i.split.us_0 main@.lr.ph75_0)
                    main@%_57_0)
                (=> main@.critedge3.i.split.us_0
                    (= main@%_58_0 (+ main@%.2.i.us74_0 1)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%_59_0 (< main@%.2.i.us74_0 9)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%or.cond9.i.us_0
                       (ite main@%_53_0 main@%_59_0 false)))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    main@.lr.ph75_0)
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (not main@%_57_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.2.i.us74_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%_58_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!2)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.critedge5.i_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0) main@%_68_0)
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_0 main@%.2.i.lcssa_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_0 main@%.111.i.lcssa38_2))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.3.i3_1 main@%.3.i3_0))
                (=> (and main@.lr.ph_0 main@.critedge5.i_0)
                    (= main@%.212.i2_1 main@%.212.i2_0))
                main@.lr.ph_0)))
  (=> a!3 (main@.lr.ph main@%loop.bound_0 main@%.212.i2_1 main@%.3.i3_1)))))
(rule (let ((a!1 (= main@%_55_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.us74_0 4))))
      (a!2 (= main@%_65_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.2.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph75 main@%loop.bound_0
                               main@%sm_0
                               main@%_6_0
                               @A_right_0
                               main@%sm5_0
                               main@%_8_0
                               main@%.2.i.us74_0
                               main@%_53_0
                               main@%_52_0
                               main@%.111.i.lcssa39_0)
                true
                a!1
                (or (<= @A_right_0 0) (> main@%_55_0 0))
                (> @A_right_0 0)
                (= main@%_56_0 (select main@%sm5_0 main@%_55_0))
                (= main@%_57_0 (< main@%_56_0 main@%_8_0))
                (=> main@.critedge3.i.split.us_0
                    (and main@.critedge3.i.split.us_0 main@.lr.ph75_0))
                (=> (and main@.critedge3.i.split.us_0 main@.lr.ph75_0)
                    main@%_57_0)
                (=> main@.critedge3.i.split.us_0
                    (= main@%_58_0 (+ main@%.2.i.us74_0 1)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%_59_0 (< main@%.2.i.us74_0 9)))
                (=> main@.critedge3.i.split.us_0
                    (= main@%or.cond9.i.us_0
                       (ite main@%_53_0 main@%_59_0 false)))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    main@.lr.ph75_0)
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    main@.critedge3.i.split.us_0)
                (=> main@.critedge5.i_0
                    (or |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                        |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (not main@%_57_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (not main@%or.cond9.i.us_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%_64_0 main@%_52_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_0 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_0 main@%.2.i.us74_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%_64_1 main@%_52_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_1 main@%.111.i.lcssa39_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_1 main@%_58_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_0))
                (=> |tuple(main@.lr.ph75_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_0))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%_64_2 main@%_64_1))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.111.i.lcssa38_2 main@%.111.i.lcssa38_1))
                (=> |tuple(main@.critedge3.i.split.us_0, main@.critedge5.i_0)|
                    (= main@%.2.i.lcssa_2 main@%.2.i.lcssa_1))
                (=> main@.critedge5.i_0
                    (= main@%sm6_0 (store main@%sm_0 main@%_64_2 main@%_6_0)))
                (=> main@.critedge5.i_0 a!2)
                (=> main@.critedge5.i_0
                    (or (<= @A_right_0 0) (> main@%_65_0 0)))
                (=> main@.critedge5.i_0 (> @A_right_0 0))
                (=> main@.critedge5.i_0
                    (= main@%sm7_0 (store main@%sm5_0 main@%_65_0 main@%_8_0)))
                (=> main@.critedge5.i_0
                    (= main@%_66_0 (< main@%.111.i.lcssa38_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_67_0 (< main@%.2.i.lcssa_2 11)))
                (=> main@.critedge5.i_0
                    (= main@%_68_0 (ite main@%_66_0 main@%_67_0 false)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.critedge5.i_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (not main@%_68_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_0 main@%.111.i.lcssa38_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_0 main@%.2.i.lcssa_2))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.critedge5.i_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!3
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0)))))
(rule (=> (and (main@.lr.ph main@%loop.bound_0 main@%.212.i2_0 main@%.3.i3_0)
         true
         (= main@%_70_0 (+ main@%.212.i2_0 1))
         (= main@%_71_0 (< main@%.3.i3_0 10))
         (= main@%spec.select15.v.i_0 (ite main@%_71_0 2 1))
         (= main@%spec.select15.i_0 (+ main@%spec.select15.v.i_0 main@%.3.i3_0))
         (= main@%_72_0 (< main@%.212.i2_0 10))
         (= main@%_73_0 (< main@%spec.select15.i_0 11))
         (= main@%_74_0 (ite main@%_72_0 main@%_73_0 false))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_74_0)
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.3.i3_1 main@%spec.select15.i_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.212.i2_1 main@%_70_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.3.i3_2 main@%.3.i3_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.212.i2_2 main@%.212.i2_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%loop.bound_0 main@%.212.i2_2 main@%.3.i3_2)))
(rule (let ((a!1 (and (main@.lr.ph main@%loop.bound_0 main@%.212.i2_0 main@%.3.i3_0)
                true
                (= main@%_70_0 (+ main@%.212.i2_0 1))
                (= main@%_71_0 (< main@%.3.i3_0 10))
                (= main@%spec.select15.v.i_0 (ite main@%_71_0 2 1))
                (= main@%spec.select15.i_0
                   (+ main@%spec.select15.v.i_0 main@%.3.i3_0))
                (= main@%_72_0 (< main@%.212.i2_0 10))
                (= main@%_73_0 (< main@%spec.select15.i_0 11))
                (= main@%_74_0 (ite main@%_72_0 main@%_73_0 false))
                (=> main@.preheader1_0 (and main@.preheader1_0 main@.lr.ph_0))
                (=> (and main@.preheader1_0 main@.lr.ph_0) (not main@%_74_0))
                (=> (and main@.preheader1_0 main@.lr.ph_0)
                    (= main@%.212.i.lcssa_0 main@%_70_0))
                (=> (and main@.preheader1_0 main@.lr.ph_0)
                    (= main@%.3.i.lcssa_0 main@%spec.select15.i_0))
                (=> (and main@.preheader1_0 main@.lr.ph_0)
                    (= main@%.212.i.lcssa_1 main@%.212.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.lr.ph_0)
                    (= main@%.3.i.lcssa_1 main@%.3.i.lcssa_0))
                (=> main@.preheader1_0
                    (= main@%_69_0 (> main@%.3.i.lcssa_1 10)))
                (=> main@_75_0 (and main@_75_0 main@.preheader1_0))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_0 main@%.212.i.lcssa_1))
                (=> (and main@_75_0 main@.preheader1_0)
                    (= main@%.313.i_1 main@%.313.i_0))
                main@_75_0)))
  (=> a!1
      (main@_75 main@%.313.i_1
                main@%loop.bound_0
                main@%.3.i.lcssa_1
                main@%_69_0))))
(rule (=> (and (main@_75 main@%.313.i_0
                   main@%loop.bound_0
                   main@%.3.i.lcssa_0
                   main@%_69_0)
         true
         (= main@%_76_0 (< main@%.313.i_0 11))
         (= main@%_77_0 (ite main@%_76_0 main@%_69_0 false))
         (= main@%_78_0 (+ main@%.313.i_0 1))
         (=> main@_75_1 (and main@_75_1 main@_75_0))
         (=> (and main@_75_1 main@_75_0) main@%_77_0)
         (=> (and main@_75_1 main@_75_0) (= main@%.313.i_1 main@%_78_0))
         (=> (and main@_75_1 main@_75_0) (= main@%.313.i_2 main@%.313.i_1))
         main@_75_1)
    (main@_75 main@%.313.i_2 main@%loop.bound_0 main@%.3.i.lcssa_0 main@%_69_0)))
(rule (let ((a!1 (and (main@_75 main@%.313.i_0
                          main@%loop.bound_0
                          main@%.3.i.lcssa_0
                          main@%_69_0)
                true
                (= main@%_76_0 (< main@%.313.i_0 11))
                (= main@%_77_0 (ite main@%_76_0 main@%_69_0 false))
                (= main@%_78_0 (+ main@%.313.i_0 1))
                (=> main@.preheader_0 (and main@.preheader_0 main@_75_0))
                (=> (and main@.preheader_0 main@_75_0) (not main@%_77_0))
                (=> main@.preheader_0 (= main@%_79_0 (> main@%.313.i_0 10)))
                (=> main@.preheader.split.us_0
                    (and main@.preheader.split.us_0 main@.preheader_0))
                (=> (and main@.preheader.split.us_0 main@.preheader_0)
                    main@%_79_0)
                (=> (and main@.preheader.split.us_0 main@.preheader_0)
                    (= main@%.5.i.us_0 main@%.3.i.lcssa_0))
                (=> (and main@.preheader.split.us_0 main@.preheader_0)
                    (= main@%.5.i.us_1 main@%.5.i.us_0))
                main@.preheader.split.us_0)))
  (=> a!1
      (main@.preheader.split.us
        main@%.313.i_0
        main@%.5.i.us_1
        main@%loop.bound_0))))
(rule (let ((a!1 (and (main@_75 main@%.313.i_0
                          main@%loop.bound_0
                          main@%.3.i.lcssa_0
                          main@%_69_0)
                true
                (= main@%_76_0 (< main@%.313.i_0 11))
                (= main@%_77_0 (ite main@%_76_0 main@%_69_0 false))
                (= main@%_78_0 (+ main@%.313.i_0 1))
                (=> main@.preheader_0 (and main@.preheader_0 main@_75_0))
                (=> (and main@.preheader_0 main@_75_0) (not main@%_77_0))
                (=> main@.preheader_0 (= main@%_79_0 (> main@%.313.i_0 10)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_79_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.5.i.lcssa_0 main@%.3.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_82_0 (= main@%.313.i_0 main@%.5.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_82_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.preheader.split.us
           main@%.313.i_0
           main@%.5.i.us_0
           main@%loop.bound_0)
         true
         (= main@%_80_0 (< main@%.5.i.us_0 main@%loop.bound_0))
         (= main@%_81_0 (+ main@%.5.i.us_0 1))
         (=> main@.preheader.split.us_1
             (and main@.preheader.split.us_1 main@.preheader.split.us_0))
         (=> (and main@.preheader.split.us_1 main@.preheader.split.us_0)
             main@%_80_0)
         (=> (and main@.preheader.split.us_1 main@.preheader.split.us_0)
             (= main@%.5.i.us_1 main@%_81_0))
         (=> (and main@.preheader.split.us_1 main@.preheader.split.us_0)
             (= main@%.5.i.us_2 main@%.5.i.us_1))
         main@.preheader.split.us_1)
    (main@.preheader.split.us main@%.313.i_0 main@%.5.i.us_2 main@%loop.bound_0)))
(rule (let ((a!1 (and (main@.preheader.split.us
                  main@%.313.i_0
                  main@%.5.i.us_0
                  main@%loop.bound_0)
                true
                (= main@%_80_0 (< main@%.5.i.us_0 main@%loop.bound_0))
                (= main@%_81_0 (+ main@%.5.i.us_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader.split.us_0))
                (=> (and main@verifier.error_0 main@.preheader.split.us_0)
                    (not main@%_80_0))
                (=> (and main@verifier.error_0 main@.preheader.split.us_0)
                    (= main@%.5.i.lcssa_0 main@%.5.i.us_0))
                (=> (and main@verifier.error_0 main@.preheader.split.us_0)
                    (= main@%.5.i.lcssa_1 main@%.5.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_82_0 (= main@%.313.i_0 main@%.5.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_82_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

