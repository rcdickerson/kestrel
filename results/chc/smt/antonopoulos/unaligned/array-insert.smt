(set-info :original "./results/chc/bytecode/antonopoulos/unaligned/array-insert.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) Int ))
(declare-rel main@.lr.ph7 (Int Int (Array Int Int) Int Int Int Int (Array Int Int) Int Int Int ))
(declare-rel main@_21 (Int Int Int (Array Int Int) Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int (Array Int Int) Int Int Int ))
(declare-rel main@_34 (Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_37_0 Bool )
(declare-var main@%_35_0 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_32_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%.0.i13_2 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%.02.i26_2 Int )
(declare-var main@entry_0 Bool )
(declare-var @A_left_0 Int )
(declare-var @A_right_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@.lr.ph7_0 Bool )
(declare-var main@%.02.i26_0 Int )
(declare-var main@%.02.i26_1 Int )
(declare-var main@.critedge.i_0 Bool )
(declare-var main@%.02.i.lcssa_0 Int )
(declare-var main@%.02.i.lcssa_1 Int )
(declare-var main@_21_0 Bool )
(declare-var main@%.13.i_0 Int )
(declare-var main@%.13.i_1 Int )
(declare-var main@%_18_0 Int )
(declare-var main@_14_0 Bool )
(declare-var main@.lr.ph7_1 Bool )
(declare-var |tuple(main@.lr.ph7_0, main@.critedge.i_0)| Bool )
(declare-var |tuple(main@_14_0, main@.critedge.i_0)| Bool )
(declare-var main@%.02.i.lcssa_2 Int )
(declare-var main@%_23_0 Int )
(declare-var main@_21_1 Bool )
(declare-var main@%.13.i_2 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0.i13_0 Int )
(declare-var main@%.0.i13_1 Int )
(declare-var main@.critedge1.i_0 Bool )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@_34_0 Bool )
(declare-var main@%.1.i_0 Int )
(declare-var main@%.1.i_1 Int )
(declare-var main@%_31_0 Int )
(declare-var main@_27_0 Bool )
(declare-var main@.lr.ph_1 Bool )
(declare-var |tuple(main@.lr.ph_0, main@.critedge1.i_0)| Bool )
(declare-var |tuple(main@_27_0, main@.critedge1.i_0)| Bool )
(declare-var main@%.0.i.lcssa_2 Int )
(declare-var main@%_36_0 Int )
(declare-var main@_34_1 Bool )
(declare-var main@%.1.i_2 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm7_0 main@%sm8_0 @arb_int_0))
(rule (let ((a!1 (and (main@entry main@%sm7_0 main@%sm8_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm7_0)
                (= main@%sm4_0 main@%sm8_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 11))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (> main@%_5_0 0))
                (= main@%_9_0 (> main@%_7_0 0))
                (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
                main@%_10_0
                (= main@%_11_0 (+ @A_left_0 (* 0 44) (* 0 4)))
                (or (<= @A_left_0 0) (> main@%_11_0 0))
                (= main@%_12_0 (select main@%sm_0 main@%_11_0))
                (= main@%_13_0 (< main@%_12_0 main@%_5_0))
                (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
                (=> (and main@.lr.ph7_0 main@entry_0) main@%_13_0)
                (=> (and main@.lr.ph7_0 main@entry_0) (= main@%.02.i26_0 0))
                (=> (and main@.lr.ph7_0 main@entry_0)
                    (= main@%.02.i26_1 main@%.02.i26_0))
                main@.lr.ph7_0)))
  (=> a!1
      (main@.lr.ph7 main@%loop.bound_0
                    @A_right_0
                    main@%sm4_0
                    main@%_7_0
                    main@%loop.bound1_0
                    main@%loop.bound2_0
                    @A_left_0
                    main@%sm_0
                    main@%_5_0
                    main@%.02.i26_1
                    main@%loop.bound3_0))))
(rule (let ((a!1 (= main@%_11_0 (+ (+ @A_left_0 (* 0 44)) (* 0 4))))
      (a!2 (= main@%_20_0 (+ (+ @A_left_0 (* 0 44)) (* main@%.02.i.lcssa_1 4)))))
(let ((a!3 (and (main@entry main@%sm7_0 main@%sm8_0 @arb_int_0)
                true
                (= main@%sm_0 main@%sm7_0)
                (= main@%sm4_0 main@%sm8_0)
                (= main@%_0_0 (= main@%loop.bound_0 11))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 9))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 11))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 9))
                main@%_3_0
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (> main@%_5_0 0))
                (= main@%_9_0 (> main@%_7_0 0))
                (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
                main@%_10_0
                a!1
                (or (<= @A_left_0 0) (> main@%_11_0 0))
                (= main@%_12_0 (select main@%sm_0 main@%_11_0))
                (= main@%_13_0 (< main@%_12_0 main@%_5_0))
                (=> main@.critedge.i_0 (and main@.critedge.i_0 main@entry_0))
                (=> (and main@.critedge.i_0 main@entry_0) (not main@%_13_0))
                (=> (and main@.critedge.i_0 main@entry_0)
                    (= main@%.02.i.lcssa_0 0))
                (=> (and main@.critedge.i_0 main@entry_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@.critedge.i_0 a!2)
                (=> main@.critedge.i_0 (or (<= @A_left_0 0) (> main@%_20_0 0)))
                (=> main@.critedge.i_0 (> @A_left_0 0))
                (=> main@.critedge.i_0
                    (= main@%sm5_0 (store main@%sm_0 main@%_20_0 main@%_5_0)))
                (=> main@_21_0 (and main@_21_0 main@.critedge.i_0))
                (=> (and main@_21_0 main@.critedge.i_0)
                    (= main@%.13.i_0 main@%.02.i.lcssa_1))
                (=> (and main@_21_0 main@.critedge.i_0)
                    (= main@%.13.i_1 main@%.13.i_0))
                main@_21_0)))
  (=> a!3
      (main@_21 main@%.13.i_1
                main@%loop.bound_0
                @A_right_0
                main@%sm4_0
                main@%_7_0
                main@%loop.bound1_0
                main@%loop.bound2_0)))))
(rule (let ((a!1 (=> main@_14_0
               (= main@%_15_0 (+ @A_left_0 (* 0 44) (* main@%_18_0 4))))))
(let ((a!2 (and (main@.lr.ph7 main@%loop.bound_0
                              @A_right_0
                              main@%sm4_0
                              main@%_7_0
                              main@%loop.bound1_0
                              main@%loop.bound2_0
                              @A_left_0
                              main@%sm_0
                              main@%_5_0
                              main@%.02.i26_0
                              main@%loop.bound3_0)
                true
                (= main@%_18_0 (+ main@%.02.i26_0 1))
                (= main@%_19_0 (< main@%.02.i26_0 main@%loop.bound3_0))
                (=> main@_14_0 (and main@_14_0 main@.lr.ph7_0))
                (=> (and main@_14_0 main@.lr.ph7_0) main@%_19_0)
                a!1
                (=> main@_14_0 (or (<= @A_left_0 0) (> main@%_15_0 0)))
                (=> main@_14_0 (> @A_left_0 0))
                (=> main@_14_0 (= main@%_16_0 (select main@%sm_0 main@%_15_0)))
                (=> main@_14_0 (= main@%_17_0 (< main@%_16_0 main@%_5_0)))
                (=> main@.lr.ph7_1 (and main@.lr.ph7_1 main@_14_0))
                (=> (and main@.lr.ph7_1 main@_14_0) main@%_17_0)
                (=> (and main@.lr.ph7_1 main@_14_0)
                    (= main@%.02.i26_1 main@%_18_0))
                (=> (and main@.lr.ph7_1 main@_14_0)
                    (= main@%.02.i26_2 main@%.02.i26_1))
                main@.lr.ph7_1)))
  (=> a!2
      (main@.lr.ph7 main@%loop.bound_0
                    @A_right_0
                    main@%sm4_0
                    main@%_7_0
                    main@%loop.bound1_0
                    main@%loop.bound2_0
                    @A_left_0
                    main@%sm_0
                    main@%_5_0
                    main@%.02.i26_2
                    main@%loop.bound3_0)))))
(rule (let ((a!1 (= main@%_15_0 (+ (+ @A_left_0 (* 0 44)) (* main@%_18_0 4))))
      (a!2 (= main@%_20_0 (+ (+ @A_left_0 (* 0 44)) (* main@%.02.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph7 main@%loop.bound_0
                              @A_right_0
                              main@%sm4_0
                              main@%_7_0
                              main@%loop.bound1_0
                              main@%loop.bound2_0
                              @A_left_0
                              main@%sm_0
                              main@%_5_0
                              main@%.02.i26_0
                              main@%loop.bound3_0)
                true
                (= main@%_18_0 (+ main@%.02.i26_0 1))
                (= main@%_19_0 (< main@%.02.i26_0 main@%loop.bound3_0))
                (=> main@_14_0 (and main@_14_0 main@.lr.ph7_0))
                (=> (and main@_14_0 main@.lr.ph7_0) main@%_19_0)
                (=> main@_14_0 a!1)
                (=> main@_14_0 (or (<= @A_left_0 0) (> main@%_15_0 0)))
                (=> main@_14_0 (> @A_left_0 0))
                (=> main@_14_0 (= main@%_16_0 (select main@%sm_0 main@%_15_0)))
                (=> main@_14_0 (= main@%_17_0 (< main@%_16_0 main@%_5_0)))
                (=> |tuple(main@.lr.ph7_0, main@.critedge.i_0)| main@.lr.ph7_0)
                (=> |tuple(main@_14_0, main@.critedge.i_0)| main@_14_0)
                (=> main@.critedge.i_0
                    (or |tuple(main@.lr.ph7_0, main@.critedge.i_0)|
                        |tuple(main@_14_0, main@.critedge.i_0)|))
                (=> |tuple(main@.lr.ph7_0, main@.critedge.i_0)|
                    (not main@%_19_0))
                (=> |tuple(main@_14_0, main@.critedge.i_0)| (not main@%_17_0))
                (=> |tuple(main@.lr.ph7_0, main@.critedge.i_0)|
                    (= main@%.02.i.lcssa_0 main@%_18_0))
                (=> |tuple(main@_14_0, main@.critedge.i_0)|
                    (= main@%.02.i.lcssa_1 main@%_18_0))
                (=> |tuple(main@.lr.ph7_0, main@.critedge.i_0)|
                    (= main@%.02.i.lcssa_2 main@%.02.i.lcssa_0))
                (=> |tuple(main@_14_0, main@.critedge.i_0)|
                    (= main@%.02.i.lcssa_2 main@%.02.i.lcssa_1))
                (=> main@.critedge.i_0 a!2)
                (=> main@.critedge.i_0 (or (<= @A_left_0 0) (> main@%_20_0 0)))
                (=> main@.critedge.i_0 (> @A_left_0 0))
                (=> main@.critedge.i_0
                    (= main@%sm5_0 (store main@%sm_0 main@%_20_0 main@%_5_0)))
                (=> main@_21_0 (and main@_21_0 main@.critedge.i_0))
                (=> (and main@_21_0 main@.critedge.i_0)
                    (= main@%.13.i_0 main@%.02.i.lcssa_2))
                (=> (and main@_21_0 main@.critedge.i_0)
                    (= main@%.13.i_1 main@%.13.i_0))
                main@_21_0)))
  (=> a!3
      (main@_21 main@%.13.i_1
                main@%loop.bound_0
                @A_right_0
                main@%sm4_0
                main@%_7_0
                main@%loop.bound1_0
                main@%loop.bound2_0)))))
(rule (=> (and (main@_21 main@%.13.i_0
                   main@%loop.bound_0
                   @A_right_0
                   main@%sm4_0
                   main@%_7_0
                   main@%loop.bound1_0
                   main@%loop.bound2_0)
         true
         (= main@%_22_0 (< main@%.13.i_0 main@%loop.bound2_0))
         (= main@%_23_0 (+ main@%.13.i_0 1))
         (=> main@_21_1 (and main@_21_1 main@_21_0))
         (=> (and main@_21_1 main@_21_0) main@%_22_0)
         (=> (and main@_21_1 main@_21_0) (= main@%.13.i_1 main@%_23_0))
         (=> (and main@_21_1 main@_21_0) (= main@%.13.i_2 main@%.13.i_1))
         main@_21_1)
    (main@_21 main@%.13.i_2
              main@%loop.bound_0
              @A_right_0
              main@%sm4_0
              main@%_7_0
              main@%loop.bound1_0
              main@%loop.bound2_0)))
(rule (let ((a!1 (=> main@.preheader_0
               (= main@%_24_0 (+ @A_right_0 (* 0 44) (* 0 4))))))
(let ((a!2 (and (main@_21 main@%.13.i_0
                          main@%loop.bound_0
                          @A_right_0
                          main@%sm4_0
                          main@%_7_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.13.i_0 main@%loop.bound2_0))
                (= main@%_23_0 (+ main@%.13.i_0 1))
                (=> main@.preheader_0 (and main@.preheader_0 main@_21_0))
                (=> (and main@.preheader_0 main@_21_0) (not main@%_22_0))
                a!1
                (=> main@.preheader_0 (or (<= @A_right_0 0) (> main@%_24_0 0)))
                (=> main@.preheader_0
                    (= main@%_25_0 (select main@%sm4_0 main@%_24_0)))
                (=> main@.preheader_0
                    (= main@%_26_0 (< main@%_25_0 main@%_7_0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_26_0)
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.0.i13_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i13_1 main@%.0.i13_0))
                main@.lr.ph_0)))
  (=> a!2
      (main@.lr.ph main@%.13.i_0
                   main@%loop.bound_0
                   @A_right_0
                   main@%sm4_0
                   main@%_7_0
                   main@%.0.i13_1
                   main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_24_0 (+ (+ @A_right_0 (* 0 44)) (* 0 4))))
      (a!2 (= main@%_33_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i.lcssa_1 4)))))
(let ((a!3 (and (main@_21 main@%.13.i_0
                          main@%loop.bound_0
                          @A_right_0
                          main@%sm4_0
                          main@%_7_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0)
                true
                (= main@%_22_0 (< main@%.13.i_0 main@%loop.bound2_0))
                (= main@%_23_0 (+ main@%.13.i_0 1))
                (=> main@.preheader_0 (and main@.preheader_0 main@_21_0))
                (=> (and main@.preheader_0 main@_21_0) (not main@%_22_0))
                (=> main@.preheader_0 a!1)
                (=> main@.preheader_0 (or (<= @A_right_0 0) (> main@%_24_0 0)))
                (=> main@.preheader_0
                    (= main@%_25_0 (select main@%sm4_0 main@%_24_0)))
                (=> main@.preheader_0
                    (= main@%_26_0 (< main@%_25_0 main@%_7_0)))
                (=> main@.critedge1.i_0
                    (and main@.critedge1.i_0 main@.preheader_0))
                (=> (and main@.critedge1.i_0 main@.preheader_0)
                    (not main@%_26_0))
                (=> (and main@.critedge1.i_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@.critedge1.i_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@.critedge1.i_0 a!2)
                (=> main@.critedge1.i_0
                    (or (<= @A_right_0 0) (> main@%_33_0 0)))
                (=> main@.critedge1.i_0 (> @A_right_0 0))
                (=> main@.critedge1.i_0
                    (= main@%sm6_0 (store main@%sm4_0 main@%_33_0 main@%_7_0)))
                (=> main@_34_0 (and main@_34_0 main@.critedge1.i_0))
                (=> (and main@_34_0 main@.critedge1.i_0)
                    (= main@%.1.i_0 main@%.0.i.lcssa_1))
                (=> (and main@_34_0 main@.critedge1.i_0)
                    (= main@%.1.i_1 main@%.1.i_0))
                main@_34_0)))
  (=> a!3 (main@_34 main@%.13.i_0 main@%.1.i_1 main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@_27_0
               (= main@%_28_0 (+ @A_right_0 (* 0 44) (* main@%_31_0 4))))))
(let ((a!2 (and (main@.lr.ph main@%.13.i_0
                             main@%loop.bound_0
                             @A_right_0
                             main@%sm4_0
                             main@%_7_0
                             main@%.0.i13_0
                             main@%loop.bound1_0)
                true
                (= main@%_31_0 (+ main@%.0.i13_0 1))
                (= main@%_32_0 (< main@%.0.i13_0 main@%loop.bound1_0))
                (=> main@_27_0 (and main@_27_0 main@.lr.ph_0))
                (=> (and main@_27_0 main@.lr.ph_0) main@%_32_0)
                a!1
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm4_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_7_0)))
                (=> main@.lr.ph_1 (and main@.lr.ph_1 main@_27_0))
                (=> (and main@.lr.ph_1 main@_27_0) main@%_30_0)
                (=> (and main@.lr.ph_1 main@_27_0)
                    (= main@%.0.i13_1 main@%_31_0))
                (=> (and main@.lr.ph_1 main@_27_0)
                    (= main@%.0.i13_2 main@%.0.i13_1))
                main@.lr.ph_1)))
  (=> a!2
      (main@.lr.ph main@%.13.i_0
                   main@%loop.bound_0
                   @A_right_0
                   main@%sm4_0
                   main@%_7_0
                   main@%.0.i13_2
                   main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_28_0 (+ (+ @A_right_0 (* 0 44)) (* main@%_31_0 4))))
      (a!2 (= main@%_33_0 (+ (+ @A_right_0 (* 0 44)) (* main@%.0.i.lcssa_2 4)))))
(let ((a!3 (and (main@.lr.ph main@%.13.i_0
                             main@%loop.bound_0
                             @A_right_0
                             main@%sm4_0
                             main@%_7_0
                             main@%.0.i13_0
                             main@%loop.bound1_0)
                true
                (= main@%_31_0 (+ main@%.0.i13_0 1))
                (= main@%_32_0 (< main@%.0.i13_0 main@%loop.bound1_0))
                (=> main@_27_0 (and main@_27_0 main@.lr.ph_0))
                (=> (and main@_27_0 main@.lr.ph_0) main@%_32_0)
                (=> main@_27_0 a!1)
                (=> main@_27_0 (or (<= @A_right_0 0) (> main@%_28_0 0)))
                (=> main@_27_0 (> @A_right_0 0))
                (=> main@_27_0 (= main@%_29_0 (select main@%sm4_0 main@%_28_0)))
                (=> main@_27_0 (= main@%_30_0 (< main@%_29_0 main@%_7_0)))
                (=> |tuple(main@.lr.ph_0, main@.critedge1.i_0)| main@.lr.ph_0)
                (=> |tuple(main@_27_0, main@.critedge1.i_0)| main@_27_0)
                (=> main@.critedge1.i_0
                    (or |tuple(main@.lr.ph_0, main@.critedge1.i_0)|
                        |tuple(main@_27_0, main@.critedge1.i_0)|))
                (=> |tuple(main@.lr.ph_0, main@.critedge1.i_0)|
                    (not main@%_32_0))
                (=> |tuple(main@_27_0, main@.critedge1.i_0)| (not main@%_30_0))
                (=> |tuple(main@.lr.ph_0, main@.critedge1.i_0)|
                    (= main@%.0.i.lcssa_0 main@%_31_0))
                (=> |tuple(main@_27_0, main@.critedge1.i_0)|
                    (= main@%.0.i.lcssa_1 main@%_31_0))
                (=> |tuple(main@.lr.ph_0, main@.critedge1.i_0)|
                    (= main@%.0.i.lcssa_2 main@%.0.i.lcssa_0))
                (=> |tuple(main@_27_0, main@.critedge1.i_0)|
                    (= main@%.0.i.lcssa_2 main@%.0.i.lcssa_1))
                (=> main@.critedge1.i_0 a!2)
                (=> main@.critedge1.i_0
                    (or (<= @A_right_0 0) (> main@%_33_0 0)))
                (=> main@.critedge1.i_0 (> @A_right_0 0))
                (=> main@.critedge1.i_0
                    (= main@%sm6_0 (store main@%sm4_0 main@%_33_0 main@%_7_0)))
                (=> main@_34_0 (and main@_34_0 main@.critedge1.i_0))
                (=> (and main@_34_0 main@.critedge1.i_0)
                    (= main@%.1.i_0 main@%.0.i.lcssa_2))
                (=> (and main@_34_0 main@.critedge1.i_0)
                    (= main@%.1.i_1 main@%.1.i_0))
                main@_34_0)))
  (=> a!3 (main@_34 main@%.13.i_0 main@%.1.i_1 main@%loop.bound_0)))))
(rule (=> (and (main@_34 main@%.13.i_0 main@%.1.i_0 main@%loop.bound_0)
         true
         (= main@%_35_0 (< main@%.1.i_0 main@%loop.bound_0))
         (= main@%_36_0 (+ main@%.1.i_0 1))
         (=> main@_34_1 (and main@_34_1 main@_34_0))
         (=> (and main@_34_1 main@_34_0) main@%_35_0)
         (=> (and main@_34_1 main@_34_0) (= main@%.1.i_1 main@%_36_0))
         (=> (and main@_34_1 main@_34_0) (= main@%.1.i_2 main@%.1.i_1))
         main@_34_1)
    (main@_34 main@%.13.i_0 main@%.1.i_2 main@%loop.bound_0)))
(rule (let ((a!1 (and (main@_34 main@%.13.i_0 main@%.1.i_0 main@%loop.bound_0)
                true
                (= main@%_35_0 (< main@%.1.i_0 main@%loop.bound_0))
                (= main@%_36_0 (+ main@%.1.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_34_0))
                (=> (and main@verifier.error_0 main@_34_0) (not main@%_35_0))
                (=> main@verifier.error_0
                    (= main@%_37_0 (= main@%.13.i_0 main@%.1.i_0)))
                (=> main@verifier.error_0 (not main@%_37_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

