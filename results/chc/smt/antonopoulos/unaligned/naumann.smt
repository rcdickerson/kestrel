(set-info :original "./results/chc/bytecode/antonopoulos/unaligned/naumann.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph7 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_21_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%.0.i3_2 Int )
(declare-var main@%.01.i2_2 Int )
(declare-var main@%.07.i1_2 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Bool )
(declare-var main@%.02.i6_2 Int )
(declare-var main@%.04.i5_2 Int )
(declare-var main@%.06.i4_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@.lr.ph7_0 Bool )
(declare-var main@%.02.i6_0 Int )
(declare-var main@%.04.i5_0 Int )
(declare-var main@%.06.i4_0 Int )
(declare-var main@%.02.i6_1 Int )
(declare-var main@%.04.i5_1 Int )
(declare-var main@%.06.i4_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.04.i.lcssa_0 Int )
(declare-var main@%.04.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0.i3_0 Int )
(declare-var main@%.01.i2_0 Int )
(declare-var main@%.07.i1_0 Int )
(declare-var main@%.0.i3_1 Int )
(declare-var main@%.01.i2_1 Int )
(declare-var main@%.07.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.01.i.lcssa_0 Int )
(declare-var main@%.01.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%.15.i_0 Int )
(declare-var main@%.13.i_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@.lr.ph7_1 Bool )
(declare-var main@%.18.i_0 Int )
(declare-var main@%.1.i_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@.lr.ph_1 Bool )
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
         (=> main@.lr.ph7_0 (and main@.lr.ph7_0 main@entry_0))
         (=> (and main@.lr.ph7_0 main@entry_0) main@%_7_0)
         (=> (and main@.lr.ph7_0 main@entry_0) (= main@%.02.i6_0 main@%_3_0))
         (=> (and main@.lr.ph7_0 main@entry_0) (= main@%.04.i5_0 24))
         (=> (and main@.lr.ph7_0 main@entry_0) (= main@%.06.i4_0 0))
         (=> (and main@.lr.ph7_0 main@entry_0)
             (= main@%.02.i6_1 main@%.02.i6_0))
         (=> (and main@.lr.ph7_0 main@entry_0)
             (= main@%.04.i5_1 main@%.04.i5_0))
         (=> (and main@.lr.ph7_0 main@entry_0)
             (= main@%.06.i4_1 main@%.06.i4_0))
         main@.lr.ph7_0)
    (main@.lr.ph7 main@%loop.bound_0
                  main@%_5_0
                  main@%.06.i4_1
                  main@%.02.i6_1
                  main@%.04.i5_1
                  main@%loop.bound1_0)))
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
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.04.i.lcssa_0 24))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_8_0 (> main@%_5_0 4)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_8_0)
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.0.i3_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.01.i2_0 16))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.07.i1_0 main@%_5_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_1 main@%.0.i3_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i2_1 main@%.01.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.07.i1_1 main@%.07.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.04.i.lcssa_1
                   main@%.0.i3_1
                   main@%.01.i2_1
                   main@%.07.i1_1
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
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.04.i.lcssa_0 24))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_8_0 (> main@%_5_0 4)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_8_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.01.i.lcssa_0 16))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_21_0 (> main@%.04.i.lcssa_1 main@%.01.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (= main@%_14_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        true)
                   (ite (< main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        false)))))
  (=> (and (main@.lr.ph7 main@%loop.bound_0
                         main@%_5_0
                         main@%.06.i4_0
                         main@%.02.i6_0
                         main@%.04.i5_0
                         main@%loop.bound1_0)
           true
           (= main@%_9_0 (mod main@%.06.i4_0 2))
           (= main@%_10_0 (= main@%_9_0 0))
           (= main@%_11_0 (ite main@%_10_0 main@%.02.i6_0 1))
           (= main@%_12_0 (ite main@%_10_0 (- 1) 0))
           (= main@%.13.i_0 (+ main@%.02.i6_0 main@%_12_0))
           (= main@%_13_0 (+ main@%.06.i4_0 1))
           a!1
           (=> main@.lr.ph7_1 (and main@.lr.ph7_1 main@.lr.ph7_0))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0) main@%_14_0)
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.02.i6_1 main@%.13.i_0))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.04.i5_1 main@%.15.i_0))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.06.i4_1 main@%_13_0))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.02.i6_2 main@%.02.i6_1))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.04.i5_2 main@%.04.i5_1))
           (=> (and main@.lr.ph7_1 main@.lr.ph7_0)
               (= main@%.06.i4_2 main@%.06.i4_1))
           main@.lr.ph7_1)
      (main@.lr.ph7 main@%loop.bound_0
                    main@%_5_0
                    main@%.06.i4_2
                    main@%.02.i6_2
                    main@%.04.i5_2
                    main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_14_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        true)
                   (ite (< main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph7 main@%loop.bound_0
                              main@%_5_0
                              main@%.06.i4_0
                              main@%.02.i6_0
                              main@%.04.i5_0
                              main@%loop.bound1_0)
                true
                (= main@%_9_0 (mod main@%.06.i4_0 2))
                (= main@%_10_0 (= main@%_9_0 0))
                (= main@%_11_0 (ite main@%_10_0 main@%.02.i6_0 1))
                (= main@%_12_0 (ite main@%_10_0 (- 1) 0))
                (= main@%.13.i_0 (+ main@%.02.i6_0 main@%_12_0))
                (= main@%_13_0 (+ main@%.06.i4_0 1))
                a!1
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_14_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.04.i.lcssa_0 main@%.15.i_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_8_0 (> main@%_5_0 4)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_8_0)
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.0.i3_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.01.i2_0 16))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.07.i1_0 main@%_5_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_1 main@%.0.i3_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i2_1 main@%.01.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.07.i1_1 main@%.07.i1_0))
                main@.lr.ph_0)))
  (=> a!2
      (main@.lr.ph main@%.04.i.lcssa_1
                   main@%.0.i3_1
                   main@%.01.i2_1
                   main@%.07.i1_1
                   main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_14_0
              (ite (>= main@%loop.bound1_0 0)
                   (ite (>= main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        true)
                   (ite (< main@%.13.i_0 0)
                        (< main@%loop.bound1_0 main@%.13.i_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph7 main@%loop.bound_0
                              main@%_5_0
                              main@%.06.i4_0
                              main@%.02.i6_0
                              main@%.04.i5_0
                              main@%loop.bound1_0)
                true
                (= main@%_9_0 (mod main@%.06.i4_0 2))
                (= main@%_10_0 (= main@%_9_0 0))
                (= main@%_11_0 (ite main@%_10_0 main@%.02.i6_0 1))
                (= main@%_12_0 (ite main@%_10_0 (- 1) 0))
                (= main@%.13.i_0 (+ main@%.02.i6_0 main@%_12_0))
                (= main@%_13_0 (+ main@%.06.i4_0 1))
                a!1
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph7_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0) (not main@%_14_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.04.i.lcssa_0 main@%.15.i_0))
                (=> (and main@.preheader_0 main@.lr.ph7_0)
                    (= main@%.04.i.lcssa_1 main@%.04.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_8_0 (> main@%_5_0 4)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_8_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.01.i.lcssa_0 16))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_21_0 (> main@%.04.i.lcssa_1 main@%.01.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!2 main@verifier.error.split))))
(rule (let ((a!1 (= main@%_20_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.18.i_0 0)
                        (< main@%loop.bound_0 main@%.18.i_0)
                        true)
                   (ite (< main@%.18.i_0 0)
                        (< main@%loop.bound_0 main@%.18.i_0)
                        false)))))
  (=> (and (main@.lr.ph main@%.04.i.lcssa_0
                        main@%.0.i3_0
                        main@%.01.i2_0
                        main@%.07.i1_0
                        main@%loop.bound_0)
           true
           (= main@%_15_0 (rem main@%.0.i3_0 3))
           (= main@%_16_0 (= main@%_15_0 0))
           (= main@%_17_0 (* main@%.01.i2_0 2))
           (= main@%_18_0 (ite main@%_16_0 (- 1) 0))
           (= main@%.18.i_0 (+ main@%.07.i1_0 main@%_18_0))
           (= main@%.1.i_0 (ite main@%_16_0 main@%_17_0 main@%.01.i2_0))
           (= main@%_19_0 (+ main@%.0.i3_0 1))
           a!1
           (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_20_0)
           (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i3_1 main@%_19_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.01.i2_1 main@%.1.i_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.07.i1_1 main@%.18.i_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.0.i3_2 main@%.0.i3_1))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.01.i2_2 main@%.01.i2_1))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.07.i1_2 main@%.07.i1_1))
           main@.lr.ph_1)
      (main@.lr.ph main@%.04.i.lcssa_0
                   main@%.0.i3_2
                   main@%.01.i2_2
                   main@%.07.i1_2
                   main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_20_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.18.i_0 0)
                        (< main@%loop.bound_0 main@%.18.i_0)
                        true)
                   (ite (< main@%.18.i_0 0)
                        (< main@%loop.bound_0 main@%.18.i_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph main@%.04.i.lcssa_0
                             main@%.0.i3_0
                             main@%.01.i2_0
                             main@%.07.i1_0
                             main@%loop.bound_0)
                true
                (= main@%_15_0 (rem main@%.0.i3_0 3))
                (= main@%_16_0 (= main@%_15_0 0))
                (= main@%_17_0 (* main@%.01.i2_0 2))
                (= main@%_18_0 (ite main@%_16_0 (- 1) 0))
                (= main@%.18.i_0 (+ main@%.07.i1_0 main@%_18_0))
                (= main@%.1.i_0 (ite main@%_16_0 main@%_17_0 main@%.01.i2_0))
                (= main@%_19_0 (+ main@%.0.i3_0 1))
                a!1
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0) (not main@%_20_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.01.i.lcssa_0 main@%.1.i_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.01.i.lcssa_1 main@%.01.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_21_0 (> main@%.04.i.lcssa_0 main@%.01.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!2 main@verifier.error.split))))
(query main@verifier.error.split)

