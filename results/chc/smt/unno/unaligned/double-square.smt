(set-info :original "./results/chc/bytecode/unno/unaligned/double-square.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph5 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_16_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%.0.i2_2 Int )
(declare-var main@%.01.i1_2 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%.02.i4_2 Int )
(declare-var main@%.03.i3_2 Int )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_7_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@.lr.ph5.preheader_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@.lr.ph5_0 Bool )
(declare-var main@%.02.i4_0 Int )
(declare-var main@%.03.i3_0 Int )
(declare-var main@%.02.i4_1 Int )
(declare-var main@%.03.i3_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.03.i.lcssa_0 Int )
(declare-var main@%.03.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0.i2_0 Int )
(declare-var main@%.01.i1_0 Int )
(declare-var main@%.0.i2_1 Int )
(declare-var main@%.01.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.0.i.lcssa_0 Int )
(declare-var main@%.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@.lr.ph5_1 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%phi.bo_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 1))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 1))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 0))
                (=> main@.lr.ph5.preheader_0
                    (and main@.lr.ph5.preheader_0 main@entry_0))
                (=> (and main@.lr.ph5.preheader_0 main@entry_0) main@%_7_0)
                (=> main@.lr.ph5.preheader_0 (= main@%_8_0 (* main@%_3_0 2)))
                (=> main@.lr.ph5_0
                    (and main@.lr.ph5_0 main@.lr.ph5.preheader_0))
                (=> (and main@.lr.ph5_0 main@.lr.ph5.preheader_0)
                    (= main@%.02.i4_0 main@%_8_0))
                (=> (and main@.lr.ph5_0 main@.lr.ph5.preheader_0)
                    (= main@%.03.i3_0 0))
                (=> (and main@.lr.ph5_0 main@.lr.ph5.preheader_0)
                    (= main@%.02.i4_1 main@%.02.i4_0))
                (=> (and main@.lr.ph5_0 main@.lr.ph5.preheader_0)
                    (= main@%.03.i3_1 main@%.03.i3_0))
                main@.lr.ph5_0)))
  (=> a!1
      (main@.lr.ph5 main@%_5_0
                    main@%loop.bound_0
                    main@%.02.i4_1
                    main@%.03.i3_1
                    main@%_3_0
                    main@%loop.bound1_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 1))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 1))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 0))
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_9_0 (> main@%_5_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_9_0)
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.0.i2_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i1_0 main@%_5_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i2_1 main@%.0.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i1_1 main@%.01.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.03.i.lcssa_1
                   main@%.01.i1_1
                   main@%.0.i2_1
                   main@%_5_0
                   main@%loop.bound_0))))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 (= main@%loop.bound_0 1))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 1))
                main@%_1_0
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 (= main@%_3_0 main@%_5_0))
                main@%_6_0
                (= main@%_7_0 (> main@%_3_0 0))
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_7_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_9_0 (> main@%_5_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_9_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_16_0 (= main@%.03.i.lcssa_1 main@%.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_16_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph5 main@%_5_0
                       main@%loop.bound_0
                       main@%.02.i4_0
                       main@%.03.i3_0
                       main@%_3_0
                       main@%loop.bound1_0)
         true
         (= main@%_10_0 (+ main@%.02.i4_0 (- 1)))
         (= main@%_11_0 (+ main@%.03.i3_0 main@%_3_0))
         (= main@%_12_0 (> main@%.02.i4_0 main@%loop.bound1_0))
         (=> main@.lr.ph5_1 (and main@.lr.ph5_1 main@.lr.ph5_0))
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0) main@%_12_0)
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0) (= main@%.02.i4_1 main@%_10_0))
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0) (= main@%.03.i3_1 main@%_11_0))
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0)
             (= main@%.02.i4_2 main@%.02.i4_1))
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0)
             (= main@%.03.i3_2 main@%.03.i3_1))
         main@.lr.ph5_1)
    (main@.lr.ph5 main@%_5_0
                  main@%loop.bound_0
                  main@%.02.i4_2
                  main@%.03.i3_2
                  main@%_3_0
                  main@%loop.bound1_0)))
(rule (let ((a!1 (and (main@.lr.ph5 main@%_5_0
                              main@%loop.bound_0
                              main@%.02.i4_0
                              main@%.03.i3_0
                              main@%_3_0
                              main@%loop.bound1_0)
                true
                (= main@%_10_0 (+ main@%.02.i4_0 (- 1)))
                (= main@%_11_0 (+ main@%.03.i3_0 main@%_3_0))
                (= main@%_12_0 (> main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph5_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0) (not main@%_12_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0)
                    (= main@%.03.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_9_0 (> main@%_5_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_9_0)
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.0.i2_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i1_0 main@%_5_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i2_1 main@%.0.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i1_1 main@%.01.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.03.i.lcssa_1
                   main@%.01.i1_1
                   main@%.0.i2_1
                   main@%_5_0
                   main@%loop.bound_0))))
(rule (let ((a!1 (and (main@.lr.ph5 main@%_5_0
                              main@%loop.bound_0
                              main@%.02.i4_0
                              main@%.03.i3_0
                              main@%_3_0
                              main@%loop.bound1_0)
                true
                (= main@%_10_0 (+ main@%.02.i4_0 (- 1)))
                (= main@%_11_0 (+ main@%.03.i3_0 main@%_3_0))
                (= main@%_12_0 (> main@%.02.i4_0 main@%loop.bound1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph5_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0) (not main@%_12_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0)
                    (= main@%.03.i.lcssa_0 main@%_11_0))
                (=> (and main@.preheader_0 main@.lr.ph5_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_9_0 (> main@%_5_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_9_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_16_0 (= main@%.03.i.lcssa_1 main@%.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_16_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (= main@%_15_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.01.i1_0 0)
                        (< main@%loop.bound_0 main@%.01.i1_0)
                        true)
                   (ite (< main@%.01.i1_0 0)
                        (< main@%loop.bound_0 main@%.01.i1_0)
                        false)))))
  (=> (and (main@.lr.ph main@%.03.i.lcssa_0
                        main@%.01.i1_0
                        main@%.0.i2_0
                        main@%_5_0
                        main@%loop.bound_0)
           true
           (= main@%_13_0 (+ main@%.01.i1_0 (- 1)))
           (= main@%_14_0 (+ main@%.0.i2_0 main@%_5_0))
           a!1
           (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_15_0)
           (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i2_1 main@%_14_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.01.i1_1 main@%_13_0))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.0.i2_2 main@%.0.i2_1))
           (=> (and main@.lr.ph_1 main@.lr.ph_0)
               (= main@%.01.i1_2 main@%.01.i1_1))
           main@.lr.ph_1)
      (main@.lr.ph main@%.03.i.lcssa_0
                   main@%.01.i1_2
                   main@%.0.i2_2
                   main@%_5_0
                   main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_15_0
              (ite (>= main@%loop.bound_0 0)
                   (ite (>= main@%.01.i1_0 0)
                        (< main@%loop.bound_0 main@%.01.i1_0)
                        true)
                   (ite (< main@%.01.i1_0 0)
                        (< main@%loop.bound_0 main@%.01.i1_0)
                        false)))))
(let ((a!2 (and (main@.lr.ph main@%.03.i.lcssa_0
                             main@%.01.i1_0
                             main@%.0.i2_0
                             main@%_5_0
                             main@%loop.bound_0)
                true
                (= main@%_13_0 (+ main@%.01.i1_0 (- 1)))
                (= main@%_14_0 (+ main@%.0.i2_0 main@%_5_0))
                a!1
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.lr.ph_0))
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    (not main@%_15_0))
                (=> main@verifier.error.loopexit_0
                    (= main@%phi.bo_0 (* main@%_14_0 2)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.0.i.lcssa_0 main@%phi.bo_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.0.i.lcssa_1 main@%.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_16_0 (= main@%.03.i.lcssa_0 main@%.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_16_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!2 main@verifier.error.split))))
(query main@verifier.error.split)

