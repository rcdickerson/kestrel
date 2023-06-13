(set-info :original "./results/chc/bytecode/chen/unaligned/barthe1.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph6 (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_22_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@%_12_0 Bool )
(declare-var main@%.0.i3_2 Int )
(declare-var main@%.01.i2_2 Int )
(declare-var main@%.02.i1_2 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%.03.i5_2 Int )
(declare-var main@%.04.i4_2 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@.lr.ph6_0 Bool )
(declare-var main@%.03.i5_0 Int )
(declare-var main@%.04.i4_0 Int )
(declare-var main@%.03.i5_1 Int )
(declare-var main@%.04.i4_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.03.i.lcssa_0 Int )
(declare-var main@%.03.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%.0.i3_0 Int )
(declare-var main@%.01.i2_0 Int )
(declare-var main@%.02.i1_0 Int )
(declare-var main@%.0.i3_1 Int )
(declare-var main@%.01.i2_1 Int )
(declare-var main@%.02.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.02.i.lcssa_0 Int )
(declare-var main@%.02.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@.lr.ph6_1 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
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
         (= main@%_4_0 @arb_int_0)
         (= main@%_6_0 @arb_int_0)
         (= main@%_8_0 (= main@%_1_0 main@%_5_0))
         (= main@%_9_0 (= main@%_3_0 main@%_7_0))
         (= main@%_10_0 (ite main@%_8_0 main@%_9_0 false))
         main@%_10_0
         (= main@%_11_0 (> main@%_1_0 0))
         (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
         (=> (and main@.lr.ph6_0 main@entry_0) main@%_11_0)
         (=> (and main@.lr.ph6_0 main@entry_0) (= main@%.03.i5_0 0))
         (=> (and main@.lr.ph6_0 main@entry_0) (= main@%.04.i4_0 0))
         (=> (and main@.lr.ph6_0 main@entry_0)
             (= main@%.03.i5_1 main@%.03.i5_0))
         (=> (and main@.lr.ph6_0 main@entry_0)
             (= main@%.04.i4_1 main@%.04.i4_0))
         main@.lr.ph6_0)
    (main@.lr.ph6 main@%_5_0
                  main@%_7_0
                  main@%.04.i4_1
                  main@%_3_0
                  main@%.03.i5_1
                  main@%_1_0)))
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
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_11_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_12_0 (> main@%_5_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_12_0)
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_0 main@%_7_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.01.i2_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.02.i1_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_1 main@%.0.i3_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i2_1 main@%.01.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.02.i1_1 main@%.02.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.03.i.lcssa_1
                   main@%.0.i3_1
                   main@%.02.i1_1
                   main@%.01.i2_1
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
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) (not main@%_11_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_0 0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_12_0 (> main@%_5_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_12_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.02.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.03.i.lcssa_1 main@%.02.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph6 main@%_5_0
                       main@%_7_0
                       main@%.04.i4_0
                       main@%_3_0
                       main@%.03.i5_0
                       main@%_1_0)
         true
         (= main@%_13_0 (* main@%.04.i4_0 5))
         (= main@%_14_0 (+ main@%_13_0 main@%_3_0))
         (= main@%_15_0 (+ main@%_14_0 main@%.03.i5_0))
         (= main@%_16_0 (+ main@%.04.i4_0 1))
         (= main@%_17_0 (< main@%_16_0 main@%_1_0))
         (=> main@.lr.ph6_1 (and main@.lr.ph6_1 main@.lr.ph6_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) main@%_17_0)
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (= main@%.03.i5_1 main@%_15_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (= main@%.04.i4_1 main@%_16_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%.03.i5_2 main@%.03.i5_1))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%.04.i4_2 main@%.04.i4_1))
         main@.lr.ph6_1)
    (main@.lr.ph6 main@%_5_0
                  main@%_7_0
                  main@%.04.i4_2
                  main@%_3_0
                  main@%.03.i5_2
                  main@%_1_0)))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_5_0
                              main@%_7_0
                              main@%.04.i4_0
                              main@%_3_0
                              main@%.03.i5_0
                              main@%_1_0)
                true
                (= main@%_13_0 (* main@%.04.i4_0 5))
                (= main@%_14_0 (+ main@%_13_0 main@%_3_0))
                (= main@%_15_0 (+ main@%_14_0 main@%.03.i5_0))
                (= main@%_16_0 (+ main@%.04.i4_0 1))
                (= main@%_17_0 (< main@%_16_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_17_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.03.i.lcssa_0 main@%_15_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_12_0 (> main@%_5_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) main@%_12_0)
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_0 main@%_7_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.01.i2_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (= main@%.02.i1_0 0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.0.i3_1 main@%.0.i3_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.01.i2_1 main@%.01.i2_0))
                (=> (and main@.lr.ph_0 main@.preheader_0)
                    (= main@%.02.i1_1 main@%.02.i1_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph main@%.03.i.lcssa_1
                   main@%.0.i3_1
                   main@%.02.i1_1
                   main@%.01.i2_1
                   main@%_5_0))))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_5_0
                              main@%_7_0
                              main@%.04.i4_0
                              main@%_3_0
                              main@%.03.i5_0
                              main@%_1_0)
                true
                (= main@%_13_0 (* main@%.04.i4_0 5))
                (= main@%_14_0 (+ main@%_13_0 main@%_3_0))
                (= main@%_15_0 (+ main@%_14_0 main@%.03.i5_0))
                (= main@%_16_0 (+ main@%.04.i4_0 1))
                (= main@%_17_0 (< main@%_16_0 main@%_1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph6_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0) (not main@%_17_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.03.i.lcssa_0 main@%_15_0))
                (=> (and main@.preheader_0 main@.lr.ph6_0)
                    (= main@%.03.i.lcssa_1 main@%.03.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_12_0 (> main@%_5_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_12_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.02.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.03.i.lcssa_1 main@%.02.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph main@%.03.i.lcssa_0
                      main@%.0.i3_0
                      main@%.02.i1_0
                      main@%.01.i2_0
                      main@%_5_0)
         true
         (= main@%_18_0 (+ main@%.0.i3_0 main@%.02.i1_0))
         (= main@%_19_0 (+ main@%.0.i3_0 5))
         (= main@%_20_0 (+ main@%.01.i2_0 1))
         (= main@%_21_0 (< main@%_20_0 main@%_5_0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_21_0)
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i3_1 main@%_19_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.01.i2_1 main@%_20_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.02.i1_1 main@%_18_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%.0.i3_2 main@%.0.i3_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.01.i2_2 main@%.01.i2_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%.02.i1_2 main@%.02.i1_1))
         main@.lr.ph_1)
    (main@.lr.ph main@%.03.i.lcssa_0
                 main@%.0.i3_2
                 main@%.02.i1_2
                 main@%.01.i2_2
                 main@%_5_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%.03.i.lcssa_0
                             main@%.0.i3_0
                             main@%.02.i1_0
                             main@%.01.i2_0
                             main@%_5_0)
                true
                (= main@%_18_0 (+ main@%.0.i3_0 main@%.02.i1_0))
                (= main@%_19_0 (+ main@%.0.i3_0 5))
                (= main@%_20_0 (+ main@%.01.i2_0 1))
                (= main@%_21_0 (< main@%_20_0 main@%_5_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.lr.ph_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0) (not main@%_21_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.02.i.lcssa_0 main@%_18_0))
                (=> (and main@verifier.error_0 main@.lr.ph_0)
                    (= main@%.02.i.lcssa_1 main@%.02.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.03.i.lcssa_0 main@%.02.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

