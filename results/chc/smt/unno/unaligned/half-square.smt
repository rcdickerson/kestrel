(set-info :original "./results/chc/bytecode/unno/unaligned/half-square.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@_18 (Int Int Int ))
(declare-rel main@.preheader2 (Int Int ))
(declare-rel main@.preheader.preheader.split ())
(declare-var main@%_21_0 Bool )
(declare-var main@%_19_0 Bool )
(declare-var main@%.02.i_2 Int )
(declare-var main@%.04.i_2 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%_11_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var @arb_int_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_17_3 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@_9_0 Bool )
(declare-var main@_12_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@_16_0 Bool )
(declare-var |tuple(main@_9_0, main@_16_0)| Bool )
(declare-var |tuple(main@entry_0, main@_16_0)| Bool )
(declare-var main@%_17_0 Bool )
(declare-var main@%_17_1 Bool )
(declare-var main@%_17_2 Bool )
(declare-var main@_18_0 Bool )
(declare-var main@%.04.i_0 Int )
(declare-var main@%.04.i_1 Int )
(declare-var main@%_20_0 Int )
(declare-var main@_18_1 Bool )
(declare-var main@.preheader2_0 Bool )
(declare-var main@%.02.i_0 Int )
(declare-var main@%.02.i_1 Int )
(declare-var main@%_22_0 Int )
(declare-var main@.preheader2_1 Bool )
(declare-var main@.preheader.preheader_0 Bool )
(declare-var main@.preheader.preheader.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @arb_int_0))
(rule (let ((a!1 (and (main@entry @arb_int_0)
                true
                (= main@%_0_0 @arb_int_0)
                (= main@%_2_0 @arb_int_0)
                (= main@%_4_0 @arb_int_0)
                (= main@%_6_0 @arb_int_0)
                (= main@%_8_0 (= main@%_1_0 main@%_5_0))
                (=> main@_9_0 (and main@_9_0 main@entry_0))
                (=> (and main@_9_0 main@entry_0) main@%_8_0)
                (=> main@_9_0 (= main@%_10_0 (> main@%_1_0 main@%_3_0)))
                (=> main@_9_0 (= main@%_11_0 (> main@%_3_0 0)))
                (=> main@_9_0
                    (= main@%or.cond.i_0 (and main@%_10_0 main@%_11_0)))
                (=> main@_12_0 (and main@_12_0 main@_9_0))
                (=> (and main@_12_0 main@_9_0) main@%or.cond.i_0)
                (=> main@_12_0 (= main@%_13_0 (> main@%_1_0 main@%_7_0)))
                (=> main@_12_0 (= main@%_14_0 (> main@%_7_0 0)))
                (=> main@_12_0 (= main@%_15_0 (and main@%_13_0 main@%_14_0)))
                (=> |tuple(main@_9_0, main@_16_0)| main@_9_0)
                (=> |tuple(main@entry_0, main@_16_0)| main@entry_0)
                (=> main@_16_0
                    (or (and main@_16_0 main@_12_0)
                        |tuple(main@_9_0, main@_16_0)|
                        |tuple(main@entry_0, main@_16_0)|))
                (=> |tuple(main@_9_0, main@_16_0)| (not main@%or.cond.i_0))
                (=> |tuple(main@entry_0, main@_16_0)| (not main@%_8_0))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_0 main@%_15_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_1 false))
                (=> |tuple(main@entry_0, main@_16_0)| (= main@%_17_2 false))
                (=> (and main@_16_0 main@_12_0) (= main@%_17_3 main@%_17_0))
                (=> |tuple(main@_9_0, main@_16_0)| (= main@%_17_3 main@%_17_1))
                (=> |tuple(main@entry_0, main@_16_0)|
                    (= main@%_17_3 main@%_17_2))
                (=> main@_16_0 main@%_17_3)
                (=> main@_18_0 (and main@_18_0 main@_16_0))
                (=> (and main@_18_0 main@_16_0) (= main@%.04.i_0 0))
                (=> (and main@_18_0 main@_16_0) (= main@%.04.i_1 main@%.04.i_0))
                main@_18_0)))
  (=> a!1 (main@_18 main@%_7_0 main@%_3_0 main@%.04.i_1))))
(rule (=> (and (main@_18 main@%_7_0 main@%_3_0 main@%.04.i_0)
         true
         (= main@%_19_0 (> main@%_3_0 main@%.04.i_0))
         (= main@%_20_0 (+ main@%.04.i_0 1))
         (=> main@_18_1 (and main@_18_1 main@_18_0))
         (=> (and main@_18_1 main@_18_0) main@%_19_0)
         (=> (and main@_18_1 main@_18_0) (= main@%.04.i_1 main@%_20_0))
         (=> (and main@_18_1 main@_18_0) (= main@%.04.i_2 main@%.04.i_1))
         main@_18_1)
    (main@_18 main@%_7_0 main@%_3_0 main@%.04.i_2)))
(rule (=> (and (main@_18 main@%_7_0 main@%_3_0 main@%.04.i_0)
         true
         (= main@%_19_0 (> main@%_3_0 main@%.04.i_0))
         (= main@%_20_0 (+ main@%.04.i_0 1))
         (=> main@.preheader2_0 (and main@.preheader2_0 main@_18_0))
         (=> (and main@.preheader2_0 main@_18_0) (not main@%_19_0))
         (=> (and main@.preheader2_0 main@_18_0) (= main@%.02.i_0 0))
         (=> (and main@.preheader2_0 main@_18_0)
             (= main@%.02.i_1 main@%.02.i_0))
         main@.preheader2_0)
    (main@.preheader2 main@%_7_0 main@%.02.i_1)))
(rule (=> (and (main@.preheader2 main@%_7_0 main@%.02.i_0)
         true
         (= main@%_21_0 (> main@%_7_0 main@%.02.i_0))
         (= main@%_22_0 (+ main@%.02.i_0 1))
         (=> main@.preheader2_1 (and main@.preheader2_1 main@.preheader2_0))
         (=> (and main@.preheader2_1 main@.preheader2_0) main@%_21_0)
         (=> (and main@.preheader2_1 main@.preheader2_0)
             (= main@%.02.i_1 main@%_22_0))
         (=> (and main@.preheader2_1 main@.preheader2_0)
             (= main@%.02.i_2 main@%.02.i_1))
         main@.preheader2_1)
    (main@.preheader2 main@%_7_0 main@%.02.i_2)))
(rule (=> (and (main@.preheader2 main@%_7_0 main@%.02.i_0)
         true
         (= main@%_21_0 (> main@%_7_0 main@%.02.i_0))
         (= main@%_22_0 (+ main@%.02.i_0 1))
         (=> main@.preheader.preheader_0
             (and main@.preheader.preheader_0 main@.preheader2_0))
         (=> (and main@.preheader.preheader_0 main@.preheader2_0)
             (not main@%_21_0))
         (=> main@.preheader.preheader_0 false)
         (=> main@.preheader.preheader.split_0
             (and main@.preheader.preheader.split_0 main@.preheader.preheader_0))
         main@.preheader.preheader.split_0)
    main@.preheader.preheader.split))
(query main@.preheader.preheader.split)

