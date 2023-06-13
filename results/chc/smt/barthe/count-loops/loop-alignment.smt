(set-info :original "./results/chc/bytecode/barthe/count-loops/loop-alignment.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int Int Int (Array Int Int) Int (Array Int Int) (Array Int Int) Int (Array Int Int) Bool Int ))
(declare-rel main@_9 (Int Int Int Int Int Int Int (Array Int Int) Int (Array Int Int) (Array Int Int) Int (Array Int Int) Bool Int Int ))
(declare-rel main@_32 (Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@.lr.ph4 (Int Int Int Int Bool (Array Int Int) (Array Int Int) Int Int Int (Array Int Int) (Array Int Int) Int ))
(declare-rel main@.lr.ph.split.us (Int (Array Int Int) Int Int Int (Array Int Int) (Array Int Int) Int ))
(declare-rel main@_52 (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_53_0 Bool )
(declare-var main@%_54_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%_56_0 Int )
(declare-var main@%_57_0 Int )
(declare-var main@%_58_0 Bool )
(declare-var main@%_51_0 Int )
(declare-var main@%sm22_0 (Array Int Int) )
(declare-var main@%.04.i_2 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Bool )
(declare-var main@%_41_0 Bool )
(declare-var main@%_42_0 Bool )
(declare-var main@%shadow.mem.12.2_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@%.2.i2.us_2 Int )
(declare-var main@%_47_0 Int )
(declare-var main@%_48_0 Int )
(declare-var main@%_50_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@%_22_0 Bool )
(declare-var main@%shadow.mem.8.3_2 (Array Int Int) )
(declare-var main@%shadow.mem.0.3_2 (Array Int Int) )
(declare-var main@%.1.i3_2 Int )
(declare-var main@%shadow.mem.0.2_1 (Array Int Int) )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_35_0 Int )
(declare-var main@%_37_0 Int )
(declare-var main@%_40_0 Bool )
(declare-var main@%_19_2 Bool )
(declare-var main@%_20_2 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%shadow.mem.12.1_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_2 (Array Int Int) )
(declare-var main@%_33_2 Int )
(declare-var main@%.01.i623_2 Int )
(declare-var main@%_11_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i7_2 Int )
(declare-var main@%sm23_0 (Array Int Int) )
(declare-var main@%sm24_0 (Array Int Int) )
(declare-var main@%sm25_0 (Array Int Int) )
(declare-var main@%sm26_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@entry_0 Bool )
(declare-var @b_1_0 Int )
(declare-var @b_2_0 Int )
(declare-var @d_2_0 Int )
(declare-var @d_1_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_9_0 Bool )
(declare-var main@%.0.i7_0 Int )
(declare-var main@%.0.i7_1 Int )
(declare-var main@%_10_0 Int )
(declare-var main@_9_1 Bool )
(declare-var main@_12_0 Bool )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@_32_0 Bool )
(declare-var main@%shadow.mem.12.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.8.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var main@%_33_0 Int )
(declare-var main@%_34_0 Int )
(declare-var main@%.02.i524_0 Int )
(declare-var main@%.01.i623_0 Int )
(declare-var main@%shadow.mem.12.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.8.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var main@%_33_1 Int )
(declare-var main@%_34_1 Int )
(declare-var main@%.02.i524_1 Int )
(declare-var main@%.01.i623_1 Int )
(declare-var main@%sm16_0 (Array Int Int) )
(declare-var main@%_36_0 Int )
(declare-var main@%sm17_0 (Array Int Int) )
(declare-var main@%_38_0 Bool )
(declare-var main@%_39_0 Bool )
(declare-var main@_23_0 Bool )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@%_26_0 Int )
(declare-var main@%sm14_0 (Array Int Int) )
(declare-var main@%_28_0 Int )
(declare-var main@%sm15_0 (Array Int Int) )
(declare-var main@_32_1 Bool )
(declare-var main@%shadow.mem.8.1_2 (Array Int Int) )
(declare-var main@%shadow.mem.0.1_2 (Array Int Int) )
(declare-var main@%_34_2 Int )
(declare-var main@%.02.i524_2 Int )
(declare-var main@.thread_0 Bool )
(declare-var main@%_31_0 Bool )
(declare-var main@.preheader1_0 Bool )
(declare-var |tuple(main@_32_0, main@.preheader1_0)| Bool )
(declare-var main@%shadow.mem.12.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%.13.i10_0 Int )
(declare-var main@%shadow.mem.12.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%_18_1 Int )
(declare-var main@%_19_1 Bool )
(declare-var main@%_20_1 Bool )
(declare-var main@%.13.i10_1 Int )
(declare-var main@%shadow.mem.12.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%_18_2 Int )
(declare-var main@%.13.i10_2 Int )
(declare-var main@.lr.ph4_0 Bool )
(declare-var main@%shadow.mem.8.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.3_0 (Array Int Int) )
(declare-var main@%.1.i3_0 Int )
(declare-var main@%shadow.mem.8.3_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.3_1 (Array Int Int) )
(declare-var main@%.1.i3_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%shadow.mem.8.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.2_0 (Array Int Int) )
(declare-var main@%.1.i.lcssa_0 Int )
(declare-var main@%shadow.mem.8.2_1 (Array Int Int) )
(declare-var main@%.1.i.lcssa_1 Int )
(declare-var main@.lr.ph.split.us_0 Bool )
(declare-var main@%shadow.mem.12.2_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%.2.i2.us_0 Int )
(declare-var main@%shadow.mem.12.2_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%.2.i2.us_1 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%shadow.mem.12.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_0 (Array Int Int) )
(declare-var main@%shadow.mem.12.3_1 (Array Int Int) )
(declare-var main@%shadow.mem.4.3_1 (Array Int Int) )
(declare-var main@_52_0 Bool )
(declare-var main@%.04.i_0 Int )
(declare-var main@%.04.i_1 Int )
(declare-var main@%sm20_0 (Array Int Int) )
(declare-var main@%sm21_0 (Array Int Int) )
(declare-var main@%_49_0 Int )
(declare-var main@.lr.ph4_1 Bool )
(declare-var main@%sm18_0 (Array Int Int) )
(declare-var main@%_44_0 Int )
(declare-var main@%sm19_0 (Array Int Int) )
(declare-var main@.lr.ph.split.us_1 Bool )
(declare-var main@%_59_0 Int )
(declare-var main@_52_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm23_0 main@%sm24_0 main@%sm25_0 main@%sm26_0))
(rule (let ((a!1 (and (main@entry main@%sm23_0 main@%sm24_0 main@%sm25_0 main@%sm26_0)
                true
                (= main@%sm_0 main@%sm23_0)
                (= main@%sm4_0 main@%sm25_0)
                (= main@%sm5_0 main@%sm24_0)
                (= main@%sm6_0 main@%sm26_0)
                (= main@%_0_0 (= main@%loop.bound_0 19))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 20))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 17))
                main@%_2_0
                (= main@%_3_0 (= main@%loop.bound3_0 19))
                main@%_3_0
                (= main@%_4_0 (+ @b_1_0 (* 0 84) (* 0 4)))
                (or (<= @b_1_0 0) (> main@%_4_0 0))
                (= main@%_5_0 (select main@%sm_0 main@%_4_0))
                (= main@%_6_0 (+ @b_2_0 (* 0 84) (* 0 4)))
                (or (<= @b_2_0 0) (> main@%_6_0 0))
                (= main@%_7_0 (select main@%sm4_0 main@%_6_0))
                (= main@%_8_0 (= main@%_5_0 main@%_7_0))
                (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
                main@empty.loop_0)))
  (=> a!1
      (main@empty.loop @d_1_0
                       @d_2_0
                       @b_2_0
                       main@%loop.bound_0
                       @b_1_0
                       main@%loop.bound1_0
                       main@%loop.bound2_0
                       main@%sm6_0
                       main@%_7_0
                       main@%sm_0
                       main@%sm5_0
                       main@%_5_0
                       main@%sm4_0
                       main@%_8_0
                       main@%loop.bound3_0))))
(rule (let ((a!1 (main@empty.loop @d_1_0
                            @d_2_0
                            @b_2_0
                            main@%loop.bound_0
                            @b_1_0
                            main@%loop.bound1_0
                            main@%loop.bound2_0
                            main@%sm6_0
                            main@%_7_0
                            main@%sm_0
                            main@%sm5_0
                            main@%_5_0
                            main@%sm4_0
                            main@%_8_0
                            main@%loop.bound3_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop @d_1_0
                          @d_2_0
                          @b_2_0
                          main@%loop.bound_0
                          @b_1_0
                          main@%loop.bound1_0
                          main@%loop.bound2_0
                          main@%sm6_0
                          main@%_7_0
                          main@%sm_0
                          main@%sm5_0
                          main@%_5_0
                          main@%sm4_0
                          main@%_8_0
                          main@%loop.bound3_0)
         true
         (=> main@_9_0 (and main@_9_0 main@empty.loop_0))
         (=> (and main@_9_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_9_0 main@empty.loop_0) (= main@%.0.i7_0 0))
         (=> (and main@_9_0 main@empty.loop_0) (= main@%.0.i7_1 main@%.0.i7_0))
         main@_9_0)
    (main@_9 @d_1_0
             @d_2_0
             @b_2_0
             main@%loop.bound_0
             @b_1_0
             main@%loop.bound1_0
             main@%loop.bound2_0
             main@%sm6_0
             main@%_7_0
             main@%sm_0
             main@%sm5_0
             main@%_5_0
             main@%sm4_0
             main@%_8_0
             main@%.0.i7_1
             main@%loop.bound3_0)))
(rule (=> (and (main@_9 @d_1_0
                  @d_2_0
                  @b_2_0
                  main@%loop.bound_0
                  @b_1_0
                  main@%loop.bound1_0
                  main@%loop.bound2_0
                  main@%sm6_0
                  main@%_7_0
                  main@%sm_0
                  main@%sm5_0
                  main@%_5_0
                  main@%sm4_0
                  main@%_8_0
                  main@%.0.i7_0
                  main@%loop.bound3_0)
         true
         main@%_8_0
         (= main@%_10_0 (+ main@%.0.i7_0 1))
         (= main@%_11_0 (< main@%.0.i7_0 main@%loop.bound3_0))
         (=> main@_9_1 (and main@_9_1 main@_9_0))
         (=> (and main@_9_1 main@_9_0) main@%_11_0)
         (=> (and main@_9_1 main@_9_0) (= main@%.0.i7_1 main@%_10_0))
         (=> (and main@_9_1 main@_9_0) (= main@%.0.i7_2 main@%.0.i7_1))
         main@_9_1)
    (main@_9 @d_1_0
             @d_2_0
             @b_2_0
             main@%loop.bound_0
             @b_1_0
             main@%loop.bound1_0
             main@%loop.bound2_0
             main@%sm6_0
             main@%_7_0
             main@%sm_0
             main@%sm5_0
             main@%_5_0
             main@%sm4_0
             main@%_8_0
             main@%.0.i7_2
             main@%loop.bound3_0)))
(rule (let ((a!1 (= main@%_13_0 (+ (+ @d_2_0 (* 0 84)) (* 1 4))))
      (a!2 (=> main@_12_0 (= main@%_14_0 (+ @b_1_0 (* 0 84) (* 1 4)))))
      (a!3 (=> main@_12_0 (= main@%_15_0 (+ @d_1_0 (* 0 84) (* 1 4)))))
      (a!4 (=> main@_12_0 (= main@%_16_0 (+ @b_2_0 (* 0 84) (* 1 4)))))
      (a!5 (= main@%_17_0 (+ (+ @d_2_0 (* 0 84)) (* 2 4)))))
(let ((a!6 (and (main@_9 @d_1_0
                         @d_2_0
                         @b_2_0
                         main@%loop.bound_0
                         @b_1_0
                         main@%loop.bound1_0
                         main@%loop.bound2_0
                         main@%sm6_0
                         main@%_7_0
                         main@%sm_0
                         main@%sm5_0
                         main@%_5_0
                         main@%sm4_0
                         main@%_8_0
                         main@%.0.i7_0
                         main@%loop.bound3_0)
                true
                main@%_8_0
                (= main@%_10_0 (+ main@%.0.i7_0 1))
                (= main@%_11_0 (< main@%.0.i7_0 main@%loop.bound3_0))
                (=> main@_12_0 (and main@_12_0 main@_9_0))
                (=> (and main@_12_0 main@_9_0) (not main@%_11_0))
                (=> main@_12_0 a!1)
                (=> main@_12_0 (or (<= @d_2_0 0) (> main@%_13_0 0)))
                (=> main@_12_0 (> @d_2_0 0))
                (=> main@_12_0
                    (= main@%sm7_0 (store main@%sm6_0 main@%_13_0 main@%_7_0)))
                a!2
                (=> main@_12_0 (or (<= @b_1_0 0) (> main@%_14_0 0)))
                (=> main@_12_0 (> @b_1_0 0))
                (=> main@_12_0 (= main@%sm8_0 (store main@%sm_0 main@%_14_0 0)))
                a!3
                (=> main@_12_0 (or (<= @d_1_0 0) (> main@%_15_0 0)))
                (=> main@_12_0 (> @d_1_0 0))
                (=> main@_12_0
                    (= main@%sm9_0 (store main@%sm5_0 main@%_15_0 main@%_5_0)))
                a!4
                (=> main@_12_0 (or (<= @b_2_0 0) (> main@%_16_0 0)))
                (=> main@_12_0 (> @b_2_0 0))
                (=> main@_12_0
                    (= main@%sm10_0 (store main@%sm4_0 main@%_16_0 0)))
                (=> main@_12_0 a!5)
                (=> main@_12_0 (or (<= @d_2_0 0) (> main@%_17_0 0)))
                (=> main@_12_0 (> @d_2_0 0))
                (=> main@_12_0
                    (= main@%sm11_0 (store main@%sm7_0 main@%_17_0 0)))
                (=> main@_32_0 (and main@_32_0 main@_12_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.12.1_0 main@%sm11_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.4.1_0 main@%sm10_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.8.1_0 main@%sm9_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@_32_0 main@_12_0) (= main@%_33_0 2))
                (=> (and main@_32_0 main@_12_0) (= main@%_34_0 2))
                (=> (and main@_32_0 main@_12_0) (= main@%.02.i524_0 1))
                (=> (and main@_32_0 main@_12_0) (= main@%.01.i623_0 1))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.12.1_1 main@%shadow.mem.12.1_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.8.1_1 main@%shadow.mem.8.1_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@_32_0 main@_12_0) (= main@%_33_1 main@%_33_0))
                (=> (and main@_32_0 main@_12_0) (= main@%_34_1 main@%_34_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%.02.i524_1 main@%.02.i524_0))
                (=> (and main@_32_0 main@_12_0)
                    (= main@%.01.i623_1 main@%.01.i623_0))
                main@_32_0)))
  (=> a!6
      (main@_32 @d_1_0
                @d_2_0
                @b_2_0
                main@%loop.bound_0
                @b_1_0
                main@%loop.bound1_0
                main@%_34_1
                main@%shadow.mem.0.1_1
                main@%shadow.mem.8.1_1
                main@%.02.i524_1
                main@%loop.bound2_0
                main@%shadow.mem.12.1_1
                main@%shadow.mem.4.1_1
                main@%_33_1
                main@%.01.i623_1)))))
(rule (let ((a!1 (= main@%_35_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_33_0 4))))
      (a!2 (= main@%_37_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!3 (=> main@_23_0 (= main@%_24_0 (+ @b_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!4 (=> main@_23_0 (= main@%_25_0 (+ @d_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!5 (= main@%_27_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!6 (= main@%_29_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_28_0 4)))))
(let ((a!7 (and (main@_32 @d_1_0
                          @d_2_0
                          @b_2_0
                          main@%loop.bound_0
                          @b_1_0
                          main@%loop.bound1_0
                          main@%_34_0
                          main@%shadow.mem.0.1_0
                          main@%shadow.mem.8.1_0
                          main@%.02.i524_0
                          main@%loop.bound2_0
                          main@%shadow.mem.12.1_0
                          main@%shadow.mem.4.1_0
                          main@%_33_0
                          main@%.01.i623_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_35_0 0))
                (> @b_2_0 0)
                (= main@%sm16_0 (store main@%shadow.mem.4.1_0 main@%_35_0 0))
                (= main@%_36_0 (+ main@%.02.i524_0 2))
                a!2
                (or (<= @d_2_0 0) (> main@%_37_0 0))
                (> @d_2_0 0)
                (= main@%sm17_0 (store main@%shadow.mem.12.1_0 main@%_37_0 0))
                (= main@%_38_0 (< main@%.01.i623_0 20))
                (= main@%_39_0 (not (= main@%.02.i524_0 18)))
                (= main@%_40_0 (ite main@%_38_0 main@%_39_0 false))
                (=> main@_23_0 (and main@_23_0 main@_32_0))
                (=> (and main@_23_0 main@_32_0) main@%_40_0)
                a!3
                (=> main@_23_0 (or (<= @b_1_0 0) (> main@%_24_0 0)))
                (=> main@_23_0 (> @b_1_0 0))
                (=> main@_23_0
                    (= main@%sm12_0
                       (store main@%shadow.mem.0.1_0 main@%_24_0 0)))
                a!4
                (=> main@_23_0 (or (<= @d_1_0 0) (> main@%_25_0 0)))
                (=> main@_23_0 (> @d_1_0 0))
                (=> main@_23_0
                    (= main@%sm13_0
                       (store main@%shadow.mem.8.1_0 main@%_25_0 0)))
                (=> main@_23_0 (= main@%_26_0 (+ main@%_34_0 1)))
                (=> main@_23_0 a!5)
                (=> main@_23_0 (or (<= @b_2_0 0) (> main@%_27_0 0)))
                (=> main@_23_0 (> @b_2_0 0))
                (=> main@_23_0
                    (= main@%sm14_0 (store main@%sm16_0 main@%_27_0 0)))
                (=> main@_23_0 (= main@%_28_0 (+ main@%.02.i524_0 3)))
                (=> main@_23_0 a!6)
                (=> main@_23_0 (or (<= @d_2_0 0) (> main@%_29_0 0)))
                (=> main@_23_0 (> @d_2_0 0))
                (=> main@_23_0
                    (= main@%sm15_0 (store main@%sm17_0 main@%_29_0 0)))
                (=> main@_23_0
                    (= main@%_30_0 (< main@%.02.i524_0 main@%loop.bound2_0)))
                (=> main@_32_1 (and main@_32_1 main@_23_0))
                (=> (and main@_32_1 main@_23_0) main@%_30_0)
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.12.1_1 main@%sm15_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.4.1_1 main@%sm14_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.8.1_1 main@%sm13_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.0.1_1 main@%sm12_0))
                (=> (and main@_32_1 main@_23_0) (= main@%_33_1 main@%_28_0))
                (=> (and main@_32_1 main@_23_0) (= main@%_34_1 main@%_26_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%.02.i524_1 main@%_36_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%.01.i623_1 main@%_34_0))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.12.1_2 main@%shadow.mem.12.1_1))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.4.1_2 main@%shadow.mem.4.1_1))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.8.1_2 main@%shadow.mem.8.1_1))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%shadow.mem.0.1_2 main@%shadow.mem.0.1_1))
                (=> (and main@_32_1 main@_23_0) (= main@%_33_2 main@%_33_1))
                (=> (and main@_32_1 main@_23_0) (= main@%_34_2 main@%_34_1))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%.02.i524_2 main@%.02.i524_1))
                (=> (and main@_32_1 main@_23_0)
                    (= main@%.01.i623_2 main@%.01.i623_1))
                main@_32_1)))
  (=> a!7
      (main@_32 @d_1_0
                @d_2_0
                @b_2_0
                main@%loop.bound_0
                @b_1_0
                main@%loop.bound1_0
                main@%_34_2
                main@%shadow.mem.0.1_2
                main@%shadow.mem.8.1_2
                main@%.02.i524_2
                main@%loop.bound2_0
                main@%shadow.mem.12.1_2
                main@%shadow.mem.4.1_2
                main@%_33_2
                main@%.01.i623_2)))))
(rule (let ((a!1 (= main@%_35_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_33_0 4))))
      (a!2 (= main@%_37_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!3 (=> main@_23_0 (= main@%_24_0 (+ @b_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!4 (=> main@_23_0 (= main@%_25_0 (+ @d_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!5 (= main@%_27_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!6 (= main@%_29_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_28_0 4)))))
(let ((a!7 (and (main@_32 @d_1_0
                          @d_2_0
                          @b_2_0
                          main@%loop.bound_0
                          @b_1_0
                          main@%loop.bound1_0
                          main@%_34_0
                          main@%shadow.mem.0.1_0
                          main@%shadow.mem.8.1_0
                          main@%.02.i524_0
                          main@%loop.bound2_0
                          main@%shadow.mem.12.1_0
                          main@%shadow.mem.4.1_0
                          main@%_33_0
                          main@%.01.i623_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_35_0 0))
                (> @b_2_0 0)
                (= main@%sm16_0 (store main@%shadow.mem.4.1_0 main@%_35_0 0))
                (= main@%_36_0 (+ main@%.02.i524_0 2))
                a!2
                (or (<= @d_2_0 0) (> main@%_37_0 0))
                (> @d_2_0 0)
                (= main@%sm17_0 (store main@%shadow.mem.12.1_0 main@%_37_0 0))
                (= main@%_38_0 (< main@%.01.i623_0 20))
                (= main@%_39_0 (not (= main@%.02.i524_0 18)))
                (= main@%_40_0 (ite main@%_38_0 main@%_39_0 false))
                (=> main@_23_0 (and main@_23_0 main@_32_0))
                (=> (and main@_23_0 main@_32_0) main@%_40_0)
                a!3
                (=> main@_23_0 (or (<= @b_1_0 0) (> main@%_24_0 0)))
                (=> main@_23_0 (> @b_1_0 0))
                (=> main@_23_0
                    (= main@%sm12_0
                       (store main@%shadow.mem.0.1_0 main@%_24_0 0)))
                a!4
                (=> main@_23_0 (or (<= @d_1_0 0) (> main@%_25_0 0)))
                (=> main@_23_0 (> @d_1_0 0))
                (=> main@_23_0
                    (= main@%sm13_0
                       (store main@%shadow.mem.8.1_0 main@%_25_0 0)))
                (=> main@_23_0 (= main@%_26_0 (+ main@%_34_0 1)))
                (=> main@_23_0 a!5)
                (=> main@_23_0 (or (<= @b_2_0 0) (> main@%_27_0 0)))
                (=> main@_23_0 (> @b_2_0 0))
                (=> main@_23_0
                    (= main@%sm14_0 (store main@%sm16_0 main@%_27_0 0)))
                (=> main@_23_0 (= main@%_28_0 (+ main@%.02.i524_0 3)))
                (=> main@_23_0 a!6)
                (=> main@_23_0 (or (<= @d_2_0 0) (> main@%_29_0 0)))
                (=> main@_23_0 (> @d_2_0 0))
                (=> main@_23_0
                    (= main@%sm15_0 (store main@%sm17_0 main@%_29_0 0)))
                (=> main@_23_0
                    (= main@%_30_0 (< main@%.02.i524_0 main@%loop.bound2_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_23_0))
                (=> (and main@.thread_0 main@_23_0) (not main@%_30_0))
                (=> main@.thread_0 (= main@%_31_0 (< main@%_34_0 20)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| main@_32_0)
                (=> main@.preheader1_0
                    (or |tuple(main@_32_0, main@.preheader1_0)|
                        (and main@.preheader1_0 main@.thread_0)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| (not main@%_40_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_0 main@%sm17_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_0 main@%sm16_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_0 main@%shadow.mem.8.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_0 main@%_34_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_0 main@%_39_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_0 main@%_38_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_0 main@%_36_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_1 main@%sm15_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%sm14_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_1 main@%sm13_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_1 main@%sm12_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_1 main@%_26_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_1 false))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_1 main@%_31_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_1 20))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_2 main@%_18_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_2 main@%_19_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_2 main@%_20_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_2 main@%.13.i10_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_2 main@%_18_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_2 main@%_19_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_2 main@%_20_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_2 main@%.13.i10_1))
                (=> main@.preheader1_0 (= main@%_21_0 (> main@%.13.i10_2 19)))
                (=> main@.preheader1_0
                    (= main@%_22_0 (ite main@%_20_2 main@%_21_0 false)))
                (=> main@.lr.ph4_0 (and main@.lr.ph4_0 main@.preheader1_0))
                (=> (and main@.lr.ph4_0 main@.preheader1_0) main@%_22_0)
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.3_0 main@%shadow.mem.8.0_2))
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.3_0 main@%shadow.mem.0.0_2))
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%.1.i3_0 main@%_18_2))
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.3_1 main@%shadow.mem.8.3_0))
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.3_1 main@%shadow.mem.0.3_0))
                (=> (and main@.lr.ph4_0 main@.preheader1_0)
                    (= main@%.1.i3_1 main@%.1.i3_0))
                main@.lr.ph4_0)))
  (=> a!7
      (main@.lr.ph4 @d_1_0
                    @d_2_0
                    @b_2_0
                    main@%loop.bound_0
                    main@%_19_2
                    main@%shadow.mem.12.0_2
                    main@%shadow.mem.4.0_2
                    main@%.13.i10_2
                    @b_1_0
                    main@%.1.i3_1
                    main@%shadow.mem.0.3_1
                    main@%shadow.mem.8.3_1
                    main@%loop.bound1_0)))))
(rule (let ((a!1 (= main@%_35_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_33_0 4))))
      (a!2 (= main@%_37_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!3 (=> main@_23_0 (= main@%_24_0 (+ @b_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!4 (=> main@_23_0 (= main@%_25_0 (+ @d_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!5 (= main@%_27_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!6 (= main@%_29_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_28_0 4)))))
(let ((a!7 (and (main@_32 @d_1_0
                          @d_2_0
                          @b_2_0
                          main@%loop.bound_0
                          @b_1_0
                          main@%loop.bound1_0
                          main@%_34_0
                          main@%shadow.mem.0.1_0
                          main@%shadow.mem.8.1_0
                          main@%.02.i524_0
                          main@%loop.bound2_0
                          main@%shadow.mem.12.1_0
                          main@%shadow.mem.4.1_0
                          main@%_33_0
                          main@%.01.i623_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_35_0 0))
                (> @b_2_0 0)
                (= main@%sm16_0 (store main@%shadow.mem.4.1_0 main@%_35_0 0))
                (= main@%_36_0 (+ main@%.02.i524_0 2))
                a!2
                (or (<= @d_2_0 0) (> main@%_37_0 0))
                (> @d_2_0 0)
                (= main@%sm17_0 (store main@%shadow.mem.12.1_0 main@%_37_0 0))
                (= main@%_38_0 (< main@%.01.i623_0 20))
                (= main@%_39_0 (not (= main@%.02.i524_0 18)))
                (= main@%_40_0 (ite main@%_38_0 main@%_39_0 false))
                (=> main@_23_0 (and main@_23_0 main@_32_0))
                (=> (and main@_23_0 main@_32_0) main@%_40_0)
                a!3
                (=> main@_23_0 (or (<= @b_1_0 0) (> main@%_24_0 0)))
                (=> main@_23_0 (> @b_1_0 0))
                (=> main@_23_0
                    (= main@%sm12_0
                       (store main@%shadow.mem.0.1_0 main@%_24_0 0)))
                a!4
                (=> main@_23_0 (or (<= @d_1_0 0) (> main@%_25_0 0)))
                (=> main@_23_0 (> @d_1_0 0))
                (=> main@_23_0
                    (= main@%sm13_0
                       (store main@%shadow.mem.8.1_0 main@%_25_0 0)))
                (=> main@_23_0 (= main@%_26_0 (+ main@%_34_0 1)))
                (=> main@_23_0 a!5)
                (=> main@_23_0 (or (<= @b_2_0 0) (> main@%_27_0 0)))
                (=> main@_23_0 (> @b_2_0 0))
                (=> main@_23_0
                    (= main@%sm14_0 (store main@%sm16_0 main@%_27_0 0)))
                (=> main@_23_0 (= main@%_28_0 (+ main@%.02.i524_0 3)))
                (=> main@_23_0 a!6)
                (=> main@_23_0 (or (<= @d_2_0 0) (> main@%_29_0 0)))
                (=> main@_23_0 (> @d_2_0 0))
                (=> main@_23_0
                    (= main@%sm15_0 (store main@%sm17_0 main@%_29_0 0)))
                (=> main@_23_0
                    (= main@%_30_0 (< main@%.02.i524_0 main@%loop.bound2_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_23_0))
                (=> (and main@.thread_0 main@_23_0) (not main@%_30_0))
                (=> main@.thread_0 (= main@%_31_0 (< main@%_34_0 20)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| main@_32_0)
                (=> main@.preheader1_0
                    (or |tuple(main@_32_0, main@.preheader1_0)|
                        (and main@.preheader1_0 main@.thread_0)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| (not main@%_40_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_0 main@%sm17_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_0 main@%sm16_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_0 main@%shadow.mem.8.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_0 main@%_34_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_0 main@%_39_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_0 main@%_38_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_0 main@%_36_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_1 main@%sm15_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%sm14_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_1 main@%sm13_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_1 main@%sm12_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_1 main@%_26_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_1 false))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_1 main@%_31_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_1 20))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_2 main@%_18_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_2 main@%_19_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_2 main@%_20_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_2 main@%.13.i10_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_2 main@%_18_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_2 main@%_19_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_2 main@%_20_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_2 main@%.13.i10_1))
                (=> main@.preheader1_0 (= main@%_21_0 (> main@%.13.i10_2 19)))
                (=> main@.preheader1_0
                    (= main@%_22_0 (ite main@%_20_2 main@%_21_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_22_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.2_0 main@%shadow.mem.8.0_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.2_0 main@%shadow.mem.0.0_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.1.i.lcssa_0 main@%_18_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.2_1 main@%shadow.mem.8.2_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_41_0 (> main@%.1.i.lcssa_1 20)))
                (=> main@.preheader_0
                    (= main@%_42_0 (ite main@%_41_0 main@%_19_2 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_42_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.12.2_0 main@%shadow.mem.12.0_2))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.0_2))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i2.us_0 main@%.13.i10_2))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.12.2_1 main@%shadow.mem.12.2_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i2.us_1 main@%.2.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!7
      (main@.lr.ph.split.us
        @d_1_0
        main@%shadow.mem.8.2_1
        @d_2_0
        @b_2_0
        main@%.2.i2.us_1
        main@%shadow.mem.4.2_1
        main@%shadow.mem.12.2_1
        main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_35_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_33_0 4))))
      (a!2 (= main@%_37_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!3 (=> main@_23_0 (= main@%_24_0 (+ @b_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!4 (=> main@_23_0 (= main@%_25_0 (+ @d_1_0 (* 0 84) (* main@%_34_0 4)))))
      (a!5 (= main@%_27_0 (+ (+ @b_2_0 (* 0 84)) (* main@%_36_0 4))))
      (a!6 (= main@%_29_0 (+ (+ @d_2_0 (* 0 84)) (* main@%_28_0 4))))
      (a!7 (= main@%_51_0 (+ (+ @b_2_0 (* 0 84)) (* 20 4)))))
(let ((a!8 (and (main@_32 @d_1_0
                          @d_2_0
                          @b_2_0
                          main@%loop.bound_0
                          @b_1_0
                          main@%loop.bound1_0
                          main@%_34_0
                          main@%shadow.mem.0.1_0
                          main@%shadow.mem.8.1_0
                          main@%.02.i524_0
                          main@%loop.bound2_0
                          main@%shadow.mem.12.1_0
                          main@%shadow.mem.4.1_0
                          main@%_33_0
                          main@%.01.i623_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_35_0 0))
                (> @b_2_0 0)
                (= main@%sm16_0 (store main@%shadow.mem.4.1_0 main@%_35_0 0))
                (= main@%_36_0 (+ main@%.02.i524_0 2))
                a!2
                (or (<= @d_2_0 0) (> main@%_37_0 0))
                (> @d_2_0 0)
                (= main@%sm17_0 (store main@%shadow.mem.12.1_0 main@%_37_0 0))
                (= main@%_38_0 (< main@%.01.i623_0 20))
                (= main@%_39_0 (not (= main@%.02.i524_0 18)))
                (= main@%_40_0 (ite main@%_38_0 main@%_39_0 false))
                (=> main@_23_0 (and main@_23_0 main@_32_0))
                (=> (and main@_23_0 main@_32_0) main@%_40_0)
                a!3
                (=> main@_23_0 (or (<= @b_1_0 0) (> main@%_24_0 0)))
                (=> main@_23_0 (> @b_1_0 0))
                (=> main@_23_0
                    (= main@%sm12_0
                       (store main@%shadow.mem.0.1_0 main@%_24_0 0)))
                a!4
                (=> main@_23_0 (or (<= @d_1_0 0) (> main@%_25_0 0)))
                (=> main@_23_0 (> @d_1_0 0))
                (=> main@_23_0
                    (= main@%sm13_0
                       (store main@%shadow.mem.8.1_0 main@%_25_0 0)))
                (=> main@_23_0 (= main@%_26_0 (+ main@%_34_0 1)))
                (=> main@_23_0 a!5)
                (=> main@_23_0 (or (<= @b_2_0 0) (> main@%_27_0 0)))
                (=> main@_23_0 (> @b_2_0 0))
                (=> main@_23_0
                    (= main@%sm14_0 (store main@%sm16_0 main@%_27_0 0)))
                (=> main@_23_0 (= main@%_28_0 (+ main@%.02.i524_0 3)))
                (=> main@_23_0 a!6)
                (=> main@_23_0 (or (<= @d_2_0 0) (> main@%_29_0 0)))
                (=> main@_23_0 (> @d_2_0 0))
                (=> main@_23_0
                    (= main@%sm15_0 (store main@%sm17_0 main@%_29_0 0)))
                (=> main@_23_0
                    (= main@%_30_0 (< main@%.02.i524_0 main@%loop.bound2_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_23_0))
                (=> (and main@.thread_0 main@_23_0) (not main@%_30_0))
                (=> main@.thread_0 (= main@%_31_0 (< main@%_34_0 20)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| main@_32_0)
                (=> main@.preheader1_0
                    (or |tuple(main@_32_0, main@.preheader1_0)|
                        (and main@.preheader1_0 main@.thread_0)))
                (=> |tuple(main@_32_0, main@.preheader1_0)| (not main@%_40_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_0 main@%sm17_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_0 main@%sm16_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_0 main@%shadow.mem.8.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_0 main@%shadow.mem.0.1_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_0 main@%_34_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_0 main@%_39_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_0 main@%_38_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_0 main@%_36_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_1 main@%sm15_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%sm14_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_1 main@%sm13_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_1 main@%sm12_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_1 main@%_26_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_1 false))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_1 main@%_31_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_1 20))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_18_2 main@%_18_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_19_2 main@%_19_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%_20_2 main@%_20_0))
                (=> |tuple(main@_32_0, main@.preheader1_0)|
                    (= main@%.13.i10_2 main@%.13.i10_0))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_18_2 main@%_18_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_19_2 main@%_19_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%_20_2 main@%_20_1))
                (=> (and main@.preheader1_0 main@.thread_0)
                    (= main@%.13.i10_2 main@%.13.i10_1))
                (=> main@.preheader1_0 (= main@%_21_0 (> main@%.13.i10_2 19)))
                (=> main@.preheader1_0
                    (= main@%_22_0 (ite main@%_20_2 main@%_21_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (not main@%_22_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.2_0 main@%shadow.mem.8.0_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.2_0 main@%shadow.mem.0.0_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.1.i.lcssa_0 main@%_18_2))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.8.2_1 main@%shadow.mem.8.2_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_41_0 (> main@%.1.i.lcssa_1 20)))
                (=> main@.preheader_0
                    (= main@%_42_0 (ite main@%_41_0 main@%_19_2 false)))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (not main@%_42_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.12.3_0 main@%shadow.mem.12.0_2))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.3_0 main@%shadow.mem.4.0_2))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.12.3_1 main@%shadow.mem.12.3_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.3_0))
                (=> main@._crit_edge_0 a!7)
                (=> main@._crit_edge_0 (or (<= @b_2_0 0) (> main@%_51_0 0)))
                (=> main@._crit_edge_0 (> @b_2_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm22_0
                       (store main@%shadow.mem.4.3_1 main@%_51_0 0)))
                (=> main@_52_0 (and main@_52_0 main@._crit_edge_0))
                (=> (and main@_52_0 main@._crit_edge_0) (= main@%.04.i_0 1))
                (=> (and main@_52_0 main@._crit_edge_0)
                    (= main@%.04.i_1 main@%.04.i_0))
                main@_52_0)))
  (=> a!8
      (main@_52 main@%.04.i_1
                @d_1_0
                main@%shadow.mem.8.2_1
                @d_2_0
                main@%shadow.mem.12.3_1)))))
(rule (let ((a!1 (and (main@.lr.ph4 @d_1_0
                              @d_2_0
                              @b_2_0
                              main@%loop.bound_0
                              main@%_19_0
                              main@%shadow.mem.12.0_0
                              main@%shadow.mem.4.0_0
                              main@%.13.i10_0
                              @b_1_0
                              main@%.1.i3_0
                              main@%shadow.mem.0.3_0
                              main@%shadow.mem.8.3_0
                              main@%loop.bound1_0)
                true
                (= main@%_47_0 (+ @b_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @b_1_0 0) (> main@%_47_0 0))
                (> @b_1_0 0)
                (= main@%sm20_0 (store main@%shadow.mem.0.3_0 main@%_47_0 0))
                (= main@%_48_0 (+ @d_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @d_1_0 0) (> main@%_48_0 0))
                (> @d_1_0 0)
                (= main@%sm21_0 (store main@%shadow.mem.8.3_0 main@%_48_0 0))
                (= main@%_49_0 (+ main@%.1.i3_0 1))
                (= main@%_50_0 (< main@%.1.i3_0 main@%loop.bound1_0))
                (=> main@.lr.ph4_1 (and main@.lr.ph4_1 main@.lr.ph4_0))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0) main@%_50_0)
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.3_1 main@%sm21_0))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.3_1 main@%sm20_0))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%.1.i3_1 main@%_49_0))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.3_2 main@%shadow.mem.8.3_1))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.3_2 main@%shadow.mem.0.3_1))
                (=> (and main@.lr.ph4_1 main@.lr.ph4_0)
                    (= main@%.1.i3_2 main@%.1.i3_1))
                main@.lr.ph4_1)))
  (=> a!1
      (main@.lr.ph4 @d_1_0
                    @d_2_0
                    @b_2_0
                    main@%loop.bound_0
                    main@%_19_0
                    main@%shadow.mem.12.0_0
                    main@%shadow.mem.4.0_0
                    main@%.13.i10_0
                    @b_1_0
                    main@%.1.i3_2
                    main@%shadow.mem.0.3_2
                    main@%shadow.mem.8.3_2
                    main@%loop.bound1_0))))
(rule (let ((a!1 (and (main@.lr.ph4 @d_1_0
                              @d_2_0
                              @b_2_0
                              main@%loop.bound_0
                              main@%_19_0
                              main@%shadow.mem.12.0_0
                              main@%shadow.mem.4.0_0
                              main@%.13.i10_0
                              @b_1_0
                              main@%.1.i3_0
                              main@%shadow.mem.0.3_0
                              main@%shadow.mem.8.3_0
                              main@%loop.bound1_0)
                true
                (= main@%_47_0 (+ @b_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @b_1_0 0) (> main@%_47_0 0))
                (> @b_1_0 0)
                (= main@%sm20_0 (store main@%shadow.mem.0.3_0 main@%_47_0 0))
                (= main@%_48_0 (+ @d_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @d_1_0 0) (> main@%_48_0 0))
                (> @d_1_0 0)
                (= main@%sm21_0 (store main@%shadow.mem.8.3_0 main@%_48_0 0))
                (= main@%_49_0 (+ main@%.1.i3_0 1))
                (= main@%_50_0 (< main@%.1.i3_0 main@%loop.bound1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph4_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0) (not main@%_50_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.2_0 main@%sm21_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.2_0 main@%sm20_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%.1.i.lcssa_0 main@%_49_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.2_1 main@%shadow.mem.8.2_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_41_0 (> main@%.1.i.lcssa_1 20)))
                (=> main@.preheader_0
                    (= main@%_42_0 (ite main@%_41_0 main@%_19_0 false)))
                (=> main@.lr.ph.split.us_0
                    (and main@.lr.ph.split.us_0 main@.preheader_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0) main@%_42_0)
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.12.2_0 main@%shadow.mem.12.0_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.0_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i2.us_0 main@%.13.i10_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.12.2_1 main@%shadow.mem.12.2_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@.lr.ph.split.us_0 main@.preheader_0)
                    (= main@%.2.i2.us_1 main@%.2.i2.us_0))
                main@.lr.ph.split.us_0)))
  (=> a!1
      (main@.lr.ph.split.us
        @d_1_0
        main@%shadow.mem.8.2_1
        @d_2_0
        @b_2_0
        main@%.2.i2.us_1
        main@%shadow.mem.4.2_1
        main@%shadow.mem.12.2_1
        main@%loop.bound_0))))
(rule (let ((a!1 (=> main@._crit_edge_0 (= main@%_51_0 (+ @b_2_0 (* 0 84) (* 20 4))))))
(let ((a!2 (and (main@.lr.ph4 @d_1_0
                              @d_2_0
                              @b_2_0
                              main@%loop.bound_0
                              main@%_19_0
                              main@%shadow.mem.12.0_0
                              main@%shadow.mem.4.0_0
                              main@%.13.i10_0
                              @b_1_0
                              main@%.1.i3_0
                              main@%shadow.mem.0.3_0
                              main@%shadow.mem.8.3_0
                              main@%loop.bound1_0)
                true
                (= main@%_47_0 (+ @b_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @b_1_0 0) (> main@%_47_0 0))
                (> @b_1_0 0)
                (= main@%sm20_0 (store main@%shadow.mem.0.3_0 main@%_47_0 0))
                (= main@%_48_0 (+ @d_1_0 (* 0 84) (* main@%.1.i3_0 4)))
                (or (<= @d_1_0 0) (> main@%_48_0 0))
                (> @d_1_0 0)
                (= main@%sm21_0 (store main@%shadow.mem.8.3_0 main@%_48_0 0))
                (= main@%_49_0 (+ main@%.1.i3_0 1))
                (= main@%_50_0 (< main@%.1.i3_0 main@%loop.bound1_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@.lr.ph4_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0) (not main@%_50_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.2_0 main@%sm21_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.2_0 main@%sm20_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%.1.i.lcssa_0 main@%_49_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.8.2_1 main@%shadow.mem.8.2_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.preheader_0 main@.lr.ph4_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_41_0 (> main@%.1.i.lcssa_1 20)))
                (=> main@.preheader_0
                    (= main@%_42_0 (ite main@%_41_0 main@%_19_0 false)))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (not main@%_42_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.12.3_0 main@%shadow.mem.12.0_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.3_0 main@%shadow.mem.4.0_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.12.3_1 main@%shadow.mem.12.3_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.3_0))
                a!1
                (=> main@._crit_edge_0 (or (<= @b_2_0 0) (> main@%_51_0 0)))
                (=> main@._crit_edge_0 (> @b_2_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm22_0
                       (store main@%shadow.mem.4.3_1 main@%_51_0 0)))
                (=> main@_52_0 (and main@_52_0 main@._crit_edge_0))
                (=> (and main@_52_0 main@._crit_edge_0) (= main@%.04.i_0 1))
                (=> (and main@_52_0 main@._crit_edge_0)
                    (= main@%.04.i_1 main@%.04.i_0))
                main@_52_0)))
  (=> a!2
      (main@_52 main@%.04.i_1
                @d_1_0
                main@%shadow.mem.8.2_1
                @d_2_0
                main@%shadow.mem.12.3_1)))))
(rule (let ((a!1 (and (main@.lr.ph.split.us
                  @d_1_0
                  main@%shadow.mem.8.2_0
                  @d_2_0
                  @b_2_0
                  main@%.2.i2.us_0
                  main@%shadow.mem.4.2_0
                  main@%shadow.mem.12.2_0
                  main@%loop.bound_0)
                true
                (= main@%_43_0 (+ @b_2_0 (* 0 84) (* main@%.2.i2.us_0 4)))
                (or (<= @b_2_0 0) (> main@%_43_0 0))
                (> @b_2_0 0)
                (= main@%sm18_0 (store main@%shadow.mem.4.2_0 main@%_43_0 0))
                (= main@%_44_0 (+ main@%.2.i2.us_0 1))
                (= main@%_45_0 (+ @d_2_0 (* 0 84) (* main@%_44_0 4)))
                (or (<= @d_2_0 0) (> main@%_45_0 0))
                (> @d_2_0 0)
                (= main@%sm19_0 (store main@%shadow.mem.12.2_0 main@%_45_0 0))
                (= main@%_46_0 (< main@%.2.i2.us_0 main@%loop.bound_0))
                (=> main@.lr.ph.split.us_1
                    (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    main@%_46_0)
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.12.2_1 main@%sm19_0))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.4.2_1 main@%sm18_0))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%.2.i2.us_1 main@%_44_0))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.12.2_2 main@%shadow.mem.12.2_1))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> (and main@.lr.ph.split.us_1 main@.lr.ph.split.us_0)
                    (= main@%.2.i2.us_2 main@%.2.i2.us_1))
                main@.lr.ph.split.us_1)))
  (=> a!1
      (main@.lr.ph.split.us
        @d_1_0
        main@%shadow.mem.8.2_0
        @d_2_0
        @b_2_0
        main@%.2.i2.us_2
        main@%shadow.mem.4.2_2
        main@%shadow.mem.12.2_2
        main@%loop.bound_0))))
(rule (let ((a!1 (= main@%_43_0 (+ (+ @b_2_0 (* 0 84)) (* main@%.2.i2.us_0 4))))
      (a!2 (= main@%_51_0 (+ (+ @b_2_0 (* 0 84)) (* 20 4)))))
(let ((a!3 (and (main@.lr.ph.split.us
                  @d_1_0
                  main@%shadow.mem.8.2_0
                  @d_2_0
                  @b_2_0
                  main@%.2.i2.us_0
                  main@%shadow.mem.4.2_0
                  main@%shadow.mem.12.2_0
                  main@%loop.bound_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_43_0 0))
                (> @b_2_0 0)
                (= main@%sm18_0 (store main@%shadow.mem.4.2_0 main@%_43_0 0))
                (= main@%_44_0 (+ main@%.2.i2.us_0 1))
                (= main@%_45_0 (+ @d_2_0 (* 0 84) (* main@%_44_0 4)))
                (or (<= @d_2_0 0) (> main@%_45_0 0))
                (> @d_2_0 0)
                (= main@%sm19_0 (store main@%shadow.mem.12.2_0 main@%_45_0 0))
                (= main@%_46_0 (< main@%.2.i2.us_0 main@%loop.bound_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.lr.ph.split.us_0))
                (=> (and main@._crit_edge_0 main@.lr.ph.split.us_0)
                    (not main@%_46_0))
                (=> (and main@._crit_edge_0 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.12.3_0 main@%sm19_0))
                (=> (and main@._crit_edge_0 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.4.3_0 main@%sm18_0))
                (=> (and main@._crit_edge_0 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.12.3_1 main@%shadow.mem.12.3_0))
                (=> (and main@._crit_edge_0 main@.lr.ph.split.us_0)
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.3_0))
                (=> main@._crit_edge_0 a!2)
                (=> main@._crit_edge_0 (or (<= @b_2_0 0) (> main@%_51_0 0)))
                (=> main@._crit_edge_0 (> @b_2_0 0))
                (=> main@._crit_edge_0
                    (= main@%sm22_0
                       (store main@%shadow.mem.4.3_1 main@%_51_0 0)))
                (=> main@_52_0 (and main@_52_0 main@._crit_edge_0))
                (=> (and main@_52_0 main@._crit_edge_0) (= main@%.04.i_0 1))
                (=> (and main@_52_0 main@._crit_edge_0)
                    (= main@%.04.i_1 main@%.04.i_0))
                main@_52_0)))
  (=> a!3
      (main@_52 main@%.04.i_1
                @d_1_0
                main@%shadow.mem.8.2_0
                @d_2_0
                main@%shadow.mem.12.3_1)))))
(rule (let ((a!1 (and (main@_52 main@%.04.i_0
                          @d_1_0
                          main@%shadow.mem.8.2_0
                          @d_2_0
                          main@%shadow.mem.12.3_0)
                true
                (= main@%_53_0 (< main@%.04.i_0 20))
                main@%_53_0
                (= main@%_54_0 (+ @d_1_0 (* 0 84) (* main@%.04.i_0 4)))
                (or (<= @d_1_0 0) (> main@%_54_0 0))
                (> @d_1_0 0)
                (= main@%_55_0 (select main@%shadow.mem.8.2_0 main@%_54_0))
                (= main@%_56_0 (+ @d_2_0 (* 0 84) (* main@%.04.i_0 4)))
                (or (<= @d_2_0 0) (> main@%_56_0 0))
                (> @d_2_0 0)
                (= main@%_57_0 (select main@%shadow.mem.12.3_0 main@%_56_0))
                (= main@%_58_0 (= main@%_55_0 main@%_57_0))
                (= main@%_59_0 (+ main@%.04.i_0 1))
                (=> main@_52_1 (and main@_52_1 main@_52_0))
                (=> (and main@_52_1 main@_52_0) main@%_58_0)
                (=> (and main@_52_1 main@_52_0) (= main@%.04.i_1 main@%_59_0))
                (=> (and main@_52_1 main@_52_0) (= main@%.04.i_2 main@%.04.i_1))
                main@_52_1)))
  (=> a!1
      (main@_52 main@%.04.i_2
                @d_1_0
                main@%shadow.mem.8.2_0
                @d_2_0
                main@%shadow.mem.12.3_0))))
(rule (let ((a!1 (and (main@_52 main@%.04.i_0
                          @d_1_0
                          main@%shadow.mem.8.2_0
                          @d_2_0
                          main@%shadow.mem.12.3_0)
                true
                (= main@%_53_0 (< main@%.04.i_0 20))
                main@%_53_0
                (= main@%_54_0 (+ @d_1_0 (* 0 84) (* main@%.04.i_0 4)))
                (or (<= @d_1_0 0) (> main@%_54_0 0))
                (> @d_1_0 0)
                (= main@%_55_0 (select main@%shadow.mem.8.2_0 main@%_54_0))
                (= main@%_56_0 (+ @d_2_0 (* 0 84) (* main@%.04.i_0 4)))
                (or (<= @d_2_0 0) (> main@%_56_0 0))
                (> @d_2_0 0)
                (= main@%_57_0 (select main@%shadow.mem.12.3_0 main@%_56_0))
                (= main@%_58_0 (= main@%_55_0 main@%_57_0))
                (= main@%_59_0 (+ main@%.04.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_52_0))
                (=> (and main@verifier.error_0 main@_52_0) (not main@%_58_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

