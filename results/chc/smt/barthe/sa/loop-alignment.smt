(set-info :original "./results/chc/bytecode/barthe/sa/loop-alignment.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) (Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int (Array Int Int) Int (Array Int Int) Bool Int ))
(declare-rel main@_8 (Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int (Array Int Int) Int (Array Int Int) Bool Int Int ))
(declare-rel main@_13 (Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int (Array Int Int) (Array Int Int) Int ))
(declare-rel main@_20 (Int Int (Array Int Int) Int Int (Array Int Int) (Array Int Int) Int Int ))
(declare-rel main@.preheader (Int Int (Array Int Int) Int (Array Int Int) ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_26_0 Bool )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Int )
(declare-var main@%_29_0 Int )
(declare-var main@%_30_0 Int )
(declare-var main@%_31_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%.03.i_2 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_2 (Array Int Int) )
(declare-var main@%_21_2 Int )
(declare-var main@%.02.i1_2 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%shadow.mem.4.0_2 (Array Int Int) )
(declare-var main@%shadow.mem.12.0_2 (Array Int Int) )
(declare-var main@%.01.i2_2 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%.0.i3_2 Int )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@%sm14_0 (Array Int Int) )
(declare-var main@%sm15_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@entry_0 Bool )
(declare-var @b_1_0 Int )
(declare-var @b_2_0 Int )
(declare-var @d_2_0 Int )
(declare-var @d_1_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm3_0 (Array Int Int) )
(declare-var main@%sm4_0 (Array Int Int) )
(declare-var main@%sm5_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_8_0 Bool )
(declare-var main@%.0.i3_0 Int )
(declare-var main@%.0.i3_1 Int )
(declare-var main@%_9_0 Int )
(declare-var main@_8_1 Bool )
(declare-var main@_11_0 Bool )
(declare-var main@%sm6_0 (Array Int Int) )
(declare-var main@_13_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.12.0_0 (Array Int Int) )
(declare-var main@%.01.i2_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.12.0_1 (Array Int Int) )
(declare-var main@%.01.i2_1 Int )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%_15_0 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@_13_1 Bool )
(declare-var main@_18_0 Bool )
(declare-var main@_20_0 Bool )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_0 (Array Int Int) )
(declare-var main@%_21_0 Int )
(declare-var main@%.02.i1_0 Int )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%shadow.mem.8.0_1 (Array Int Int) )
(declare-var main@%_21_1 Int )
(declare-var main@%.02.i1_1 Int )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@%_24_0 Int )
(declare-var main@_20_1 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%.03.i_0 Int )
(declare-var main@%.03.i_1 Int )
(declare-var main@%_32_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm12_0 main@%sm13_0 main@%sm14_0 main@%sm15_0))
(rule (let ((a!1 (and (main@entry main@%sm12_0 main@%sm13_0 main@%sm14_0 main@%sm15_0)
                true
                (= main@%sm_0 main@%sm15_0)
                (= main@%sm3_0 main@%sm13_0)
                (= main@%sm4_0 main@%sm14_0)
                (= main@%sm5_0 main@%sm12_0)
                (= main@%_0_0 (= main@%loop.bound_0 20))
                main@%_0_0
                (= main@%_1_0 (= main@%loop.bound1_0 19))
                main@%_1_0
                (= main@%_2_0 (= main@%loop.bound2_0 19))
                main@%_2_0
                (= main@%_3_0 (+ @b_1_0 (* 0 84) (* 0 4)))
                (or (<= @b_1_0 0) (> main@%_3_0 0))
                (= main@%_4_0 (select main@%sm_0 main@%_3_0))
                (= main@%_5_0 (+ @b_2_0 (* 0 84) (* 0 4)))
                (or (<= @b_2_0 0) (> main@%_5_0 0))
                (= main@%_6_0 (select main@%sm3_0 main@%_5_0))
                (= main@%_7_0 (= main@%_4_0 main@%_6_0))
                (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
                main@empty.loop_0)))
  (=> a!1
      (main@empty.loop @d_1_0
                       @d_2_0
                       @b_1_0
                       main@%loop.bound_0
                       @b_2_0
                       main@%sm_0
                       main@%sm4_0
                       main@%_4_0
                       main@%loop.bound1_0
                       main@%sm5_0
                       main@%_6_0
                       main@%sm3_0
                       main@%_7_0
                       main@%loop.bound2_0))))
(rule (let ((a!1 (main@empty.loop @d_1_0
                            @d_2_0
                            @b_1_0
                            main@%loop.bound_0
                            @b_2_0
                            main@%sm_0
                            main@%sm4_0
                            main@%_4_0
                            main@%loop.bound1_0
                            main@%sm5_0
                            main@%_6_0
                            main@%sm3_0
                            main@%_7_0
                            main@%loop.bound2_0)))
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
                          @b_1_0
                          main@%loop.bound_0
                          @b_2_0
                          main@%sm_0
                          main@%sm4_0
                          main@%_4_0
                          main@%loop.bound1_0
                          main@%sm5_0
                          main@%_6_0
                          main@%sm3_0
                          main@%_7_0
                          main@%loop.bound2_0)
         true
         (=> main@_8_0 (and main@_8_0 main@empty.loop_0))
         (=> (and main@_8_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_8_0 main@empty.loop_0) (= main@%.0.i3_0 0))
         (=> (and main@_8_0 main@empty.loop_0) (= main@%.0.i3_1 main@%.0.i3_0))
         main@_8_0)
    (main@_8 @d_1_0
             @d_2_0
             @b_1_0
             main@%loop.bound_0
             @b_2_0
             main@%sm_0
             main@%sm4_0
             main@%_4_0
             main@%loop.bound1_0
             main@%sm5_0
             main@%_6_0
             main@%sm3_0
             main@%_7_0
             main@%.0.i3_1
             main@%loop.bound2_0)))
(rule (=> (and (main@_8 @d_1_0
                  @d_2_0
                  @b_1_0
                  main@%loop.bound_0
                  @b_2_0
                  main@%sm_0
                  main@%sm4_0
                  main@%_4_0
                  main@%loop.bound1_0
                  main@%sm5_0
                  main@%_6_0
                  main@%sm3_0
                  main@%_7_0
                  main@%.0.i3_0
                  main@%loop.bound2_0)
         true
         main@%_7_0
         (= main@%_9_0 (+ main@%.0.i3_0 1))
         (= main@%_10_0 (< main@%.0.i3_0 main@%loop.bound2_0))
         (=> main@_8_1 (and main@_8_1 main@_8_0))
         (=> (and main@_8_1 main@_8_0) main@%_10_0)
         (=> (and main@_8_1 main@_8_0) (= main@%.0.i3_1 main@%_9_0))
         (=> (and main@_8_1 main@_8_0) (= main@%.0.i3_2 main@%.0.i3_1))
         main@_8_1)
    (main@_8 @d_1_0
             @d_2_0
             @b_1_0
             main@%loop.bound_0
             @b_2_0
             main@%sm_0
             main@%sm4_0
             main@%_4_0
             main@%loop.bound1_0
             main@%sm5_0
             main@%_6_0
             main@%sm3_0
             main@%_7_0
             main@%.0.i3_2
             main@%loop.bound2_0)))
(rule (let ((a!1 (=> main@_11_0 (= main@%_12_0 (+ @d_2_0 (* 0 84) (* 1 4))))))
(let ((a!2 (and (main@_8 @d_1_0
                         @d_2_0
                         @b_1_0
                         main@%loop.bound_0
                         @b_2_0
                         main@%sm_0
                         main@%sm4_0
                         main@%_4_0
                         main@%loop.bound1_0
                         main@%sm5_0
                         main@%_6_0
                         main@%sm3_0
                         main@%_7_0
                         main@%.0.i3_0
                         main@%loop.bound2_0)
                true
                main@%_7_0
                (= main@%_9_0 (+ main@%.0.i3_0 1))
                (= main@%_10_0 (< main@%.0.i3_0 main@%loop.bound2_0))
                (=> main@_11_0 (and main@_11_0 main@_8_0))
                (=> (and main@_11_0 main@_8_0) (not main@%_10_0))
                a!1
                (=> main@_11_0 (or (<= @d_2_0 0) (> main@%_12_0 0)))
                (=> main@_11_0 (> @d_2_0 0))
                (=> main@_11_0
                    (= main@%sm6_0 (store main@%sm5_0 main@%_12_0 main@%_6_0)))
                (=> main@_13_0 (and main@_13_0 main@_11_0))
                (=> (and main@_13_0 main@_11_0)
                    (= main@%shadow.mem.4.0_0 main@%sm3_0))
                (=> (and main@_13_0 main@_11_0)
                    (= main@%shadow.mem.12.0_0 main@%sm6_0))
                (=> (and main@_13_0 main@_11_0) (= main@%.01.i2_0 1))
                (=> (and main@_13_0 main@_11_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@_13_0 main@_11_0)
                    (= main@%shadow.mem.12.0_1 main@%shadow.mem.12.0_0))
                (=> (and main@_13_0 main@_11_0)
                    (= main@%.01.i2_1 main@%.01.i2_0))
                main@_13_0)))
  (=> a!2
      (main@_13 @d_1_0
                @d_2_0
                @b_1_0
                main@%loop.bound_0
                @b_2_0
                main@%sm_0
                main@%sm4_0
                main@%_4_0
                main@%.01.i2_1
                main@%shadow.mem.4.0_1
                main@%shadow.mem.12.0_1
                main@%loop.bound1_0)))))
(rule (let ((a!1 (and (main@_13 @d_1_0
                          @d_2_0
                          @b_1_0
                          main@%loop.bound_0
                          @b_2_0
                          main@%sm_0
                          main@%sm4_0
                          main@%_4_0
                          main@%.01.i2_0
                          main@%shadow.mem.4.0_0
                          main@%shadow.mem.12.0_0
                          main@%loop.bound1_0)
                true
                (= main@%_14_0 (+ @b_2_0 (* 0 84) (* main@%.01.i2_0 4)))
                (or (<= @b_2_0 0) (> main@%_14_0 0))
                (> @b_2_0 0)
                (= main@%sm7_0 (store main@%shadow.mem.4.0_0 main@%_14_0 0))
                (= main@%_15_0 (+ main@%.01.i2_0 1))
                (= main@%_16_0 (+ @d_2_0 (* 0 84) (* main@%_15_0 4)))
                (or (<= @d_2_0 0) (> main@%_16_0 0))
                (> @d_2_0 0)
                (= main@%sm8_0 (store main@%shadow.mem.12.0_0 main@%_16_0 0))
                (= main@%_17_0 (< main@%.01.i2_0 main@%loop.bound1_0))
                (=> main@_13_1 (and main@_13_1 main@_13_0))
                (=> (and main@_13_1 main@_13_0) main@%_17_0)
                (=> (and main@_13_1 main@_13_0)
                    (= main@%shadow.mem.4.0_1 main@%sm7_0))
                (=> (and main@_13_1 main@_13_0)
                    (= main@%shadow.mem.12.0_1 main@%sm8_0))
                (=> (and main@_13_1 main@_13_0) (= main@%.01.i2_1 main@%_15_0))
                (=> (and main@_13_1 main@_13_0)
                    (= main@%shadow.mem.4.0_2 main@%shadow.mem.4.0_1))
                (=> (and main@_13_1 main@_13_0)
                    (= main@%shadow.mem.12.0_2 main@%shadow.mem.12.0_1))
                (=> (and main@_13_1 main@_13_0)
                    (= main@%.01.i2_2 main@%.01.i2_1))
                main@_13_1)))
  (=> a!1
      (main@_13 @d_1_0
                @d_2_0
                @b_1_0
                main@%loop.bound_0
                @b_2_0
                main@%sm_0
                main@%sm4_0
                main@%_4_0
                main@%.01.i2_2
                main@%shadow.mem.4.0_2
                main@%shadow.mem.12.0_2
                main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_14_0 (+ (+ @b_2_0 (* 0 84)) (* main@%.01.i2_0 4))))
      (a!2 (= main@%_19_0 (+ (+ @b_2_0 (* 0 84)) (* 20 4)))))
(let ((a!3 (and (main@_13 @d_1_0
                          @d_2_0
                          @b_1_0
                          main@%loop.bound_0
                          @b_2_0
                          main@%sm_0
                          main@%sm4_0
                          main@%_4_0
                          main@%.01.i2_0
                          main@%shadow.mem.4.0_0
                          main@%shadow.mem.12.0_0
                          main@%loop.bound1_0)
                true
                a!1
                (or (<= @b_2_0 0) (> main@%_14_0 0))
                (> @b_2_0 0)
                (= main@%sm7_0 (store main@%shadow.mem.4.0_0 main@%_14_0 0))
                (= main@%_15_0 (+ main@%.01.i2_0 1))
                (= main@%_16_0 (+ @d_2_0 (* 0 84) (* main@%_15_0 4)))
                (or (<= @d_2_0 0) (> main@%_16_0 0))
                (> @d_2_0 0)
                (= main@%sm8_0 (store main@%shadow.mem.12.0_0 main@%_16_0 0))
                (= main@%_17_0 (< main@%.01.i2_0 main@%loop.bound1_0))
                (=> main@_18_0 (and main@_18_0 main@_13_0))
                (=> (and main@_18_0 main@_13_0) (not main@%_17_0))
                (=> main@_18_0 a!2)
                (=> main@_18_0 (or (<= @b_2_0 0) (> main@%_19_0 0)))
                (=> main@_18_0 (> @b_2_0 0))
                (=> main@_18_0
                    (= main@%sm9_0 (store main@%sm7_0 main@%_19_0 0)))
                (=> main@_20_0 (and main@_20_0 main@_18_0))
                (=> (and main@_20_0 main@_18_0)
                    (= main@%shadow.mem.0.0_0 main@%sm_0))
                (=> (and main@_20_0 main@_18_0)
                    (= main@%shadow.mem.8.0_0 main@%sm4_0))
                (=> (and main@_20_0 main@_18_0) (= main@%_21_0 main@%_4_0))
                (=> (and main@_20_0 main@_18_0) (= main@%.02.i1_0 1))
                (=> (and main@_20_0 main@_18_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@_20_0 main@_18_0)
                    (= main@%shadow.mem.8.0_1 main@%shadow.mem.8.0_0))
                (=> (and main@_20_0 main@_18_0) (= main@%_21_1 main@%_21_0))
                (=> (and main@_20_0 main@_18_0)
                    (= main@%.02.i1_1 main@%.02.i1_0))
                main@_20_0)))
  (=> a!3
      (main@_20 @d_1_0
                @d_2_0
                main@%sm8_0
                @b_1_0
                main@%.02.i1_1
                main@%shadow.mem.0.0_1
                main@%shadow.mem.8.0_1
                main@%_21_1
                main@%loop.bound_0)))))
(rule (let ((a!1 (and (main@_20 @d_1_0
                          @d_2_0
                          main@%sm8_0
                          @b_1_0
                          main@%.02.i1_0
                          main@%shadow.mem.0.0_0
                          main@%shadow.mem.8.0_0
                          main@%_21_0
                          main@%loop.bound_0)
                true
                (= main@%_22_0 (+ @b_1_0 (* 0 84) (* main@%.02.i1_0 4)))
                (or (<= @b_1_0 0) (> main@%_22_0 0))
                (> @b_1_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.0.0_0 main@%_22_0 0))
                (= main@%_23_0 (+ @d_1_0 (* 0 84) (* main@%.02.i1_0 4)))
                (or (<= @d_1_0 0) (> main@%_23_0 0))
                (> @d_1_0 0)
                (= main@%sm11_0
                   (store main@%shadow.mem.8.0_0 main@%_23_0 main@%_21_0))
                (= main@%_24_0 (+ main@%.02.i1_0 1))
                (= main@%_25_0 (< main@%.02.i1_0 main@%loop.bound_0))
                (=> main@_20_1 (and main@_20_1 main@_20_0))
                (=> (and main@_20_1 main@_20_0) main@%_25_0)
                (=> (and main@_20_1 main@_20_0)
                    (= main@%shadow.mem.0.0_1 main@%sm10_0))
                (=> (and main@_20_1 main@_20_0)
                    (= main@%shadow.mem.8.0_1 main@%sm11_0))
                (=> (and main@_20_1 main@_20_0) (= main@%_21_1 0))
                (=> (and main@_20_1 main@_20_0) (= main@%.02.i1_1 main@%_24_0))
                (=> (and main@_20_1 main@_20_0)
                    (= main@%shadow.mem.0.0_2 main@%shadow.mem.0.0_1))
                (=> (and main@_20_1 main@_20_0)
                    (= main@%shadow.mem.8.0_2 main@%shadow.mem.8.0_1))
                (=> (and main@_20_1 main@_20_0) (= main@%_21_2 main@%_21_1))
                (=> (and main@_20_1 main@_20_0)
                    (= main@%.02.i1_2 main@%.02.i1_1))
                main@_20_1)))
  (=> a!1
      (main@_20 @d_1_0
                @d_2_0
                main@%sm8_0
                @b_1_0
                main@%.02.i1_2
                main@%shadow.mem.0.0_2
                main@%shadow.mem.8.0_2
                main@%_21_2
                main@%loop.bound_0))))
(rule (let ((a!1 (and (main@_20 @d_1_0
                          @d_2_0
                          main@%sm8_0
                          @b_1_0
                          main@%.02.i1_0
                          main@%shadow.mem.0.0_0
                          main@%shadow.mem.8.0_0
                          main@%_21_0
                          main@%loop.bound_0)
                true
                (= main@%_22_0 (+ @b_1_0 (* 0 84) (* main@%.02.i1_0 4)))
                (or (<= @b_1_0 0) (> main@%_22_0 0))
                (> @b_1_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.0.0_0 main@%_22_0 0))
                (= main@%_23_0 (+ @d_1_0 (* 0 84) (* main@%.02.i1_0 4)))
                (or (<= @d_1_0 0) (> main@%_23_0 0))
                (> @d_1_0 0)
                (= main@%sm11_0
                   (store main@%shadow.mem.8.0_0 main@%_23_0 main@%_21_0))
                (= main@%_24_0 (+ main@%.02.i1_0 1))
                (= main@%_25_0 (< main@%.02.i1_0 main@%loop.bound_0))
                (=> main@.preheader_0 (and main@.preheader_0 main@_20_0))
                (=> (and main@.preheader_0 main@_20_0) (not main@%_25_0))
                (=> (and main@.preheader_0 main@_20_0) (= main@%.03.i_0 1))
                (=> (and main@.preheader_0 main@_20_0)
                    (= main@%.03.i_1 main@%.03.i_0))
                main@.preheader_0)))
  (=> a!1
      (main@.preheader main@%.03.i_1 @d_1_0 main@%sm11_0 @d_2_0 main@%sm8_0))))
(rule (let ((a!1 (and (main@.preheader main@%.03.i_0
                                 @d_1_0
                                 main@%sm11_0
                                 @d_2_0
                                 main@%sm8_0)
                true
                (= main@%_26_0 (< main@%.03.i_0 20))
                main@%_26_0
                (= main@%_27_0 (+ @d_1_0 (* 0 84) (* main@%.03.i_0 4)))
                (or (<= @d_1_0 0) (> main@%_27_0 0))
                (> @d_1_0 0)
                (= main@%_28_0 (select main@%sm11_0 main@%_27_0))
                (= main@%_29_0 (+ @d_2_0 (* 0 84) (* main@%.03.i_0 4)))
                (or (<= @d_2_0 0) (> main@%_29_0 0))
                (> @d_2_0 0)
                (= main@%_30_0 (select main@%sm8_0 main@%_29_0))
                (= main@%_31_0 (= main@%_28_0 main@%_30_0))
                (= main@%_32_0 (+ main@%.03.i_0 1))
                (=> main@.preheader_1 (and main@.preheader_1 main@.preheader_0))
                (=> (and main@.preheader_1 main@.preheader_0) main@%_31_0)
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.03.i_1 main@%_32_0))
                (=> (and main@.preheader_1 main@.preheader_0)
                    (= main@%.03.i_2 main@%.03.i_1))
                main@.preheader_1)))
  (=> a!1
      (main@.preheader main@%.03.i_2 @d_1_0 main@%sm11_0 @d_2_0 main@%sm8_0))))
(rule (let ((a!1 (and (main@.preheader main@%.03.i_0
                                 @d_1_0
                                 main@%sm11_0
                                 @d_2_0
                                 main@%sm8_0)
                true
                (= main@%_26_0 (< main@%.03.i_0 20))
                main@%_26_0
                (= main@%_27_0 (+ @d_1_0 (* 0 84) (* main@%.03.i_0 4)))
                (or (<= @d_1_0 0) (> main@%_27_0 0))
                (> @d_1_0 0)
                (= main@%_28_0 (select main@%sm11_0 main@%_27_0))
                (= main@%_29_0 (+ @d_2_0 (* 0 84) (* main@%.03.i_0 4)))
                (or (<= @d_2_0 0) (> main@%_29_0 0))
                (> @d_2_0 0)
                (= main@%_30_0 (select main@%sm8_0 main@%_29_0))
                (= main@%_31_0 (= main@%_28_0 main@%_30_0))
                (= main@%_32_0 (+ main@%.03.i_0 1))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_31_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

