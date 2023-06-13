(set-info :original "./results/chc/bytecode/antonopoulos/count-loops/loop-tiling.bc")
(set-info :authors "SeaHorn v.14.0.0-rc0")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ((Array Int Int) (Array Int Int) ))
(declare-rel main@empty.loop (Int Int Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) ))
(declare-rel main@_11 (Int Int Int Int Int Int Int Int (Array Int Int) (Array Int Int) Int Int Int ))
(declare-rel main@_14 (Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int (Array Int Int) Int ))
(declare-rel main@.preheader4 (Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int (Array Int Int) Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int Bool (Array Int Int) Int Int (Array Int Int) Int ))
(declare-rel main@.preheader1.us (Int (Array Int Int) Int Int Int Int (Array Int Int) Int ))
(declare-rel main@_35 (Int (Array Int Int) Int Int Int Int Int (Array Int Int) Int ))
(declare-rel main@.lr.ph33 (Int Int (Array Int Int) Int (Array Int Int) Int ))
(declare-rel main@_47 (Int Int Int (Array Int Int) Int (Array Int Int) Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_51_0 Int )
(declare-var main@%_52_0 Int )
(declare-var main@%_53_0 Int )
(declare-var main@%_54_0 Int )
(declare-var main@%_55_0 Int )
(declare-var main@%_56_0 Int )
(declare-var main@%_57_0 Bool )
(declare-var main@%_60_0 Bool )
(declare-var main@%_61_0 Int )
(declare-var main@%_62_0 Int )
(declare-var main@%_63_0 Int )
(declare-var main@%_64_0 Int )
(declare-var main@%_65_0 Int )
(declare-var main@%_66_0 Bool )
(declare-var main@%_49_0 Bool )
(declare-var main@%_42_0 Int )
(declare-var main@%_43_0 Int )
(declare-var main@%_44_0 Int )
(declare-var main@%_45_0 Int )
(declare-var main@%_46_0 Bool )
(declare-var main@%_34_0 Bool )
(declare-var main@%_36_0 Int )
(declare-var main@%_38_0 Bool )
(declare-var main@%shadow.mem.4.5_2 (Array Int Int) )
(declare-var main@%.05.i6.us_2 Int )
(declare-var main@%_30_0 Bool )
(declare-var main@%_31_0 Bool )
(declare-var main@%_39_0 Int )
(declare-var main@%_41_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%_10_0 Bool )
(declare-var main@%shadow.mem.0.2_2 (Array Int Int) )
(declare-var main@%.1.i8_2 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@%_24_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%shadow.mem.4.3_2 (Array Int Int) )
(declare-var main@%.04.i10_2 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_17_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%shadow.mem.4.2_2 (Array Int Int) )
(declare-var main@%.03.i9_2 Int )
(declare-var main@%nd.loop.cond_0 Bool )
(declare-var main@%sm13_0 (Array Int Int) )
(declare-var main@%sm14_0 (Array Int Int) )
(declare-var main@%_0_0 Bool )
(declare-var main@%_1_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@%_6_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var @a_1_0 Int )
(declare-var @a_2_0 Int )
(declare-var main@%sm_0 (Array Int Int) )
(declare-var main@%sm7_0 (Array Int Int) )
(declare-var main@%loop.bound_0 Int )
(declare-var main@%loop.bound1_0 Int )
(declare-var main@%loop.bound2_0 Int )
(declare-var main@%loop.bound3_0 Int )
(declare-var main@%loop.bound4_0 Int )
(declare-var main@%loop.bound5_0 Int )
(declare-var main@%loop.bound6_0 Int )
(declare-var main@empty.loop_0 Bool )
(declare-var main@empty.loop.body_0 Bool )
(declare-var main@empty.loop_1 Bool )
(declare-var main@_11_0 Bool )
(declare-var main@%shadow.mem.4.1_0 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_0 (Array Int Int) )
(declare-var main@%.0.i12_0 Int )
(declare-var main@%.01.i11_0 Int )
(declare-var main@%shadow.mem.4.1_1 (Array Int Int) )
(declare-var main@%shadow.mem.0.0_1 (Array Int Int) )
(declare-var main@%.0.i12_1 Int )
(declare-var main@%.01.i11_1 Int )
(declare-var main@%sm8_0 (Array Int Int) )
(declare-var main@%_13_0 Int )
(declare-var main@_14_0 Bool )
(declare-var main@%shadow.mem.4.2_0 (Array Int Int) )
(declare-var main@%.03.i9_0 Int )
(declare-var main@%shadow.mem.4.2_1 (Array Int Int) )
(declare-var main@%.03.i9_1 Int )
(declare-var main@%sm9_0 (Array Int Int) )
(declare-var main@%_16_0 Int )
(declare-var main@_14_1 Bool )
(declare-var main@_18_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@.preheader4_0 Bool )
(declare-var main@%shadow.mem.4.3_0 (Array Int Int) )
(declare-var main@%.04.i10_0 Int )
(declare-var main@%shadow.mem.4.3_1 (Array Int Int) )
(declare-var main@%.04.i10_1 Int )
(declare-var main@.thread_0 Bool )
(declare-var main@%_21_0 Bool )
(declare-var main@.preheader3_0 Bool )
(declare-var main@%shadow.mem.4.0_0 (Array Int Int) )
(declare-var main@%_7_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%.12.i15_0 Int )
(declare-var main@%shadow.mem.4.0_1 (Array Int Int) )
(declare-var main@%_7_1 Bool )
(declare-var main@%_8_1 Bool )
(declare-var main@%.12.i15_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%shadow.mem.0.2_0 (Array Int Int) )
(declare-var main@%.1.i8_0 Int )
(declare-var main@%shadow.mem.0.2_1 (Array Int Int) )
(declare-var main@%.1.i8_1 Int )
(declare-var main@.preheader2_0 Bool )
(declare-var main@%shadow.mem.0.1_0 (Array Int Int) )
(declare-var main@%.1.i.lcssa_0 Int )
(declare-var main@%shadow.mem.0.1_1 (Array Int Int) )
(declare-var main@%.1.i.lcssa_1 Int )
(declare-var main@.preheader1.us_0 Bool )
(declare-var main@%shadow.mem.4.4_0 (Array Int Int) )
(declare-var main@%.2.i7.us_0 Int )
(declare-var main@%shadow.mem.4.4_1 (Array Int Int) )
(declare-var main@%.2.i7.us_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%shadow.mem.4.6_0 (Array Int Int) )
(declare-var main@%shadow.mem.4.6_1 (Array Int Int) )
(declare-var main@.lr.ph33_0 Bool )
(declare-var main@%.06.i35_0 Int )
(declare-var main@%.06.i35_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%sm10_0 (Array Int Int) )
(declare-var main@%_23_0 Int )
(declare-var main@_25_0 Bool )
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Bool )
(declare-var main@%_28_0 Bool )
(declare-var main@%.0.i12_2 Int )
(declare-var main@%.01.i11_2 Int )
(declare-var main@.preheader4_1 Bool )
(declare-var main@%sm12_0 (Array Int Int) )
(declare-var main@%_40_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@_35_0 Bool )
(declare-var main@%shadow.mem.4.5_0 (Array Int Int) )
(declare-var main@%.05.i6.us_0 Int )
(declare-var main@%shadow.mem.4.5_1 (Array Int Int) )
(declare-var main@%.05.i6.us_1 Int )
(declare-var main@%sm11_0 (Array Int Int) )
(declare-var main@%_37_0 Int )
(declare-var main@_32_0 Bool )
(declare-var main@%_33_0 Int )
(declare-var main@%.2.i7.us_2 Int )
(declare-var main@_35_1 Bool )
(declare-var main@_47_0 Bool )
(declare-var main@%.07.i532_0 Int )
(declare-var main@%.07.i532_1 Int )
(declare-var main@%_48_0 Int )
(declare-var main@_58_0 Bool )
(declare-var main@%_59_0 Int )
(declare-var main@%.06.i35_2 Int )
(declare-var main@_50_0 Bool )
(declare-var main@_47_1 Bool )
(declare-var main@%.07.i532_2 Int )
(declare-var |tuple(main@_58_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@_50_0, main@verifier.error_0)| Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry main@%sm13_0 main@%sm14_0))
(rule (=> (and (main@entry main@%sm13_0 main@%sm14_0)
         true
         (= main@%sm_0 main@%sm13_0)
         (= main@%sm7_0 main@%sm14_0)
         (= main@%_0_0 (= main@%loop.bound_0 9))
         main@%_0_0
         (= main@%_1_0 (= main@%loop.bound1_0 9))
         main@%_1_0
         (= main@%_2_0 (= main@%loop.bound2_0 9))
         main@%_2_0
         (= main@%_3_0 (= main@%loop.bound3_0 99))
         main@%_3_0
         (= main@%_4_0 (= main@%loop.bound4_0 9))
         main@%_4_0
         (= main@%_5_0 (= main@%loop.bound5_0 9))
         main@%_5_0
         (= main@%_6_0 (= main@%loop.bound6_0 9))
         main@%_6_0
         true
         (=> main@empty.loop_0 (and main@empty.loop_0 main@entry_0))
         main@empty.loop_0)
    (main@empty.loop @a_1_0
                     @a_2_0
                     main@%loop.bound_0
                     main@%loop.bound2_0
                     main@%loop.bound1_0
                     main@%loop.bound3_0
                     main@%loop.bound5_0
                     main@%loop.bound6_0
                     main@%loop.bound4_0
                     main@%sm7_0
                     main@%sm_0)))
(rule (let ((a!1 (main@empty.loop @a_1_0
                            @a_2_0
                            main@%loop.bound_0
                            main@%loop.bound2_0
                            main@%loop.bound1_0
                            main@%loop.bound3_0
                            main@%loop.bound5_0
                            main@%loop.bound6_0
                            main@%loop.bound4_0
                            main@%sm7_0
                            main@%sm_0)))
  (=> (and a!1
           true
           (=> main@empty.loop.body_0
               (and main@empty.loop.body_0 main@empty.loop_0))
           (=> (and main@empty.loop.body_0 main@empty.loop_0)
               main@%nd.loop.cond_0)
           (=> main@empty.loop_1 (and main@empty.loop_1 main@empty.loop.body_0))
           main@empty.loop_1)
      a!1)))
(rule (=> (and (main@empty.loop @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%loop.bound4_0
                          main@%sm7_0
                          main@%sm_0)
         true
         (=> main@_11_0 (and main@_11_0 main@empty.loop_0))
         (=> (and main@_11_0 main@empty.loop_0) (not main@%nd.loop.cond_0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%shadow.mem.4.1_0 main@%sm7_0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_0 main@%sm_0))
         (=> (and main@_11_0 main@empty.loop_0) (= main@%.0.i12_0 0))
         (=> (and main@_11_0 main@empty.loop_0) (= main@%.01.i11_0 0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%.0.i12_1 main@%.0.i12_0))
         (=> (and main@_11_0 main@empty.loop_0)
             (= main@%.01.i11_1 main@%.01.i11_0))
         main@_11_0)
    (main@_11 @a_1_0
              @a_2_0
              main@%loop.bound_0
              main@%loop.bound2_0
              main@%loop.bound1_0
              main@%loop.bound3_0
              main@%.01.i11_1
              main@%.0.i12_1
              main@%shadow.mem.4.1_1
              main@%shadow.mem.0.0_1
              main@%loop.bound5_0
              main@%loop.bound6_0
              main@%loop.bound4_0)))
(rule (let ((a!1 (and (main@_11 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%shadow.mem.4.1_0
                          main@%shadow.mem.0.0_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%loop.bound4_0)
                true
                (= main@%_12_0 (+ @a_1_0 (* 0 400) (* main@%.0.i12_0 4)))
                (or (<= @a_1_0 0) (> main@%_12_0 0))
                (> @a_1_0 0)
                (= main@%sm8_0 (store main@%shadow.mem.0.0_0 main@%_12_0 0))
                (= main@%_13_0 (+ main@%.0.i12_0 1))
                (=> main@_14_0 (and main@_14_0 main@_11_0))
                (=> (and main@_14_0 main@_11_0)
                    (= main@%shadow.mem.4.2_0 main@%shadow.mem.4.1_0))
                (=> (and main@_14_0 main@_11_0) (= main@%.03.i9_0 0))
                (=> (and main@_14_0 main@_11_0)
                    (= main@%shadow.mem.4.2_1 main@%shadow.mem.4.2_0))
                (=> (and main@_14_0 main@_11_0)
                    (= main@%.03.i9_1 main@%.03.i9_0))
                main@_14_0)))
  (=> a!1
      (main@_14 @a_1_0
                @a_2_0
                main@%loop.bound_0
                main@%loop.bound2_0
                main@%loop.bound1_0
                main@%loop.bound3_0
                main@%sm8_0
                main@%_13_0
                main@%.01.i11_0
                main@%.0.i12_0
                main@%loop.bound5_0
                main@%loop.bound6_0
                main@%.03.i9_1
                main@%shadow.mem.4.2_1
                main@%loop.bound4_0))))
(rule (let ((a!1 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                (= main@%_15_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i11_0 40)
                      (* main@%.03.i9_0 4)))
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_14_1 (and main@_14_1 main@_14_0))
                (=> (and main@_14_1 main@_14_0) main@%_17_0)
                (=> (and main@_14_1 main@_14_0)
                    (= main@%shadow.mem.4.2_1 main@%sm9_0))
                (=> (and main@_14_1 main@_14_0) (= main@%.03.i9_1 main@%_16_0))
                (=> (and main@_14_1 main@_14_0)
                    (= main@%shadow.mem.4.2_2 main@%shadow.mem.4.2_1))
                (=> (and main@_14_1 main@_14_0)
                    (= main@%.03.i9_2 main@%.03.i9_1))
                main@_14_1)))
  (=> a!1
      (main@_14 @a_1_0
                @a_2_0
                main@%loop.bound_0
                main@%loop.bound2_0
                main@%loop.bound1_0
                main@%loop.bound3_0
                main@%sm8_0
                main@%_13_0
                main@%.01.i11_0
                main@%.0.i12_0
                main@%loop.bound5_0
                main@%loop.bound6_0
                main@%.03.i9_2
                main@%shadow.mem.4.2_2
                main@%loop.bound4_0))))
(rule (let ((a!1 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                (= main@%_15_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i11_0 40)
                      (* main@%.03.i9_0 4)))
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_18_0 (and main@_18_0 main@_14_0))
                (=> (and main@_18_0 main@_14_0) (not main@%_17_0))
                (=> main@_18_0 (= main@%_19_0 (+ main@%.01.i11_0 1)))
                (=> main@_18_0
                    (= main@%_20_0 (< main@%.01.i11_0 main@%loop.bound6_0)))
                (=> main@.preheader4_0 (and main@.preheader4_0 main@_18_0))
                (=> (and main@.preheader4_0 main@_18_0) main@%_20_0)
                (=> (and main@.preheader4_0 main@_18_0)
                    (= main@%shadow.mem.4.3_0 main@%sm9_0))
                (=> (and main@.preheader4_0 main@_18_0) (= main@%.04.i10_0 0))
                (=> (and main@.preheader4_0 main@_18_0)
                    (= main@%shadow.mem.4.3_1 main@%shadow.mem.4.3_0))
                (=> (and main@.preheader4_0 main@_18_0)
                    (= main@%.04.i10_1 main@%.04.i10_0))
                main@.preheader4_0)))
  (=> a!1
      (main@.preheader4 @a_1_0
                        @a_2_0
                        main@%loop.bound_0
                        main@%loop.bound2_0
                        main@%loop.bound1_0
                        main@%loop.bound3_0
                        main@%sm8_0
                        main@%_13_0
                        main@%.01.i11_0
                        main@%.0.i12_0
                        main@%_19_0
                        main@%.04.i10_1
                        main@%shadow.mem.4.3_1
                        main@%loop.bound5_0
                        main@%loop.bound6_0
                        main@%loop.bound4_0))))
(rule (let ((a!1 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                (= main@%_15_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i11_0 40)
                      (* main@%.03.i9_0 4)))
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_18_0 (and main@_18_0 main@_14_0))
                (=> (and main@_18_0 main@_14_0) (not main@%_17_0))
                (=> main@_18_0 (= main@%_19_0 (+ main@%.01.i11_0 1)))
                (=> main@_18_0
                    (= main@%_20_0 (< main@%.01.i11_0 main@%loop.bound6_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_18_0))
                (=> (and main@.thread_0 main@_18_0) (not main@%_20_0))
                (=> main@.thread_0 (= main@%_21_0 (< main@%.0.i12_0 99)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.thread_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_0 main@%sm9_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_0 false))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_0 main@%_21_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_0 main@%_19_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader3_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0) main@%_10_0)
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.2_0 main@%sm8_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%.1.i8_0 main@%_13_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%.1.i8_1 main@%.1.i8_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph @a_1_0
                   @a_2_0
                   main@%loop.bound_0
                   main@%loop.bound2_0
                   main@%loop.bound1_0
                   main@%_7_1
                   main@%shadow.mem.4.0_1
                   main@%.12.i15_1
                   main@%.1.i8_1
                   main@%shadow.mem.0.2_1
                   main@%loop.bound3_0))))
(rule (let ((a!1 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                (= main@%_15_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.01.i11_0 40)
                      (* main@%.03.i9_0 4)))
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_18_0 (and main@_18_0 main@_14_0))
                (=> (and main@_18_0 main@_14_0) (not main@%_17_0))
                (=> main@_18_0 (= main@%_19_0 (+ main@%.01.i11_0 1)))
                (=> main@_18_0
                    (= main@%_20_0 (< main@%.01.i11_0 main@%loop.bound6_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_18_0))
                (=> (and main@.thread_0 main@_18_0) (not main@%_20_0))
                (=> main@.thread_0 (= main@%_21_0 (< main@%.0.i12_0 99)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.thread_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_0 main@%sm9_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_0 false))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_0 main@%_21_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_0 main@%_19_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader1.us_0
                    (and main@.preheader1.us_0 main@.preheader2_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0) main@%_31_0)
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_0 main@%.12.i15_1))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_1 main@%.2.i7.us_0))
                main@.preheader1.us_0)))
  (=> a!1
      (main@.preheader1.us
        @a_1_0
        main@%shadow.mem.0.1_1
        @a_2_0
        main@%loop.bound_0
        main@%.2.i7.us_1
        main@%loop.bound2_0
        main@%shadow.mem.4.4_1
        main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_15_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.01.i11_0 40)
                 (* main@%.03.i9_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_18_0 (and main@_18_0 main@_14_0))
                (=> (and main@_18_0 main@_14_0) (not main@%_17_0))
                (=> main@_18_0 (= main@%_19_0 (+ main@%.01.i11_0 1)))
                (=> main@_18_0
                    (= main@%_20_0 (< main@%.01.i11_0 main@%loop.bound6_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_18_0))
                (=> (and main@.thread_0 main@_18_0) (not main@%_20_0))
                (=> main@.thread_0 (= main@%_21_0 (< main@%.0.i12_0 99)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.thread_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_0 main@%sm9_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_0 false))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_0 main@%_21_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_0 main@%_19_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@.lr.ph33_0 (and main@.lr.ph33_0 main@.preheader_0))
                (=> (and main@.lr.ph33_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_0 0))
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_1 main@%.06.i35_0))
                main@.lr.ph33_0)))
  (=> a!4
      (main@.lr.ph33 main@%.06.i35_1
                     @a_1_0
                     main@%shadow.mem.0.1_1
                     @a_2_0
                     main@%shadow.mem.4.6_1
                     main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_15_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.01.i11_0 40)
                 (* main@%.03.i9_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_14 @a_1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%loop.bound2_0
                          main@%loop.bound1_0
                          main@%loop.bound3_0
                          main@%sm8_0
                          main@%_13_0
                          main@%.01.i11_0
                          main@%.0.i12_0
                          main@%loop.bound5_0
                          main@%loop.bound6_0
                          main@%.03.i9_0
                          main@%shadow.mem.4.2_0
                          main@%loop.bound4_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_15_0 0))
                (> @a_2_0 0)
                (= main@%sm9_0 (store main@%shadow.mem.4.2_0 main@%_15_0 0))
                (= main@%_16_0 (+ main@%.03.i9_0 1))
                (= main@%_17_0 (< main@%.03.i9_0 main@%loop.bound4_0))
                (=> main@_18_0 (and main@_18_0 main@_14_0))
                (=> (and main@_18_0 main@_14_0) (not main@%_17_0))
                (=> main@_18_0 (= main@%_19_0 (+ main@%.01.i11_0 1)))
                (=> main@_18_0
                    (= main@%_20_0 (< main@%.01.i11_0 main@%loop.bound6_0)))
                (=> main@.thread_0 (and main@.thread_0 main@_18_0))
                (=> (and main@.thread_0 main@_18_0) (not main@%_20_0))
                (=> main@.thread_0 (= main@%_21_0 (< main@%.0.i12_0 99)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@.thread_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_0 main@%sm9_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_0 false))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_0 main@%_21_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_0 main@%_19_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@.thread_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!4 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                (= main@%_22_0
                   (+ @a_2_0 (* 0 400) (* main@%_19_0 40) (* main@%.04.i10_0 4)))
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@_25_0 (and main@_25_0 main@.preheader4_0))
                (=> (and main@_25_0 main@.preheader4_0) (not main@%_24_0))
                (=> main@_25_0 (= main@%_26_0 (+ main@%.01.i11_0 2)))
                (=> main@_25_0 (= main@%_27_0 (< main@%.0.i12_0 99)))
                (=> main@_25_0 (= main@%_28_0 (< main@%.01.i11_0 8)))
                (=> main@_25_0
                    (= main@%_29_0 (ite main@%_27_0 main@%_28_0 false)))
                (=> main@_11_0 (and main@_11_0 main@_25_0))
                (=> (and main@_11_0 main@_25_0) main@%_29_0)
                (=> (and main@_11_0 main@_25_0)
                    (= main@%shadow.mem.4.1_0 main@%sm10_0))
                (=> (and main@_11_0 main@_25_0)
                    (= main@%shadow.mem.0.0_0 main@%sm8_0))
                (=> (and main@_11_0 main@_25_0) (= main@%.0.i12_1 main@%_13_0))
                (=> (and main@_11_0 main@_25_0) (= main@%.01.i11_1 main@%_26_0))
                (=> (and main@_11_0 main@_25_0)
                    (= main@%shadow.mem.4.1_1 main@%shadow.mem.4.1_0))
                (=> (and main@_11_0 main@_25_0)
                    (= main@%shadow.mem.0.0_1 main@%shadow.mem.0.0_0))
                (=> (and main@_11_0 main@_25_0)
                    (= main@%.0.i12_2 main@%.0.i12_1))
                (=> (and main@_11_0 main@_25_0)
                    (= main@%.01.i11_2 main@%.01.i11_1))
                main@_11_0)))
  (=> a!1
      (main@_11 @a_1_0
                @a_2_0
                main@%loop.bound_0
                main@%loop.bound2_0
                main@%loop.bound1_0
                main@%loop.bound3_0
                main@%.01.i11_2
                main@%.0.i12_2
                main@%shadow.mem.4.1_1
                main@%shadow.mem.0.0_1
                main@%loop.bound5_0
                main@%loop.bound6_0
                main@%loop.bound4_0))))
(rule (let ((a!1 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                (= main@%_22_0
                   (+ @a_2_0 (* 0 400) (* main@%_19_0 40) (* main@%.04.i10_0 4)))
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@.preheader4_1
                    (and main@.preheader4_1 main@.preheader4_0))
                (=> (and main@.preheader4_1 main@.preheader4_0) main@%_24_0)
                (=> (and main@.preheader4_1 main@.preheader4_0)
                    (= main@%shadow.mem.4.3_1 main@%sm10_0))
                (=> (and main@.preheader4_1 main@.preheader4_0)
                    (= main@%.04.i10_1 main@%_23_0))
                (=> (and main@.preheader4_1 main@.preheader4_0)
                    (= main@%shadow.mem.4.3_2 main@%shadow.mem.4.3_1))
                (=> (and main@.preheader4_1 main@.preheader4_0)
                    (= main@%.04.i10_2 main@%.04.i10_1))
                main@.preheader4_1)))
  (=> a!1
      (main@.preheader4 @a_1_0
                        @a_2_0
                        main@%loop.bound_0
                        main@%loop.bound2_0
                        main@%loop.bound1_0
                        main@%loop.bound3_0
                        main@%sm8_0
                        main@%_13_0
                        main@%.01.i11_0
                        main@%.0.i12_0
                        main@%_19_0
                        main@%.04.i10_2
                        main@%shadow.mem.4.3_2
                        main@%loop.bound5_0
                        main@%loop.bound6_0
                        main@%loop.bound4_0))))
(rule (let ((a!1 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                (= main@%_22_0
                   (+ @a_2_0 (* 0 400) (* main@%_19_0 40) (* main@%.04.i10_0 4)))
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@_25_0 (and main@_25_0 main@.preheader4_0))
                (=> (and main@_25_0 main@.preheader4_0) (not main@%_24_0))
                (=> main@_25_0 (= main@%_26_0 (+ main@%.01.i11_0 2)))
                (=> main@_25_0 (= main@%_27_0 (< main@%.0.i12_0 99)))
                (=> main@_25_0 (= main@%_28_0 (< main@%.01.i11_0 8)))
                (=> main@_25_0
                    (= main@%_29_0 (ite main@%_27_0 main@%_28_0 false)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@_25_0))
                (=> (and main@.preheader3_0 main@_25_0) (not main@%_29_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_0 main@%sm10_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_0 main@%_28_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_0 main@%_27_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_0 main@%_26_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader3_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0) main@%_10_0)
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.2_0 main@%sm8_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%.1.i8_0 main@%_13_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.2_1 main@%shadow.mem.0.2_0))
                (=> (and main@.lr.ph_0 main@.preheader3_0)
                    (= main@%.1.i8_1 main@%.1.i8_0))
                main@.lr.ph_0)))
  (=> a!1
      (main@.lr.ph @a_1_0
                   @a_2_0
                   main@%loop.bound_0
                   main@%loop.bound2_0
                   main@%loop.bound1_0
                   main@%_7_1
                   main@%shadow.mem.4.0_1
                   main@%.12.i15_1
                   main@%.1.i8_1
                   main@%shadow.mem.0.2_1
                   main@%loop.bound3_0))))
(rule (let ((a!1 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                (= main@%_22_0
                   (+ @a_2_0 (* 0 400) (* main@%_19_0 40) (* main@%.04.i10_0 4)))
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@_25_0 (and main@_25_0 main@.preheader4_0))
                (=> (and main@_25_0 main@.preheader4_0) (not main@%_24_0))
                (=> main@_25_0 (= main@%_26_0 (+ main@%.01.i11_0 2)))
                (=> main@_25_0 (= main@%_27_0 (< main@%.0.i12_0 99)))
                (=> main@_25_0 (= main@%_28_0 (< main@%.01.i11_0 8)))
                (=> main@_25_0
                    (= main@%_29_0 (ite main@%_27_0 main@%_28_0 false)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@_25_0))
                (=> (and main@.preheader3_0 main@_25_0) (not main@%_29_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_0 main@%sm10_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_0 main@%_28_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_0 main@%_27_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_0 main@%_26_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader1.us_0
                    (and main@.preheader1.us_0 main@.preheader2_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0) main@%_31_0)
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_0 main@%.12.i15_1))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_1 main@%.2.i7.us_0))
                main@.preheader1.us_0)))
  (=> a!1
      (main@.preheader1.us
        @a_1_0
        main@%shadow.mem.0.1_1
        @a_2_0
        main@%loop.bound_0
        main@%.2.i7.us_1
        main@%loop.bound2_0
        main@%shadow.mem.4.4_1
        main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_22_0
              (+ (+ @a_2_0 (* 0 400)) (* main@%_19_0 40) (* main@%.04.i10_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@_25_0 (and main@_25_0 main@.preheader4_0))
                (=> (and main@_25_0 main@.preheader4_0) (not main@%_24_0))
                (=> main@_25_0 (= main@%_26_0 (+ main@%.01.i11_0 2)))
                (=> main@_25_0 (= main@%_27_0 (< main@%.0.i12_0 99)))
                (=> main@_25_0 (= main@%_28_0 (< main@%.01.i11_0 8)))
                (=> main@_25_0
                    (= main@%_29_0 (ite main@%_27_0 main@%_28_0 false)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@_25_0))
                (=> (and main@.preheader3_0 main@_25_0) (not main@%_29_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_0 main@%sm10_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_0 main@%_28_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_0 main@%_27_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_0 main@%_26_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@.lr.ph33_0 (and main@.lr.ph33_0 main@.preheader_0))
                (=> (and main@.lr.ph33_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_0 0))
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_1 main@%.06.i35_0))
                main@.lr.ph33_0)))
  (=> a!4
      (main@.lr.ph33 main@%.06.i35_1
                     @a_1_0
                     main@%shadow.mem.0.1_1
                     @a_2_0
                     main@%shadow.mem.4.6_1
                     main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_22_0
              (+ (+ @a_2_0 (* 0 400)) (* main@%_19_0 40) (* main@%.04.i10_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@.preheader4 @a_1_0
                                  @a_2_0
                                  main@%loop.bound_0
                                  main@%loop.bound2_0
                                  main@%loop.bound1_0
                                  main@%loop.bound3_0
                                  main@%sm8_0
                                  main@%_13_0
                                  main@%.01.i11_0
                                  main@%.0.i12_0
                                  main@%_19_0
                                  main@%.04.i10_0
                                  main@%shadow.mem.4.3_0
                                  main@%loop.bound5_0
                                  main@%loop.bound6_0
                                  main@%loop.bound4_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_22_0 0))
                (> @a_2_0 0)
                (= main@%sm10_0 (store main@%shadow.mem.4.3_0 main@%_22_0 0))
                (= main@%_23_0 (+ main@%.04.i10_0 1))
                (= main@%_24_0 (< main@%.04.i10_0 main@%loop.bound5_0))
                (=> main@_25_0 (and main@_25_0 main@.preheader4_0))
                (=> (and main@_25_0 main@.preheader4_0) (not main@%_24_0))
                (=> main@_25_0 (= main@%_26_0 (+ main@%.01.i11_0 2)))
                (=> main@_25_0 (= main@%_27_0 (< main@%.0.i12_0 99)))
                (=> main@_25_0 (= main@%_28_0 (< main@%.01.i11_0 8)))
                (=> main@_25_0
                    (= main@%_29_0 (ite main@%_27_0 main@%_28_0 false)))
                (=> main@.preheader3_0 (and main@.preheader3_0 main@_25_0))
                (=> (and main@.preheader3_0 main@_25_0) (not main@%_29_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_0 main@%sm10_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_0 main@%_28_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_0 main@%_27_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_0 main@%_26_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%shadow.mem.4.0_1 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_7_1 main@%_7_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.preheader3_0 main@_25_0)
                    (= main@%.12.i15_1 main@%.12.i15_0))
                (=> main@.preheader3_0 (= main@%_9_0 (> main@%.12.i15_1 9)))
                (=> main@.preheader3_0
                    (= main@%_10_0 (ite main@%_8_1 main@%_9_0 false)))
                (=> main@.preheader2_0
                    (and main@.preheader2_0 main@.preheader3_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (not main@%_10_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_0 main@%sm8_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_0 main@%_13_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.preheader3_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_1 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_1))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!4 main@verifier.error.split))))
(rule (let ((a!1 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%loop.bound_0
                             main@%loop.bound2_0
                             main@%loop.bound1_0
                             main@%_7_0
                             main@%shadow.mem.4.0_0
                             main@%.12.i15_0
                             main@%.1.i8_0
                             main@%shadow.mem.0.2_0
                             main@%loop.bound3_0)
                true
                (= main@%_39_0 (+ @a_1_0 (* 0 400) (* main@%.1.i8_0 4)))
                (or (<= @a_1_0 0) (> main@%_39_0 0))
                (> @a_1_0 0)
                (= main@%sm12_0 (store main@%shadow.mem.0.2_0 main@%_39_0 0))
                (= main@%_40_0 (+ main@%.1.i8_0 1))
                (= main@%_41_0 (< main@%.1.i8_0 main@%loop.bound3_0))
                (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
                (=> (and main@.lr.ph_1 main@.lr.ph_0) main@%_41_0)
                (=> (and main@.lr.ph_1 main@.lr.ph_0)
                    (= main@%shadow.mem.0.2_1 main@%sm12_0))
                (=> (and main@.lr.ph_1 main@.lr.ph_0)
                    (= main@%.1.i8_1 main@%_40_0))
                (=> (and main@.lr.ph_1 main@.lr.ph_0)
                    (= main@%shadow.mem.0.2_2 main@%shadow.mem.0.2_1))
                (=> (and main@.lr.ph_1 main@.lr.ph_0)
                    (= main@%.1.i8_2 main@%.1.i8_1))
                main@.lr.ph_1)))
  (=> a!1
      (main@.lr.ph @a_1_0
                   @a_2_0
                   main@%loop.bound_0
                   main@%loop.bound2_0
                   main@%loop.bound1_0
                   main@%_7_0
                   main@%shadow.mem.4.0_0
                   main@%.12.i15_0
                   main@%.1.i8_2
                   main@%shadow.mem.0.2_2
                   main@%loop.bound3_0))))
(rule (let ((a!1 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%loop.bound_0
                             main@%loop.bound2_0
                             main@%loop.bound1_0
                             main@%_7_0
                             main@%shadow.mem.4.0_0
                             main@%.12.i15_0
                             main@%.1.i8_0
                             main@%shadow.mem.0.2_0
                             main@%loop.bound3_0)
                true
                (= main@%_39_0 (+ @a_1_0 (* 0 400) (* main@%.1.i8_0 4)))
                (or (<= @a_1_0 0) (> main@%_39_0 0))
                (> @a_1_0 0)
                (= main@%sm12_0 (store main@%shadow.mem.0.2_0 main@%_39_0 0))
                (= main@%_40_0 (+ main@%.1.i8_0 1))
                (= main@%_41_0 (< main@%.1.i8_0 main@%loop.bound3_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0) (not main@%_41_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_0 main@%sm12_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_0 main@%_40_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_0 false)))
                (=> main@.preheader1.us_0
                    (and main@.preheader1.us_0 main@.preheader2_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0) main@%_31_0)
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_0 main@%.12.i15_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader1.us_0 main@.preheader2_0)
                    (= main@%.2.i7.us_1 main@%.2.i7.us_0))
                main@.preheader1.us_0)))
  (=> a!1
      (main@.preheader1.us
        @a_1_0
        main@%shadow.mem.0.1_1
        @a_2_0
        main@%loop.bound_0
        main@%.2.i7.us_1
        main@%loop.bound2_0
        main@%shadow.mem.4.4_1
        main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_39_0 (+ (+ @a_1_0 (* 0 400)) (* main@%.1.i8_0 4))))
      (a!2 (= main@%_42_0 (+ (+ @a_1_0 (* 0 400)) (* 0 4))))
      (a!3 (=> main@.preheader_0
               (= main@%_44_0 (+ @a_2_0 (* 0 400) (* 0 40) (* 0 4))))))
(let ((a!4 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%loop.bound_0
                             main@%loop.bound2_0
                             main@%loop.bound1_0
                             main@%_7_0
                             main@%shadow.mem.4.0_0
                             main@%.12.i15_0
                             main@%.1.i8_0
                             main@%shadow.mem.0.2_0
                             main@%loop.bound3_0)
                true
                a!1
                (or (<= @a_1_0 0) (> main@%_39_0 0))
                (> @a_1_0 0)
                (= main@%sm12_0 (store main@%shadow.mem.0.2_0 main@%_39_0 0))
                (= main@%_40_0 (+ main@%.1.i8_0 1))
                (= main@%_41_0 (< main@%.1.i8_0 main@%loop.bound3_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0) (not main@%_41_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_0 main@%sm12_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_0 main@%_40_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                (=> main@.preheader_0 a!2)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                a!3
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@.lr.ph33_0 (and main@.lr.ph33_0 main@.preheader_0))
                (=> (and main@.lr.ph33_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_0 0))
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_1 main@%.06.i35_0))
                main@.lr.ph33_0)))
  (=> a!4
      (main@.lr.ph33 main@%.06.i35_1
                     @a_1_0
                     main@%shadow.mem.0.1_1
                     @a_2_0
                     main@%shadow.mem.4.6_1
                     main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_39_0 (+ (+ @a_1_0 (* 0 400)) (* main@%.1.i8_0 4))))
      (a!2 (= main@%_42_0 (+ (+ @a_1_0 (* 0 400)) (* 0 4))))
      (a!3 (=> main@.preheader_0
               (= main@%_44_0 (+ @a_2_0 (* 0 400) (* 0 40) (* 0 4))))))
(let ((a!4 (and (main@.lr.ph @a_1_0
                             @a_2_0
                             main@%loop.bound_0
                             main@%loop.bound2_0
                             main@%loop.bound1_0
                             main@%_7_0
                             main@%shadow.mem.4.0_0
                             main@%.12.i15_0
                             main@%.1.i8_0
                             main@%shadow.mem.0.2_0
                             main@%loop.bound3_0)
                true
                a!1
                (or (<= @a_1_0 0) (> main@%_39_0 0))
                (> @a_1_0 0)
                (= main@%sm12_0 (store main@%shadow.mem.0.2_0 main@%_39_0 0))
                (= main@%_40_0 (+ main@%.1.i8_0 1))
                (= main@%_41_0 (< main@%.1.i8_0 main@%loop.bound3_0))
                (=> main@.preheader2_0 (and main@.preheader2_0 main@.lr.ph_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0) (not main@%_41_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_0 main@%sm12_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_0 main@%_40_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%shadow.mem.0.1_1 main@%shadow.mem.0.1_0))
                (=> (and main@.preheader2_0 main@.lr.ph_0)
                    (= main@%.1.i.lcssa_1 main@%.1.i.lcssa_0))
                (=> main@.preheader2_0
                    (= main@%_30_0 (> main@%.1.i.lcssa_1 99)))
                (=> main@.preheader2_0
                    (= main@%_31_0 (ite main@%_30_0 main@%_7_0 false)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader2_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (not main@%_31_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_0 main@%shadow.mem.4.0_0))
                (=> (and main@.preheader_0 main@.preheader2_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                (=> main@.preheader_0 a!2)
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_1 main@%_42_0)))
                a!3
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!4 main@verifier.error.split))))
(rule (=> (and (main@.preheader1.us
           @a_1_0
           main@%shadow.mem.0.1_0
           @a_2_0
           main@%loop.bound_0
           main@%.2.i7.us_0
           main@%loop.bound2_0
           main@%shadow.mem.4.4_0
           main@%loop.bound1_0)
         true
         (=> main@_35_0 (and main@_35_0 main@.preheader1.us_0))
         (=> (and main@_35_0 main@.preheader1.us_0)
             (= main@%shadow.mem.4.5_0 main@%shadow.mem.4.4_0))
         (=> (and main@_35_0 main@.preheader1.us_0) (= main@%.05.i6.us_0 0))
         (=> (and main@_35_0 main@.preheader1.us_0)
             (= main@%shadow.mem.4.5_1 main@%shadow.mem.4.5_0))
         (=> (and main@_35_0 main@.preheader1.us_0)
             (= main@%.05.i6.us_1 main@%.05.i6.us_0))
         main@_35_0)
    (main@_35 @a_1_0
              main@%shadow.mem.0.1_0
              @a_2_0
              main@%loop.bound_0
              main@%.2.i7.us_0
              main@%loop.bound2_0
              main@%.05.i6.us_1
              main@%shadow.mem.4.5_1
              main@%loop.bound1_0)))
(rule (let ((a!1 (and (main@_35 @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%.2.i7.us_0
                          main@%loop.bound2_0
                          main@%.05.i6.us_0
                          main@%shadow.mem.4.5_0
                          main@%loop.bound1_0)
                true
                (= main@%_36_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.2.i7.us_0 40)
                      (* main@%.05.i6.us_0 4)))
                (or (<= @a_2_0 0) (> main@%_36_0 0))
                (> @a_2_0 0)
                (= main@%sm11_0 (store main@%shadow.mem.4.5_0 main@%_36_0 0))
                (= main@%_37_0 (+ main@%.05.i6.us_0 1))
                (= main@%_38_0 (< main@%.05.i6.us_0 main@%loop.bound1_0))
                (=> main@_32_0 (and main@_32_0 main@_35_0))
                (=> (and main@_32_0 main@_35_0) (not main@%_38_0))
                (=> main@_32_0 (= main@%_33_0 (+ main@%.2.i7.us_0 1)))
                (=> main@_32_0
                    (= main@%_34_0 (< main@%.2.i7.us_0 main@%loop.bound2_0)))
                (=> main@.preheader1.us_0
                    (and main@.preheader1.us_0 main@_32_0))
                (=> (and main@.preheader1.us_0 main@_32_0) main@%_34_0)
                (=> (and main@.preheader1.us_0 main@_32_0)
                    (= main@%shadow.mem.4.4_0 main@%sm11_0))
                (=> (and main@.preheader1.us_0 main@_32_0)
                    (= main@%.2.i7.us_1 main@%_33_0))
                (=> (and main@.preheader1.us_0 main@_32_0)
                    (= main@%shadow.mem.4.4_1 main@%shadow.mem.4.4_0))
                (=> (and main@.preheader1.us_0 main@_32_0)
                    (= main@%.2.i7.us_2 main@%.2.i7.us_1))
                main@.preheader1.us_0)))
  (=> a!1
      (main@.preheader1.us
        @a_1_0
        main@%shadow.mem.0.1_0
        @a_2_0
        main@%loop.bound_0
        main@%.2.i7.us_2
        main@%loop.bound2_0
        main@%shadow.mem.4.4_1
        main@%loop.bound1_0))))
(rule (let ((a!1 (and (main@_35 @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%.2.i7.us_0
                          main@%loop.bound2_0
                          main@%.05.i6.us_0
                          main@%shadow.mem.4.5_0
                          main@%loop.bound1_0)
                true
                (= main@%_36_0
                   (+ @a_2_0
                      (* 0 400)
                      (* main@%.2.i7.us_0 40)
                      (* main@%.05.i6.us_0 4)))
                (or (<= @a_2_0 0) (> main@%_36_0 0))
                (> @a_2_0 0)
                (= main@%sm11_0 (store main@%shadow.mem.4.5_0 main@%_36_0 0))
                (= main@%_37_0 (+ main@%.05.i6.us_0 1))
                (= main@%_38_0 (< main@%.05.i6.us_0 main@%loop.bound1_0))
                (=> main@_35_1 (and main@_35_1 main@_35_0))
                (=> (and main@_35_1 main@_35_0) main@%_38_0)
                (=> (and main@_35_1 main@_35_0)
                    (= main@%shadow.mem.4.5_1 main@%sm11_0))
                (=> (and main@_35_1 main@_35_0)
                    (= main@%.05.i6.us_1 main@%_37_0))
                (=> (and main@_35_1 main@_35_0)
                    (= main@%shadow.mem.4.5_2 main@%shadow.mem.4.5_1))
                (=> (and main@_35_1 main@_35_0)
                    (= main@%.05.i6.us_2 main@%.05.i6.us_1))
                main@_35_1)))
  (=> a!1
      (main@_35 @a_1_0
                main@%shadow.mem.0.1_0
                @a_2_0
                main@%loop.bound_0
                main@%.2.i7.us_0
                main@%loop.bound2_0
                main@%.05.i6.us_2
                main@%shadow.mem.4.5_2
                main@%loop.bound1_0))))
(rule (let ((a!1 (= main@%_36_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.2.i7.us_0 40)
                 (* main@%.05.i6.us_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_35 @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%.2.i7.us_0
                          main@%loop.bound2_0
                          main@%.05.i6.us_0
                          main@%shadow.mem.4.5_0
                          main@%loop.bound1_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_36_0 0))
                (> @a_2_0 0)
                (= main@%sm11_0 (store main@%shadow.mem.4.5_0 main@%_36_0 0))
                (= main@%_37_0 (+ main@%.05.i6.us_0 1))
                (= main@%_38_0 (< main@%.05.i6.us_0 main@%loop.bound1_0))
                (=> main@_32_0 (and main@_32_0 main@_35_0))
                (=> (and main@_32_0 main@_35_0) (not main@%_38_0))
                (=> main@_32_0 (= main@%_33_0 (+ main@%.2.i7.us_0 1)))
                (=> main@_32_0
                    (= main@%_34_0 (< main@%.2.i7.us_0 main@%loop.bound2_0)))
                (=> main@.preheader_0 (and main@.preheader_0 main@_32_0))
                (=> (and main@.preheader_0 main@_32_0) (not main@%_34_0))
                (=> (and main@.preheader_0 main@_32_0)
                    (= main@%shadow.mem.4.6_0 main@%sm11_0))
                (=> (and main@.preheader_0 main@_32_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_0 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@.lr.ph33_0 (and main@.lr.ph33_0 main@.preheader_0))
                (=> (and main@.lr.ph33_0 main@.preheader_0) main@%_46_0)
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_0 0))
                (=> (and main@.lr.ph33_0 main@.preheader_0)
                    (= main@%.06.i35_1 main@%.06.i35_0))
                main@.lr.ph33_0)))
  (=> a!4
      (main@.lr.ph33 main@%.06.i35_1
                     @a_1_0
                     main@%shadow.mem.0.1_0
                     @a_2_0
                     main@%shadow.mem.4.6_1
                     main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_36_0
              (+ (+ @a_2_0 (* 0 400))
                 (* main@%.2.i7.us_0 40)
                 (* main@%.05.i6.us_0 4))))
      (a!2 (=> main@.preheader_0 (= main@%_42_0 (+ @a_1_0 (* 0 400) (* 0 4)))))
      (a!3 (= main@%_44_0 (+ (+ @a_2_0 (* 0 400)) (* 0 40) (* 0 4)))))
(let ((a!4 (and (main@_35 @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%loop.bound_0
                          main@%.2.i7.us_0
                          main@%loop.bound2_0
                          main@%.05.i6.us_0
                          main@%shadow.mem.4.5_0
                          main@%loop.bound1_0)
                true
                a!1
                (or (<= @a_2_0 0) (> main@%_36_0 0))
                (> @a_2_0 0)
                (= main@%sm11_0 (store main@%shadow.mem.4.5_0 main@%_36_0 0))
                (= main@%_37_0 (+ main@%.05.i6.us_0 1))
                (= main@%_38_0 (< main@%.05.i6.us_0 main@%loop.bound1_0))
                (=> main@_32_0 (and main@_32_0 main@_35_0))
                (=> (and main@_32_0 main@_35_0) (not main@%_38_0))
                (=> main@_32_0 (= main@%_33_0 (+ main@%.2.i7.us_0 1)))
                (=> main@_32_0
                    (= main@%_34_0 (< main@%.2.i7.us_0 main@%loop.bound2_0)))
                (=> main@.preheader_0 (and main@.preheader_0 main@_32_0))
                (=> (and main@.preheader_0 main@_32_0) (not main@%_34_0))
                (=> (and main@.preheader_0 main@_32_0)
                    (= main@%shadow.mem.4.6_0 main@%sm11_0))
                (=> (and main@.preheader_0 main@_32_0)
                    (= main@%shadow.mem.4.6_1 main@%shadow.mem.4.6_0))
                true
                a!2
                (=> main@.preheader_0 (or (<= @a_1_0 0) (> main@%_42_0 0)))
                (=> main@.preheader_0
                    (= main@%_43_0 (select main@%shadow.mem.0.1_0 main@%_42_0)))
                (=> main@.preheader_0 a!3)
                (=> main@.preheader_0 (or (<= @a_2_0 0) (> main@%_44_0 0)))
                (=> main@.preheader_0
                    (= main@%_45_0 (select main@%shadow.mem.4.6_1 main@%_44_0)))
                (=> main@.preheader_0
                    (= main@%_46_0 (= main@%_43_0 main@%_45_0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (not main@%_46_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!4 main@verifier.error.split))))
(rule (=> (and (main@.lr.ph33 main@%.06.i35_0
                        @a_1_0
                        main@%shadow.mem.0.1_0
                        @a_2_0
                        main@%shadow.mem.4.6_0
                        main@%loop.bound_0)
         true
         (=> main@_47_0 (and main@_47_0 main@.lr.ph33_0))
         (=> (and main@_47_0 main@.lr.ph33_0) (= main@%.07.i532_0 0))
         (=> (and main@_47_0 main@.lr.ph33_0)
             (= main@%.07.i532_1 main@%.07.i532_0))
         main@_47_0)
    (main@_47 main@%.07.i532_1
              main@%.06.i35_0
              @a_1_0
              main@%shadow.mem.0.1_0
              @a_2_0
              main@%shadow.mem.4.6_0
              main@%loop.bound_0)))
(rule (let ((a!1 (=> main@_58_0
               (= main@%_62_0 (+ @a_1_0 (* 0 400) (* main@%_61_0 4)))))
      (a!2 (=> main@_58_0
               (= main@%_64_0 (+ @a_2_0 (* 0 400) (* main@%_59_0 40) (* 0 4))))))
(let ((a!3 (and (main@_47 main@%.07.i532_0
                          main@%.06.i35_0
                          @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%shadow.mem.4.6_0
                          main@%loop.bound_0)
                true
                (= main@%_48_0 (+ main@%.07.i532_0 1))
                (= main@%_49_0 (< main@%.07.i532_0 main@%loop.bound_0))
                (=> main@_58_0 (and main@_58_0 main@_47_0))
                (=> (and main@_58_0 main@_47_0) (not main@%_49_0))
                (=> main@_58_0 (= main@%_59_0 (+ main@%.06.i35_0 1)))
                (=> main@_58_0 (= main@%_60_0 (< main@%.06.i35_0 9)))
                (=> main@_58_0 main@%_60_0)
                (=> main@_58_0 (= main@%_61_0 (* main@%_59_0 10)))
                a!1
                (=> main@_58_0 (or (<= @a_1_0 0) (> main@%_62_0 0)))
                (=> main@_58_0 (> @a_1_0 0))
                (=> main@_58_0
                    (= main@%_63_0 (select main@%shadow.mem.0.1_0 main@%_62_0)))
                a!2
                (=> main@_58_0 (or (<= @a_2_0 0) (> main@%_64_0 0)))
                (=> main@_58_0 (> @a_2_0 0))
                (=> main@_58_0
                    (= main@%_65_0 (select main@%shadow.mem.4.6_0 main@%_64_0)))
                (=> main@_58_0 (= main@%_66_0 (= main@%_63_0 main@%_65_0)))
                (=> main@.lr.ph33_0 (and main@.lr.ph33_0 main@_58_0))
                (=> (and main@.lr.ph33_0 main@_58_0) main@%_66_0)
                (=> (and main@.lr.ph33_0 main@_58_0)
                    (= main@%.06.i35_1 main@%_59_0))
                (=> (and main@.lr.ph33_0 main@_58_0)
                    (= main@%.06.i35_2 main@%.06.i35_1))
                main@.lr.ph33_0)))
  (=> a!3
      (main@.lr.ph33 main@%.06.i35_2
                     @a_1_0
                     main@%shadow.mem.0.1_0
                     @a_2_0
                     main@%shadow.mem.4.6_0
                     main@%loop.bound_0)))))
(rule (let ((a!1 (=> main@_50_0
               (= main@%_53_0 (+ @a_1_0 (* 0 400) (* main@%_52_0 4)))))
      (a!2 (=> main@_50_0
               (= main@%_55_0
                  (+ @a_2_0 (* 0 400) (* main@%.06.i35_0 40) (* main@%_48_0 4))))))
(let ((a!3 (and (main@_47 main@%.07.i532_0
                          main@%.06.i35_0
                          @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%shadow.mem.4.6_0
                          main@%loop.bound_0)
                true
                (= main@%_48_0 (+ main@%.07.i532_0 1))
                (= main@%_49_0 (< main@%.07.i532_0 main@%loop.bound_0))
                (=> main@_50_0 (and main@_50_0 main@_47_0))
                (=> (and main@_50_0 main@_47_0) main@%_49_0)
                (=> main@_50_0 (= main@%_51_0 (+ main@%.07.i532_0 11)))
                a!1
                (=> main@_50_0 (or (<= @a_1_0 0) (> main@%_53_0 0)))
                (=> main@_50_0 (> @a_1_0 0))
                (=> main@_50_0
                    (= main@%_54_0 (select main@%shadow.mem.0.1_0 main@%_53_0)))
                a!2
                (=> main@_50_0 (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@_50_0 (> @a_2_0 0))
                (=> main@_50_0
                    (= main@%_56_0 (select main@%shadow.mem.4.6_0 main@%_55_0)))
                (=> main@_50_0 (= main@%_57_0 (= main@%_54_0 main@%_56_0)))
                (=> main@_47_1 (and main@_47_1 main@_50_0))
                (=> (and main@_47_1 main@_50_0) main@%_57_0)
                (=> (and main@_47_1 main@_50_0)
                    (= main@%.07.i532_1 main@%_48_0))
                (=> (and main@_47_1 main@_50_0)
                    (= main@%.07.i532_2 main@%.07.i532_1))
                main@_47_1)))
  (=> a!3
      (main@_47 main@%.07.i532_2
                main@%.06.i35_0
                @a_1_0
                main@%shadow.mem.0.1_0
                @a_2_0
                main@%shadow.mem.4.6_0
                main@%loop.bound_0)))))
(rule (let ((a!1 (= main@%_62_0 (+ (+ @a_1_0 (* 0 400)) (* main@%_61_0 4))))
      (a!2 (= main@%_64_0 (+ (+ @a_2_0 (* 0 400)) (* main@%_59_0 40) (* 0 4))))
      (a!3 (= main@%_53_0 (+ (+ @a_1_0 (* 0 400)) (* main@%_52_0 4))))
      (a!4 (= main@%_55_0
              (+ (+ @a_2_0 (* 0 400)) (* main@%.06.i35_0 40) (* main@%_48_0 4)))))
(let ((a!5 (and (main@_47 main@%.07.i532_0
                          main@%.06.i35_0
                          @a_1_0
                          main@%shadow.mem.0.1_0
                          @a_2_0
                          main@%shadow.mem.4.6_0
                          main@%loop.bound_0)
                true
                (= main@%_48_0 (+ main@%.07.i532_0 1))
                (= main@%_49_0 (< main@%.07.i532_0 main@%loop.bound_0))
                (=> main@_58_0 (and main@_58_0 main@_47_0))
                (=> (and main@_58_0 main@_47_0) (not main@%_49_0))
                (=> main@_58_0 (= main@%_59_0 (+ main@%.06.i35_0 1)))
                (=> main@_58_0 (= main@%_60_0 (< main@%.06.i35_0 9)))
                (=> main@_58_0 main@%_60_0)
                (=> main@_58_0 (= main@%_61_0 (* main@%_59_0 10)))
                (=> main@_58_0 a!1)
                (=> main@_58_0 (or (<= @a_1_0 0) (> main@%_62_0 0)))
                (=> main@_58_0 (> @a_1_0 0))
                (=> main@_58_0
                    (= main@%_63_0 (select main@%shadow.mem.0.1_0 main@%_62_0)))
                (=> main@_58_0 a!2)
                (=> main@_58_0 (or (<= @a_2_0 0) (> main@%_64_0 0)))
                (=> main@_58_0 (> @a_2_0 0))
                (=> main@_58_0
                    (= main@%_65_0 (select main@%shadow.mem.4.6_0 main@%_64_0)))
                (=> main@_58_0 (= main@%_66_0 (= main@%_63_0 main@%_65_0)))
                (=> main@_50_0 (and main@_50_0 main@_47_0))
                (=> (and main@_50_0 main@_47_0) main@%_49_0)
                (=> main@_50_0 (= main@%_51_0 (+ main@%.07.i532_0 11)))
                (=> main@_50_0 a!3)
                (=> main@_50_0 (or (<= @a_1_0 0) (> main@%_53_0 0)))
                (=> main@_50_0 (> @a_1_0 0))
                (=> main@_50_0
                    (= main@%_54_0 (select main@%shadow.mem.0.1_0 main@%_53_0)))
                (=> main@_50_0 a!4)
                (=> main@_50_0 (or (<= @a_2_0 0) (> main@%_55_0 0)))
                (=> main@_50_0 (> @a_2_0 0))
                (=> main@_50_0
                    (= main@%_56_0 (select main@%shadow.mem.4.6_0 main@%_55_0)))
                (=> main@_50_0 (= main@%_57_0 (= main@%_54_0 main@%_56_0)))
                (=> |tuple(main@_58_0, main@verifier.error_0)| main@_58_0)
                (=> |tuple(main@_50_0, main@verifier.error_0)| main@_50_0)
                (=> main@verifier.error_0
                    (or |tuple(main@_58_0, main@verifier.error_0)|
                        |tuple(main@_50_0, main@verifier.error_0)|))
                (=> |tuple(main@_58_0, main@verifier.error_0)|
                    (not main@%_66_0))
                (=> |tuple(main@_50_0, main@verifier.error_0)|
                    (not main@%_57_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!5 main@verifier.error.split))))
(query main@verifier.error.split)

