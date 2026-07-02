; ModuleID = 'loop.4ec5acff3b6ddb15-cgu.0'
source_filename = "loop.4ec5acff3b6ddb15-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_e2b9f373b3385bf1dfe1d5657c591caa = private unnamed_addr constant [27 x i8] c"llvm-examples/loop/loop.rs\00", align 1
@alloc_ff438de2926f93a88d97a4d20a267937 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_e2b9f373b3385bf1dfe1d5657c591caa, [16 x i8] c"\1A\00\00\00\00\00\00\00\05\00\00\00\0F\00\00\00" }>, align 8
@alloc_1d4ac44ac6ce4dfa37017d5355a98ab8 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_e2b9f373b3385bf1dfe1d5657c591caa, [16 x i8] c"\1A\00\00\00\00\00\00\00\06\00\00\00\0D\00\00\00" }>, align 8

; loop::sum_to_n
; Function Attrs: nounwind nonlazybind uwtable
define i32 @_ZN4loop8sum_to_n17h1dd796fbd7a45127E(i32 %n) unnamed_addr #0 {
start:
  %i = alloca [4 x i8], align 4
  %sum = alloca [4 x i8], align 4
  store i32 0, ptr %sum, align 4
  store i32 1, ptr %i, align 4
  br label %bb1

bb1:                                              ; preds = %bb4, %start
  %_5 = load i32, ptr %i, align 4
  %_4 = icmp sle i32 %_5, %n
  br i1 %_4, label %bb2, label %bb5

bb5:                                              ; preds = %bb1
  %_0 = load i32, ptr %sum, align 4
  ret i32 %_0

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %sum, align 4
  %_7 = load i32, ptr %i, align 4
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_6, i32 %_7)
  %_8.0 = extractvalue { i32, i1 } %0, 0
  %_8.1 = extractvalue { i32, i1 } %0, 1
  br i1 %_8.1, label %panic, label %bb3

bb3:                                              ; preds = %bb2
  store i32 %_8.0, ptr %sum, align 4
  %_9 = load i32, ptr %i, align 4
  %1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_9, i32 1)
  %_10.0 = extractvalue { i32, i1 } %1, 0
  %_10.1 = extractvalue { i32, i1 } %1, 1
  br i1 %_10.1, label %panic1, label %bb4

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_ff438de2926f93a88d97a4d20a267937) #3
  unreachable

bb4:                                              ; preds = %bb3
  store i32 %_10.0, ptr %i, align 4
  br label %bb1

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_1d4ac44ac6ce4dfa37017d5355a98ab8) #3
  unreachable
}

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
