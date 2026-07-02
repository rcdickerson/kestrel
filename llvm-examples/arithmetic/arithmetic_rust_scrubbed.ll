; ModuleID = 'arithmetic.a049be47490e3f75-cgu.0'
source_filename = "arithmetic.a049be47490e3f75-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_899392582b7fde1bab3c6663c0b7cee1 = private unnamed_addr constant [39 x i8] c"llvm-examples/arithmetic/arithmetic.rs\00", align 1
@alloc_9b398cbf6e12c203b55e61d4308a0691 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_899392582b7fde1bab3c6663c0b7cee1, [16 x i8] c"&\00\00\00\00\00\00\00\02\00\00\00\0F\00\00\00" }>, align 8
@alloc_3f2ff58dc16902889f3ba955cd8b5da9 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_899392582b7fde1bab3c6663c0b7cee1, [16 x i8] c"&\00\00\00\00\00\00\00\03\00\00\00\10\00\00\00" }>, align 8

; arithmetic::compute
; Function Attrs: nounwind nonlazybind uwtable
define i32 @_ZN10arithmetic7compute17ha86421f09ea0b53eE(i32 %a, i32 %b, i32 %c) unnamed_addr #0 {
start:
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %a, i32 %b)
  %_5.0 = extractvalue { i32, i1 } %0, 0
  %_5.1 = extractvalue { i32, i1 } %0, 1
  br i1 %_5.1, label %panic, label %bb1

bb1:                                              ; preds = %start
  %1 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %_5.0, i32 %c)
  %_6.0 = extractvalue { i32, i1 } %1, 0
  %_6.1 = extractvalue { i32, i1 } %1, 1
  br i1 %_6.1, label %panic1, label %bb2

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_9b398cbf6e12c203b55e61d4308a0691) #3
  unreachable

bb2:                                              ; preds = %bb1
  ret i32 %_6.0

panic1:                                           ; preds = %bb1
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8 @alloc_3f2ff58dc16902889f3ba955cd8b5da9) #3
  unreachable
}

; Function Attrs: nosync nounwind speculatable
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

; Function Attrs: nosync nounwind speculatable
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCs27Vx93FoQ6z_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nosync nounwind speculatable }
attributes #2 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
