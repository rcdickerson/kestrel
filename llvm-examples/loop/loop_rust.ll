; ModuleID = 'loop.4ec5acff3b6ddb15-cgu.0'
source_filename = "loop.4ec5acff3b6ddb15-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define i32 @sum_to_n(i32 %n) unnamed_addr #0 {
start:
  %i = alloca [4 x i8], align 4
  %sum = alloca [4 x i8], align 4
  store i32 0, ptr %sum, align 4
  store i32 1, ptr %i, align 4
  br label %bb1

bb1:                                              ; preds = %bb2, %start
  %_5 = load i32, ptr %i, align 4
  %_4 = icmp sle i32 %_5, %n
  br i1 %_4, label %bb2, label %bb3

bb3:                                              ; preds = %bb1
  %_0 = load i32, ptr %sum, align 4
  ret i32 %_0

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %sum, align 4
  %_7 = load i32, ptr %i, align 4
  %0 = add i32 %_6, %_7
  store i32 %0, ptr %sum, align 4
  %_8 = load i32, ptr %i, align 4
  %1 = add i32 %_8, 1
  store i32 %1, ptr %i, align 4
  br label %bb1
}

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
