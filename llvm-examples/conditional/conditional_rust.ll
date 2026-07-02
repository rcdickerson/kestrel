; ModuleID = 'conditional.8e87b399a02cd757-cgu.0'
source_filename = "conditional.8e87b399a02cd757-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; conditional::get_discount
; Function Attrs: nounwind nonlazybind uwtable
define i32 @_ZN11conditional12get_discount17hf7838d63c204e4bcE(i32 %age) unnamed_addr #0 {
start:
  %_0 = alloca [4 x i8], align 4
  %_2 = icmp sge i32 %age, 65
  br i1 %_2, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %_3 = icmp sle i32 %age, 12
  br i1 %_3, label %bb3, label %bb4

bb1:                                              ; preds = %start
  store i32 20, ptr %_0, align 4
  br label %bb5

bb4:                                              ; preds = %bb2
  store i32 0, ptr %_0, align 4
  br label %bb5

bb3:                                              ; preds = %bb2
  store i32 50, ptr %_0, align 4
  br label %bb5

bb5:                                              ; preds = %bb1, %bb3, %bb4
  %0 = load i32, ptr %_0, align 4
  ret i32 %0
}

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
