; ModuleID = 'conditional.8e87b399a02cd757-cgu.0'
source_filename = "conditional.8e87b399a02cd757-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define i32 @get_discount(i32 %age) unnamed_addr #0 {
start:
  %ret_val = alloca [4 x i8], align 4
  store i32 0, ptr %ret_val, align 4
  %_3 = icmp sge i32 %age, 65
  br i1 %_3, label %bb1, label %bb2

bb2:                                              ; preds = %start
  %_4 = icmp sle i32 %age, 12
  br i1 %_4, label %bb3, label %bb4

bb1:                                              ; preds = %start
  store i32 20, ptr %ret_val, align 4
  br label %bb4

bb4:                                              ; preds = %bb1, %bb3, %bb2
  %_0 = load i32, ptr %ret_val, align 4
  ret i32 %_0

bb3:                                              ; preds = %bb2
  store i32 50, ptr %ret_val, align 4
  br label %bb4
}

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
