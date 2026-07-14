; ModuleID = 'arithmetic.a049be47490e3f75-cgu.0'
source_filename = "arithmetic.a049be47490e3f75-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define i32 @compute_rust(i32 %a, i32 %b, i32 %c) unnamed_addr #0 {
start:
  %sum = add i32 %a, %b
  %prod = mul i32 %sum, %c
  ret i32 %prod
}

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{!"rustc version 1.96.0 (ac68faa20 2026-05-25)"}
