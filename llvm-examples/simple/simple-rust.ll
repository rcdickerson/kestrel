; ModuleID = 'simple.1b5b82a4b977db3-cgu.0'
source_filename = "simple.1b5b82a4b977db3-cgu.0"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx11.0.0"

@alloc_52fb0c84ea436fa453ba5f5c783273d8 = private unnamed_addr constant <{ [9 x i8] }> <{ [9 x i8] c"simple.rs" }>, align 1
@alloc_9bc7c6f5cf931fb741be5df83272eb0a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_52fb0c84ea436fa453ba5f5c783273d8, [16 x i8] c"\09\00\00\00\00\00\00\00\02\00\00\00\03\00\00\00" }>, align 8

; Function Attrs: uwtable
define i32 @add_one(i32 %x) unnamed_addr #0 {
start:
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %x, i32 1)
  %_2.0 = extractvalue { i32, i1 } %0, 0
  %_2.1 = extractvalue { i32, i1 } %0, 1
  br i1 %_2.1, label %panic, label %bb1

bb1:                                              ; preds = %start
  ret i32 %_2.0

panic:                                            ; preds = %start
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h3576f6fcd4ff2b72E(ptr align 8 @alloc_9bc7c6f5cf931fb741be5df83272eb0a) #3
  unreachable
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn uwtable
declare void @_ZN4core9panicking11panic_const24panic_const_add_overflow17h3576f6fcd4ff2b72E(ptr align 8) unnamed_addr #2

attributes #0 = { uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { cold noinline noreturn uwtable "frame-pointer"="non-leaf" "probe-stack"="inline-asm" "target-cpu"="apple-m1" }
attributes #3 = { noreturn }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{!"rustc version 1.86.0 (05f9846f8 2025-03-31) (Homebrew)"}
