; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_d58fd7249401e5d7b0f8a03dedaf138b = private unnamed_addr constant [34 x i8] c"llvm-examples/square-sum/right.rs\00", align 1
@alloc_179c49ada6cb72719bfa512ac4b1923a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d58fd7249401e5d7b0f8a03dedaf138b, [16 x i8] c"!\00\00\00\00\00\00\00\05\00\00\00\11\00\00\00" }>, align 8
@alloc_08ea59b51ec41ad24b2b5eec37f3909f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d58fd7249401e5d7b0f8a03dedaf138b, [16 x i8] c"!\00\00\00\00\00\00\00\05\00\00\00\0D\00\00\00" }>, align 8
@alloc_ec107ee395ac6b4ecf0fa2ec2dc85880 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d58fd7249401e5d7b0f8a03dedaf138b, [16 x i8] c"!\00\00\00\00\00\00\00\06\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %0, i32 %b) unnamed_addr #0 !dbg !7 {
start:
  %b.dbg.spill = alloca [4 x i8], align 4
  %c = alloca [4 x i8], align 4
  %a = alloca [4 x i8], align 4
  store i32 %0, ptr %a, align 4
    #dbg_declare(ptr %a, !14, !DIExpression(), !19)
  store i32 %b, ptr %b.dbg.spill, align 4
    #dbg_declare(ptr %b.dbg.spill, !15, !DIExpression(), !20)
    #dbg_declare(ptr %c, !16, !DIExpression(), !21)
  store i32 0, ptr %c, align 4, !dbg !22
  br label %bb1, !dbg !23

bb1:                                              ; preds = %bb5, %start
  %_5 = load i32, ptr %a, align 4, !dbg !24
  %_4 = icmp slt i32 %_5, %b, !dbg !24
  br i1 %_4, label %bb2, label %bb6, !dbg !24

bb6:                                              ; preds = %bb1
  ret void, !dbg !25

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %c, align 4, !dbg !26
  %_8 = load i32, ptr %a, align 4, !dbg !27
  %_9 = load i32, ptr %a, align 4, !dbg !28
  %1 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %_8, i32 %_9), !dbg !29
  %_10.0 = extractvalue { i32, i1 } %1, 0, !dbg !29
  %_10.1 = extractvalue { i32, i1 } %1, 1, !dbg !29
  br i1 %_10.1, label %panic, label %bb3, !dbg !29

bb3:                                              ; preds = %bb2
  %2 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_6, i32 %_10.0), !dbg !26
  %_11.0 = extractvalue { i32, i1 } %2, 0, !dbg !26
  %_11.1 = extractvalue { i32, i1 } %2, 1, !dbg !26
  br i1 %_11.1, label %panic1, label %bb4, !dbg !26

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8 @alloc_179c49ada6cb72719bfa512ac4b1923a) #3, !dbg !29
  unreachable, !dbg !29

bb4:                                              ; preds = %bb3
  store i32 %_11.0, ptr %c, align 4, !dbg !30
  %_12 = load i32, ptr %a, align 4, !dbg !31
  %3 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_12, i32 1), !dbg !31
  %_13.0 = extractvalue { i32, i1 } %3, 0, !dbg !31
  %_13.1 = extractvalue { i32, i1 } %3, 1, !dbg !31
  br i1 %_13.1, label %panic2, label %bb5, !dbg !31

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_08ea59b51ec41ad24b2b5eec37f3909f) #3, !dbg !26
  unreachable, !dbg !26

bb5:                                              ; preds = %bb4
  store i32 %_13.0, ptr %a, align 4, !dbg !32
  br label %bb1, !dbg !23

panic2:                                           ; preds = %bb4
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_ec107ee395ac6b4ecf0fa2ec2dc85880) #3, !dbg !31
  unreachable, !dbg !31
}

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8) unnamed_addr #2

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!llvm.dbg.cu = !{!5}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"Dwarf Version", i32 4}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{!"rustc version 1.97.0 (2d8144b78 2026-07-07)"}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6, producer: "clang LLVM (rustc version 1.97.0 (2d8144b78 2026-07-07))", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!6 = !DIFile(filename: "llvm-examples/square-sum/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !18, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/square-sum/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "3f803fbb68acba81f0bfe6ec1dd3c5a8")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !16}
!14 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!16 = !DILocalVariable(name: "c", scope: !17, file: !8, line: 3, type: !12, align: 32)
!17 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!18 = !{}
!19 = !DILocation(line: 2, column: 14, scope: !7)
!20 = !DILocation(line: 2, column: 26, scope: !7)
!21 = !DILocation(line: 3, column: 9, scope: !17)
!22 = !DILocation(line: 3, column: 17, scope: !7)
!23 = !DILocation(line: 4, column: 5, scope: !17)
!24 = !DILocation(line: 4, column: 11, scope: !17)
!25 = !DILocation(line: 8, column: 2, scope: !7)
!26 = !DILocation(line: 5, column: 13, scope: !17)
!27 = !DILocation(line: 5, column: 18, scope: !17)
!28 = !DILocation(line: 5, column: 22, scope: !17)
!29 = !DILocation(line: 5, column: 17, scope: !17)
!30 = !DILocation(line: 5, column: 9, scope: !17)
!31 = !DILocation(line: 6, column: 13, scope: !17)
!32 = !DILocation(line: 6, column: 9, scope: !17)
