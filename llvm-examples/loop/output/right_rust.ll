; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_72b76b03aa3be83f823e552e2267c704 = private unnamed_addr constant [28 x i8] c"llvm-examples/loop/right.rs\00", align 1
@alloc_cec36e1e6db6a74003dcc27714188173 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_72b76b03aa3be83f823e552e2267c704, [16 x i8] c"\1B\00\00\00\00\00\00\00\05\00\00\00\0F\00\00\00" }>, align 8
@alloc_83591e49dc36b934441419653b8254c2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_72b76b03aa3be83f823e552e2267c704, [16 x i8] c"\1B\00\00\00\00\00\00\00\06\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %n) unnamed_addr #0 !dbg !7 {
start:
  %n.dbg.spill = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  %sum = alloca [4 x i8], align 4
  store i32 %n, ptr %n.dbg.spill, align 4
    #dbg_declare(ptr %n.dbg.spill, !14, !DIExpression(), !20)
    #dbg_declare(ptr %sum, !15, !DIExpression(), !21)
    #dbg_declare(ptr %i, !17, !DIExpression(), !22)
  store i32 0, ptr %sum, align 4, !dbg !23
  store i32 1, ptr %i, align 4, !dbg !24
  br label %bb1, !dbg !25

bb1:                                              ; preds = %bb4, %start
  %_5 = load i32, ptr %i, align 4, !dbg !26
  %_4 = icmp sle i32 %_5, %n, !dbg !27
  br i1 %_4, label %bb2, label %bb5, !dbg !27

bb5:                                              ; preds = %bb1
  ret void, !dbg !28

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %sum, align 4, !dbg !30
  %_7 = load i32, ptr %i, align 4, !dbg !31
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_6, i32 %_7), !dbg !30
  %_8.0 = extractvalue { i32, i1 } %0, 0, !dbg !30
  %_8.1 = extractvalue { i32, i1 } %0, 1, !dbg !30
  br i1 %_8.1, label %panic, label %bb3, !dbg !30

bb3:                                              ; preds = %bb2
  store i32 %_8.0, ptr %sum, align 4, !dbg !32
  %_9 = load i32, ptr %i, align 4, !dbg !33
  %1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_9, i32 1), !dbg !33
  %_10.0 = extractvalue { i32, i1 } %1, 0, !dbg !33
  %_10.1 = extractvalue { i32, i1 } %1, 1, !dbg !33
  br i1 %_10.1, label %panic1, label %bb4, !dbg !33

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_cec36e1e6db6a74003dcc27714188173) #3, !dbg !30
  unreachable, !dbg !30

bb4:                                              ; preds = %bb3
  store i32 %_10.0, ptr %i, align 4, !dbg !34
  br label %bb1, !dbg !25

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_83591e49dc36b934441419653b8254c2) #3, !dbg !33
  unreachable, !dbg !33
}

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
!6 = !DIFile(filename: "llvm-examples/loop/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !19, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/loop/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "46a3e53296eec80054acf024c33394a4")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !17}
!14 = !DILocalVariable(name: "n", arg: 1, scope: !7, file: !8, line: 1, type: !12)
!15 = !DILocalVariable(name: "sum", scope: !16, file: !8, line: 2, type: !12, align: 32)
!16 = distinct !DILexicalBlock(scope: !7, file: !8, line: 2, column: 5)
!17 = !DILocalVariable(name: "i", scope: !18, file: !8, line: 3, type: !12, align: 32)
!18 = distinct !DILexicalBlock(scope: !16, file: !8, line: 3, column: 5)
!19 = !{}
!20 = !DILocation(line: 1, column: 27, scope: !7)
!21 = !DILocation(line: 2, column: 9, scope: !16)
!22 = !DILocation(line: 3, column: 9, scope: !18)
!23 = !DILocation(line: 2, column: 19, scope: !7)
!24 = !DILocation(line: 3, column: 17, scope: !16)
!25 = !DILocation(line: 4, column: 5, scope: !18)
!26 = !DILocation(line: 4, column: 12, scope: !18)
!27 = !DILocation(line: 4, column: 11, scope: !18)
!28 = !DILocation(line: 8, column: 2, scope: !29)
!29 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!30 = !DILocation(line: 5, column: 15, scope: !18)
!31 = !DILocation(line: 5, column: 21, scope: !18)
!32 = !DILocation(line: 5, column: 9, scope: !18)
!33 = !DILocation(line: 6, column: 13, scope: !18)
!34 = !DILocation(line: 6, column: 9, scope: !18)
