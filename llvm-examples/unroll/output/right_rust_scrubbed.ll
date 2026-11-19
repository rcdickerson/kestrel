; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_18989b541471998acea3ba6b5f4461ab = private unnamed_addr constant [30 x i8] c"llvm-examples/unroll/right.rs\00", align 1
@alloc_008eee418d4229b5969b3d61ddac92ee = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_18989b541471998acea3ba6b5f4461ab, [16 x i8] c"\1D\00\00\00\00\00\00\00\06\00\00\00\0D\00\00\00" }>, align 8
@alloc_f5fb85dd27a38af5b5bac898394b9cbc = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_18989b541471998acea3ba6b5f4461ab, [16 x i8] c"\1D\00\00\00\00\00\00\00\07\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %N) unnamed_addr #0 !dbg !7 {
start:
  %N.dbg.spill = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  %x = alloca [4 x i8], align 4
  store i32 %N, ptr %N.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %N.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !20
  call void @llvm.dbg.declare(metadata ptr %x, metadata !15, metadata !DIExpression()), !dbg !21
  call void @llvm.dbg.declare(metadata ptr %i, metadata !17, metadata !DIExpression()), !dbg !22
  store i32 0, ptr %x, align 4, !dbg !23
  store i32 1, ptr %i, align 4, !dbg !24
  br label %bb1, !dbg !25

bb1:                                              ; preds = %bb4, %start
  %_5 = load i32, ptr %i, align 4, !dbg !26
  %_4 = icmp sle i32 %_5, %N, !dbg !26
  br i1 %_4, label %bb2, label %bb5, !dbg !26

bb5:                                              ; preds = %bb1
  ret void, !dbg !27

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %x, align 4, !dbg !28
  %_7 = load i32, ptr %i, align 4, !dbg !29
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_6, i32 %_7), !dbg !28
  %_8.0 = extractvalue { i32, i1 } %0, 0, !dbg !28
  %_8.1 = extractvalue { i32, i1 } %0, 1, !dbg !28
  br i1 %_8.1, label %panic, label %bb3, !dbg !28

bb3:                                              ; preds = %bb2
  store i32 %_8.0, ptr %x, align 4, !dbg !30
  %_9 = load i32, ptr %i, align 4, !dbg !31
  %1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_9, i32 1), !dbg !31
  %_10.0 = extractvalue { i32, i1 } %1, 0, !dbg !31
  %_10.1 = extractvalue { i32, i1 } %1, 1, !dbg !31
  br i1 %_10.1, label %panic1, label %bb4, !dbg !31

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_008eee418d4229b5969b3d61ddac92ee) #3, !dbg !28
  unreachable, !dbg !28

bb4:                                              ; preds = %bb3
  store i32 %_10.0, ptr %i, align 4, !dbg !32
  br label %bb1, !dbg !25

panic1:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_f5fb85dd27a38af5b5bac898394b9cbc) #3, !dbg !31
  unreachable, !dbg !31
}

; Function Attrs: nosync nounwind speculatable
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nosync nounwind speculatable }
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
!6 = !DIFile(filename: "llvm-examples/unroll/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !19, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/unroll/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "44b17b6fdb5896f4e1a6b0bf5ccd63ec")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !17}
!14 = !DILocalVariable(name: "N", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "x", scope: !16, file: !8, line: 3, type: !12, align: 32)
!16 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!17 = !DILocalVariable(name: "i", scope: !18, file: !8, line: 4, type: !12, align: 32)
!18 = distinct !DILexicalBlock(scope: !16, file: !8, line: 4, column: 5)
!19 = !{}
!20 = !DILocation(line: 2, column: 14, scope: !7)
!21 = !DILocation(line: 3, column: 9, scope: !16)
!22 = !DILocation(line: 4, column: 9, scope: !18)
!23 = !DILocation(line: 3, column: 17, scope: !7)
!24 = !DILocation(line: 4, column: 17, scope: !16)
!25 = !DILocation(line: 5, column: 5, scope: !18)
!26 = !DILocation(line: 5, column: 11, scope: !18)
!27 = !DILocation(line: 9, column: 2, scope: !7)
!28 = !DILocation(line: 6, column: 13, scope: !18)
!29 = !DILocation(line: 6, column: 17, scope: !18)
!30 = !DILocation(line: 6, column: 9, scope: !18)
!31 = !DILocation(line: 7, column: 13, scope: !18)
!32 = !DILocation(line: 7, column: 9, scope: !18)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
