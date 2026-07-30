; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %n) unnamed_addr #0 !dbg !7 {
start:
  %n.dbg.spill = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  %sum = alloca [4 x i8], align 4
  store i32 %n, ptr %n.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !20
  call void @llvm.dbg.declare(metadata ptr %sum, metadata !15, metadata !DIExpression()), !dbg !21
  call void @llvm.dbg.declare(metadata ptr %i, metadata !17, metadata !DIExpression()), !dbg !22
  store i32 0, ptr %sum, align 4, !dbg !23
  store i32 1, ptr %i, align 4, !dbg !24
  br label %bb1, !dbg !25

bb1:                                              ; preds = %bb2, %start
  %_5 = load i32, ptr %i, align 4, !dbg !26
  %_4 = icmp sle i32 %_5, %n, !dbg !27
  br i1 %_4, label %bb2, label %bb3, !dbg !27

bb3:                                              ; preds = %bb1
  ret void, !dbg !28

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %sum, align 4, !dbg !30
  %_7 = load i32, ptr %i, align 4, !dbg !31
  %0 = add i32 %_6, %_7, !dbg !32
  store i32 %0, ptr %sum, align 4, !dbg !32
  %_8 = load i32, ptr %i, align 4, !dbg !33
  %1 = add i32 %_8, 1, !dbg !34
  store i32 %1, ptr %i, align 4, !dbg !34
  br label %bb1, !dbg !25
}

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

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

declare void @llvm.dbg.declare(metadata, metadata, metadata)
