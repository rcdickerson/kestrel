; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %x) unnamed_addr #0 !dbg !7 {
start:
  %x.dbg.spill = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  %y = alloca [4 x i8], align 4
  store i32 %x, ptr %x.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !17, metadata !DIExpression()), !dbg !23
  call void @llvm.dbg.declare(metadata ptr %y, metadata !15, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.declare(metadata ptr %i, metadata !19, metadata !DIExpression()), !dbg !25
  store i32 0, ptr %y, align 4, !dbg !26
  store i32 0, ptr %i, align 4, !dbg !27
  br label %bb1, !dbg !28

bb1:                                              ; preds = %bb2, %start
  %_5 = load i32, ptr %i, align 4, !dbg !29
  %_4 = icmp slt i32 %_5, %x, !dbg !29
  br i1 %_4, label %bb2, label %bb3, !dbg !29

bb3:                                              ; preds = %bb1
  %_8 = load i32, ptr %y, align 4, !dbg !30
  %0 = mul i32 %_8, 2, !dbg !31
  store i32 %0, ptr %y, align 4, !dbg !31
  ret void, !dbg !32

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %y, align 4, !dbg !34
  %1 = add i32 %_6, %x, !dbg !35
  store i32 %1, ptr %y, align 4, !dbg !35
  %_7 = load i32, ptr %i, align 4, !dbg !36
  %2 = add i32 %_7, 1, !dbg !37
  store i32 %2, ptr %i, align 4, !dbg !37
  br label %bb1, !dbg !28
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
!6 = !DIFile(filename: "llvm-examples/shemer/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !21, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/shemer/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "67cd1fc8e57517368c9ceb6d33d7d872")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !17, !19}
!14 = !DILocalVariable(name: "x", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "y", scope: !16, file: !8, line: 3, type: !12, align: 32)
!16 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!17 = !DILocalVariable(name: "z", scope: !18, file: !8, line: 4, type: !12, align: 32)
!18 = distinct !DILexicalBlock(scope: !16, file: !8, line: 4, column: 5)
!19 = !DILocalVariable(name: "i", scope: !20, file: !8, line: 5, type: !12, align: 32)
!20 = distinct !DILexicalBlock(scope: !18, file: !8, line: 5, column: 5)
!21 = !{}
!22 = !DILocation(line: 2, column: 14, scope: !7)
!23 = !DILocation(line: 4, column: 9, scope: !18)
!24 = !DILocation(line: 3, column: 9, scope: !16)
!25 = !DILocation(line: 5, column: 9, scope: !20)
!26 = !DILocation(line: 3, column: 17, scope: !7)
!27 = !DILocation(line: 5, column: 17, scope: !18)
!28 = !DILocation(line: 7, column: 5, scope: !20)
!29 = !DILocation(line: 7, column: 11, scope: !20)
!30 = !DILocation(line: 11, column: 9, scope: !20)
!31 = !DILocation(line: 11, column: 5, scope: !20)
!32 = !DILocation(line: 12, column: 2, scope: !33)
!33 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!34 = !DILocation(line: 8, column: 13, scope: !20)
!35 = !DILocation(line: 8, column: 9, scope: !20)
!36 = !DILocation(line: 9, column: 13, scope: !20)
!37 = !DILocation(line: 9, column: 9, scope: !20)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
