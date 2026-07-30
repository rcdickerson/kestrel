; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %0, i32 %b) unnamed_addr #0 !dbg !7 {
start:
  %b.dbg.spill = alloca [4 x i8], align 4
  %c = alloca [4 x i8], align 4
  %a = alloca [4 x i8], align 4
  store i32 %0, ptr %a, align 4
  call void @llvm.dbg.declare(metadata ptr %a, metadata !14, metadata !DIExpression()), !dbg !19
  store i32 %b, ptr %b.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %b.dbg.spill, metadata !15, metadata !DIExpression()), !dbg !20
  call void @llvm.dbg.declare(metadata ptr %c, metadata !16, metadata !DIExpression()), !dbg !21
  store i32 0, ptr %c, align 4, !dbg !22
  br label %bb1, !dbg !23

bb1:                                              ; preds = %bb2, %start
  %_5 = load i32, ptr %a, align 4, !dbg !24
  %_4 = icmp slt i32 %_5, %b, !dbg !24
  br i1 %_4, label %bb2, label %bb3, !dbg !24

bb3:                                              ; preds = %bb1
  ret void, !dbg !25

bb2:                                              ; preds = %bb1
  %_6 = load i32, ptr %c, align 4, !dbg !26
  %_8 = load i32, ptr %a, align 4, !dbg !27
  %_9 = load i32, ptr %a, align 4, !dbg !28
  %_7 = mul i32 %_8, %_9, !dbg !29
  %1 = add i32 %_6, %_7, !dbg !30
  store i32 %1, ptr %c, align 4, !dbg !30
  %_10 = load i32, ptr %a, align 4, !dbg !31
  %2 = add i32 %_10, 1, !dbg !32
  store i32 %2, ptr %a, align 4, !dbg !32
  br label %bb1, !dbg !23
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
!6 = !DIFile(filename: "llvm-examples/square-sum/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !18, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/square-sum/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "0b684a6dd08f3451c52a49b4d9160660")
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

declare void @llvm.dbg.declare(metadata, metadata, metadata)
