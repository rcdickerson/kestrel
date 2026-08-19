; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %B, i32 %C, i32 %N, i32 %0) unnamed_addr #0 !dbg !7 {
start:
  %N.dbg.spill = alloca [4 x i8], align 4
  %C.dbg.spill = alloca [4 x i8], align 4
  %B.dbg.spill = alloca [4 x i8], align 4
  %j = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  %x = alloca [4 x i8], align 4
  store i32 %0, ptr %x, align 4
  store i32 %B, ptr %B.dbg.spill, align 4
    #dbg_declare(ptr %B.dbg.spill, !14, !DIExpression(), !23)
  store i32 %C, ptr %C.dbg.spill, align 4
    #dbg_declare(ptr %C.dbg.spill, !15, !DIExpression(), !24)
  store i32 %N, ptr %N.dbg.spill, align 4
    #dbg_declare(ptr %N.dbg.spill, !16, !DIExpression(), !25)
    #dbg_declare(ptr %x, !17, !DIExpression(), !26)
    #dbg_declare(ptr %i, !18, !DIExpression(), !27)
    #dbg_declare(ptr %j, !20, !DIExpression(), !28)
  store i32 0, ptr %i, align 4, !dbg !29
  store i32 %C, ptr %j, align 4, !dbg !30
  br label %bb1, !dbg !31

bb1:                                              ; preds = %bb2, %start
  %_8 = load i32, ptr %i, align 4, !dbg !32
  %_7 = icmp slt i32 %_8, %N, !dbg !32
  br i1 %_7, label %bb2, label %bb3, !dbg !32

bb3:                                              ; preds = %bb1
  ret void, !dbg !33

bb2:                                              ; preds = %bb1
  %_9 = load i32, ptr %x, align 4, !dbg !34
  %_10 = load i32, ptr %j, align 4, !dbg !35
  %1 = add i32 %_9, %_10, !dbg !36
  store i32 %1, ptr %x, align 4, !dbg !36
  %_11 = load i32, ptr %j, align 4, !dbg !37
  %2 = add i32 %_11, %B, !dbg !38
  store i32 %2, ptr %j, align 4, !dbg !38
  %_12 = load i32, ptr %i, align 4, !dbg !39
  %3 = add i32 %_12, 1, !dbg !40
  store i32 %3, ptr %i, align 4, !dbg !40
  br label %bb1, !dbg !31
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
!6 = !DIFile(filename: "llvm-examples/strength-reduction/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !22, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/strength-reduction/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "bcba7024a7bb173f407fa938c52ca036")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12, !12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !16, !17, !18, !20}
!14 = !DILocalVariable(name: "B", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "C", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!16 = !DILocalVariable(name: "N", arg: 3, scope: !7, file: !8, line: 2, type: !12)
!17 = !DILocalVariable(name: "x", arg: 4, scope: !7, file: !8, line: 2, type: !12)
!18 = !DILocalVariable(name: "i", scope: !19, file: !8, line: 3, type: !12, align: 32)
!19 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!20 = !DILocalVariable(name: "j", scope: !21, file: !8, line: 4, type: !12, align: 32)
!21 = distinct !DILexicalBlock(scope: !19, file: !8, line: 4, column: 5)
!22 = !{}
!23 = !DILocation(line: 2, column: 14, scope: !7)
!24 = !DILocation(line: 2, column: 22, scope: !7)
!25 = !DILocation(line: 2, column: 30, scope: !7)
!26 = !DILocation(line: 2, column: 38, scope: !7)
!27 = !DILocation(line: 3, column: 9, scope: !19)
!28 = !DILocation(line: 4, column: 9, scope: !21)
!29 = !DILocation(line: 3, column: 17, scope: !7)
!30 = !DILocation(line: 4, column: 17, scope: !19)
!31 = !DILocation(line: 5, column: 5, scope: !21)
!32 = !DILocation(line: 5, column: 11, scope: !21)
!33 = !DILocation(line: 10, column: 2, scope: !7)
!34 = !DILocation(line: 6, column: 13, scope: !21)
!35 = !DILocation(line: 6, column: 17, scope: !21)
!36 = !DILocation(line: 6, column: 9, scope: !21)
!37 = !DILocation(line: 7, column: 13, scope: !21)
!38 = !DILocation(line: 7, column: 9, scope: !21)
!39 = !DILocation(line: 8, column: 13, scope: !21)
!40 = !DILocation(line: 8, column: 9, scope: !21)
