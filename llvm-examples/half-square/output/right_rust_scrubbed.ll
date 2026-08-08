; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %low, i32 %h) unnamed_addr #0 !dbg !7 {
start:
  %h.dbg.spill = alloca [4 x i8], align 4
  %low.dbg.spill = alloca [4 x i8], align 4
  %v = alloca [4 x i8], align 4
  %y = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  store i32 %low, ptr %low.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %low.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !23
  store i32 %h, ptr %h.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %h.dbg.spill, metadata !15, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.declare(metadata ptr %i, metadata !16, metadata !DIExpression()), !dbg !25
  call void @llvm.dbg.declare(metadata ptr %y, metadata !18, metadata !DIExpression()), !dbg !26
  call void @llvm.dbg.declare(metadata ptr %v, metadata !20, metadata !DIExpression()), !dbg !27
  store i32 0, ptr %i, align 4, !dbg !28
  store i32 0, ptr %y, align 4, !dbg !29
  store i32 0, ptr %v, align 4, !dbg !30
  br label %bb1, !dbg !31

bb1:                                              ; preds = %bb2, %start
  %_7 = load i32, ptr %i, align 4, !dbg !32
  %_6 = icmp sgt i32 %h, %_7, !dbg !33
  br i1 %_6, label %bb2, label %bb3, !dbg !33

bb3:                                              ; preds = %bb1
  store i32 1, ptr %v, align 4, !dbg !34
  br label %bb4, !dbg !35

bb2:                                              ; preds = %bb1
  %_8 = load i32, ptr %i, align 4, !dbg !36
  %0 = add i32 %_8, 1, !dbg !37
  store i32 %0, ptr %i, align 4, !dbg !37
  %_9 = load i32, ptr %y, align 4, !dbg !38
  %_10 = load i32, ptr %y, align 4, !dbg !39
  %1 = add i32 %_9, %_10, !dbg !40
  store i32 %1, ptr %y, align 4, !dbg !40
  br label %bb1, !dbg !31

bb4:                                              ; preds = %bb5, %bb3
  %_12 = load i32, ptr %i, align 4, !dbg !41
  %_11 = icmp sgt i32 %low, %_12, !dbg !42
  br i1 %_11, label %bb5, label %bb6, !dbg !42

bb6:                                              ; preds = %bb4
  ret void, !dbg !43

bb5:                                              ; preds = %bb4
  %_13 = load i32, ptr %i, align 4, !dbg !44
  %2 = add i32 %_13, 1, !dbg !45
  store i32 %2, ptr %i, align 4, !dbg !45
  %_14 = load i32, ptr %y, align 4, !dbg !46
  %_15 = load i32, ptr %y, align 4, !dbg !47
  %3 = add i32 %_14, %_15, !dbg !48
  store i32 %3, ptr %y, align 4, !dbg !48
  br label %bb4, !dbg !35
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
!6 = !DIFile(filename: "llvm-examples/half-square/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !22, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/half-square/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "b5ae4c684422c79960ff6f7055eaa149")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !16, !18, !20}
!14 = !DILocalVariable(name: "low", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "h", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!16 = !DILocalVariable(name: "i", scope: !17, file: !8, line: 3, type: !12, align: 32)
!17 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!18 = !DILocalVariable(name: "y", scope: !19, file: !8, line: 4, type: !12, align: 32)
!19 = distinct !DILexicalBlock(scope: !17, file: !8, line: 4, column: 5)
!20 = !DILocalVariable(name: "v", scope: !21, file: !8, line: 5, type: !12, align: 32)
!21 = distinct !DILexicalBlock(scope: !19, file: !8, line: 5, column: 5)
!22 = !{}
!23 = !DILocation(line: 2, column: 14, scope: !7)
!24 = !DILocation(line: 2, column: 24, scope: !7)
!25 = !DILocation(line: 3, column: 9, scope: !17)
!26 = !DILocation(line: 4, column: 9, scope: !19)
!27 = !DILocation(line: 5, column: 9, scope: !21)
!28 = !DILocation(line: 3, column: 17, scope: !7)
!29 = !DILocation(line: 4, column: 17, scope: !17)
!30 = !DILocation(line: 5, column: 17, scope: !19)
!31 = !DILocation(line: 6, column: 5, scope: !21)
!32 = !DILocation(line: 6, column: 15, scope: !21)
!33 = !DILocation(line: 6, column: 11, scope: !21)
!34 = !DILocation(line: 10, column: 5, scope: !21)
!35 = !DILocation(line: 11, column: 5, scope: !21)
!36 = !DILocation(line: 7, column: 13, scope: !21)
!37 = !DILocation(line: 7, column: 9, scope: !21)
!38 = !DILocation(line: 8, column: 13, scope: !21)
!39 = !DILocation(line: 8, column: 17, scope: !21)
!40 = !DILocation(line: 8, column: 9, scope: !21)
!41 = !DILocation(line: 11, column: 17, scope: !21)
!42 = !DILocation(line: 11, column: 11, scope: !21)
!43 = !DILocation(line: 15, column: 2, scope: !7)
!44 = !DILocation(line: 12, column: 13, scope: !21)
!45 = !DILocation(line: 12, column: 9, scope: !21)
!46 = !DILocation(line: 13, column: 13, scope: !21)
!47 = !DILocation(line: 13, column: 17, scope: !21)
!48 = !DILocation(line: 13, column: 9, scope: !21)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
