; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %age) unnamed_addr #0 !dbg !7 {
start:
  %age.dbg.spill = alloca [4 x i8], align 4
  %ret_val = alloca [4 x i8], align 4
  store i32 %age, ptr %age.dbg.spill, align 4
    #dbg_declare(ptr %age.dbg.spill, !14, !DIExpression(), !18)
    #dbg_declare(ptr %ret_val, !15, !DIExpression(), !19)
  store i32 0, ptr %ret_val, align 4, !dbg !20
  %_3 = icmp sge i32 %age, 65, !dbg !21
  br i1 %_3, label %bb1, label %bb2, !dbg !21

bb2:                                              ; preds = %start
  %_4 = icmp sle i32 %age, 12, !dbg !22
  br i1 %_4, label %bb3, label %bb4, !dbg !22

bb1:                                              ; preds = %start
  store i32 20, ptr %ret_val, align 4, !dbg !23
  br label %bb4, !dbg !24

bb4:                                              ; preds = %bb1, %bb3, %bb2
  ret void, !dbg !25

bb3:                                              ; preds = %bb2
  store i32 50, ptr %ret_val, align 4, !dbg !27
  br label %bb4, !dbg !28
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
!6 = !DIFile(filename: "llvm-examples/verified/conditional/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !17, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/verified/conditional/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "79bb3656759f920d1f25b79e386b74b3")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15}
!14 = !DILocalVariable(name: "age", arg: 1, scope: !7, file: !8, line: 1, type: !12)
!15 = !DILocalVariable(name: "ret_val", scope: !16, file: !8, line: 2, type: !12, align: 32)
!16 = distinct !DILexicalBlock(scope: !7, file: !8, line: 2, column: 5)
!17 = !{}
!18 = !DILocation(line: 1, column: 27, scope: !7)
!19 = !DILocation(line: 2, column: 9, scope: !16)
!20 = !DILocation(line: 2, column: 23, scope: !7)
!21 = !DILocation(line: 3, column: 8, scope: !16)
!22 = !DILocation(line: 5, column: 15, scope: !16)
!23 = !DILocation(line: 4, column: 9, scope: !16)
!24 = !DILocation(line: 3, column: 5, scope: !16)
!25 = !DILocation(line: 8, column: 2, scope: !26)
!26 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!27 = !DILocation(line: 6, column: 9, scope: !16)
!28 = !DILocation(line: 5, column: 12, scope: !16)
