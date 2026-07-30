; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %x) unnamed_addr #0 !dbg !7 {
start:
  %ret_val.dbg.spill = alloca [4 x i8], align 4
  %x.dbg.spill = alloca [4 x i8], align 4
  store i32 %x, ptr %x.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !18
  %ret_val = add i32 %x, 1, !dbg !19
  store i32 %ret_val, ptr %ret_val.dbg.spill, align 4, !dbg !19
  call void @llvm.dbg.declare(metadata ptr %ret_val.dbg.spill, metadata !15, metadata !DIExpression()), !dbg !20
  ret void, !dbg !21
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
!6 = !DIFile(filename: "llvm-examples/simple/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !17, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/simple/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "19069e79a2a65fbac015d79d6b7332b0")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15}
!14 = !DILocalVariable(name: "x", arg: 1, scope: !7, file: !8, line: 1, type: !12)
!15 = !DILocalVariable(name: "ret_val", scope: !16, file: !8, line: 2, type: !12, align: 32)
!16 = distinct !DILexicalBlock(scope: !7, file: !8, line: 2, column: 3)
!17 = !{}
!18 = !DILocation(line: 1, column: 23, scope: !7)
!19 = !DILocation(line: 2, column: 21, scope: !7)
!20 = !DILocation(line: 2, column: 7, scope: !16)
!21 = !DILocation(line: 3, column: 2, scope: !7)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
