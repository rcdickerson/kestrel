; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %a, i32 %b, i32 %c) unnamed_addr #0 !dbg !7 {
start:
  %prod.dbg.spill = alloca [4 x i8], align 4
  %sum.dbg.spill = alloca [4 x i8], align 4
  %c.dbg.spill = alloca [4 x i8], align 4
  %b.dbg.spill = alloca [4 x i8], align 4
  %a.dbg.spill = alloca [4 x i8], align 4
  store i32 %a, ptr %a.dbg.spill, align 4
    #dbg_declare(ptr %a.dbg.spill, !14, !DIExpression(), !22)
  store i32 %b, ptr %b.dbg.spill, align 4
    #dbg_declare(ptr %b.dbg.spill, !15, !DIExpression(), !23)
  store i32 %c, ptr %c.dbg.spill, align 4
    #dbg_declare(ptr %c.dbg.spill, !16, !DIExpression(), !24)
  %sum = add i32 %a, %b, !dbg !25
  store i32 %sum, ptr %sum.dbg.spill, align 4, !dbg !25
    #dbg_declare(ptr %sum.dbg.spill, !17, !DIExpression(), !26)
  %prod = mul i32 %sum, %c, !dbg !27
  store i32 %prod, ptr %prod.dbg.spill, align 4, !dbg !27
    #dbg_declare(ptr %prod.dbg.spill, !19, !DIExpression(), !28)
  ret void, !dbg !29
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
!6 = !DIFile(filename: "llvm-examples/verified/arithmetic/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !21, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/verified/arithmetic/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "6bf5410e88b0a43fc45356a91a9d535a")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !16, !17, !19}
!14 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 1, type: !12)
!15 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !8, line: 1, type: !12)
!16 = !DILocalVariable(name: "c", arg: 3, scope: !7, file: !8, line: 1, type: !12)
!17 = !DILocalVariable(name: "sum", scope: !18, file: !8, line: 2, type: !12, align: 32)
!18 = distinct !DILexicalBlock(scope: !7, file: !8, line: 2, column: 5)
!19 = !DILocalVariable(name: "prod", scope: !20, file: !8, line: 3, type: !12, align: 32)
!20 = distinct !DILexicalBlock(scope: !18, file: !8, line: 3, column: 5)
!21 = !{}
!22 = !DILocation(line: 1, column: 27, scope: !7)
!23 = !DILocation(line: 1, column: 35, scope: !7)
!24 = !DILocation(line: 1, column: 43, scope: !7)
!25 = !DILocation(line: 2, column: 15, scope: !7)
!26 = !DILocation(line: 2, column: 9, scope: !18)
!27 = !DILocation(line: 3, column: 16, scope: !18)
!28 = !DILocation(line: 3, column: 9, scope: !20)
!29 = !DILocation(line: 4, column: 2, scope: !30)
!30 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
