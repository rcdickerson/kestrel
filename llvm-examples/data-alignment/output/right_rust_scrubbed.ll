; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_9145327e5a54bbfe006b4c2d25b2b018 = private unnamed_addr constant [38 x i8] c"llvm-examples/data-alignment/right.rs\00", align 1
@alloc_6f6e251c8165b2b3ad25bd67f27acacb = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_9145327e5a54bbfe006b4c2d25b2b018, [16 x i8] c"%\00\00\00\00\00\00\00\08\00\00\00\0C\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %x) unnamed_addr #0 !dbg !7 {
start:
  %x.dbg.spill = alloca [4 x i8], align 4
  %w = alloca [4 x i8], align 4
  %z = alloca [4 x i8], align 4
  %y = alloca [4 x i8], align 4
  store i32 %x, ptr %x.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !22
  call void @llvm.dbg.declare(metadata ptr %y, metadata !15, metadata !DIExpression()), !dbg !23
  call void @llvm.dbg.declare(metadata ptr %z, metadata !17, metadata !DIExpression()), !dbg !24
  call void @llvm.dbg.declare(metadata ptr %w, metadata !19, metadata !DIExpression()), !dbg !25
  store i32 %x, ptr %y, align 4, !dbg !26
  store i32 16, ptr %z, align 4, !dbg !27
  store i32 0, ptr %w, align 4, !dbg !28
  br label %bb1, !dbg !29

bb1:                                              ; preds = %bb6, %start
  %_6 = load i32, ptr %y, align 4, !dbg !30
  %_5 = icmp sgt i32 %_6, 4, !dbg !30
  br i1 %_5, label %bb2, label %bb7, !dbg !30

bb7:                                              ; preds = %bb1
  ret void, !dbg !31

bb2:                                              ; preds = %bb1
  %_9 = load i32, ptr %w, align 4, !dbg !33
  %_12 = icmp eq i32 %_9, -2147483648, !dbg !33
  %_13 = and i1 false, %_12, !dbg !33
  br i1 %_13, label %panic, label %bb4, !dbg !33

bb4:                                              ; preds = %bb2
  %_8 = srem i32 %_9, 3, !dbg !33
  %_7 = icmp eq i32 %_8, 0, !dbg !33
  br i1 %_7, label %bb5, label %bb6, !dbg !33

panic:                                            ; preds = %bb2
; call core::panicking::panic_const::panic_const_rem_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(ptr align 8 @alloc_6f6e251c8165b2b3ad25bd67f27acacb) #2, !dbg !33
  unreachable, !dbg !33

bb6:                                              ; preds = %bb5, %bb4
  %_16 = load i32, ptr %w, align 4, !dbg !34
  %0 = add i32 %_16, 1, !dbg !35
  store i32 %0, ptr %w, align 4, !dbg !35
  br label %bb1, !dbg !29

bb5:                                              ; preds = %bb4
  %_14 = load i32, ptr %z, align 4, !dbg !36
  %1 = mul i32 %_14, 2, !dbg !37
  store i32 %1, ptr %z, align 4, !dbg !37
  %_15 = load i32, ptr %y, align 4, !dbg !38
  %2 = sub i32 %_15, 1, !dbg !39
  store i32 %2, ptr %y, align 4, !dbg !39
  br label %bb6, !dbg !40
}

; core::panicking::panic_const::panic_const_rem_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_rem_overflow(ptr align 8) unnamed_addr #1

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!llvm.dbg.cu = !{!5}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"Dwarf Version", i32 4}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{!"rustc version 1.97.0 (2d8144b78 2026-07-07)"}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6, producer: "clang LLVM (rustc version 1.97.0 (2d8144b78 2026-07-07))", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!6 = !DIFile(filename: "llvm-examples/data-alignment/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !21, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/data-alignment/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "dcc3f957bb6117b817bac4a54640e68b")
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
!19 = !DILocalVariable(name: "w", scope: !20, file: !8, line: 5, type: !12, align: 32)
!20 = distinct !DILexicalBlock(scope: !18, file: !8, line: 5, column: 5)
!21 = !{}
!22 = !DILocation(line: 2, column: 14, scope: !7)
!23 = !DILocation(line: 3, column: 9, scope: !16)
!24 = !DILocation(line: 4, column: 9, scope: !18)
!25 = !DILocation(line: 5, column: 9, scope: !20)
!26 = !DILocation(line: 3, column: 17, scope: !7)
!27 = !DILocation(line: 4, column: 17, scope: !16)
!28 = !DILocation(line: 5, column: 17, scope: !18)
!29 = !DILocation(line: 7, column: 5, scope: !20)
!30 = !DILocation(line: 7, column: 11, scope: !20)
!31 = !DILocation(line: 14, column: 2, scope: !32)
!32 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!33 = !DILocation(line: 8, column: 12, scope: !20)
!34 = !DILocation(line: 12, column: 13, scope: !20)
!35 = !DILocation(line: 12, column: 9, scope: !20)
!36 = !DILocation(line: 9, column: 17, scope: !20)
!37 = !DILocation(line: 9, column: 13, scope: !20)
!38 = !DILocation(line: 10, column: 17, scope: !20)
!39 = !DILocation(line: 10, column: 13, scope: !20)
!40 = !DILocation(line: 8, column: 9, scope: !20)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
