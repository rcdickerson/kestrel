; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_d6ea669b398674e760a68487fbb40ba5 = private unnamed_addr constant [36 x i8] c"llvm-examples/array-insert/right.rs\00", align 1
@alloc_1b6aad345a552ecadc4ef2f80a0f897d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\06\00\00\00\19\00\00\00" }>, align 8
@alloc_a74a36876f5d89ac1dedf5b0e55c3dda = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\0B\00\00\00\05\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a, i32 %val) unnamed_addr #0 !dbg !7 {
start:
  %len.dbg.spill = alloca [8 x i8], align 8
  %a_size.dbg.spill = alloca [8 x i8], align 8
  %val.dbg.spill = alloca [4 x i8], align 4
  %a.dbg.spill = alloca [8 x i8], align 8
  %j = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
    #dbg_declare(ptr %a.dbg.spill, !18, !DIExpression(), !28)
  store i32 %val, ptr %val.dbg.spill, align 4
    #dbg_declare(ptr %val.dbg.spill, !19, !DIExpression(), !29)
    #dbg_declare(ptr %j, !23, !DIExpression(), !30)
  store i64 10, ptr %a_size.dbg.spill, align 8, !dbg !31
    #dbg_declare(ptr %a_size.dbg.spill, !20, !DIExpression(), !32)
  store i64 0, ptr %j, align 8, !dbg !33
  br label %bb1, !dbg !34

bb1:                                              ; preds = %bb4, %start
  %_6 = load i64, ptr %j, align 8, !dbg !35
  %_5 = icmp ult i64 %_6, 10, !dbg !35
  br i1 %_5, label %bb2, label %bb5, !dbg !35

bb5:                                              ; preds = %bb3, %bb1
  store i64 11, ptr %len.dbg.spill, align 8, !dbg !36
    #dbg_declare(ptr %len.dbg.spill, !25, !DIExpression(), !37)
  %_13 = load i64, ptr %j, align 8, !dbg !38
  %_14 = icmp ult i64 %_13, 11, !dbg !39
  br i1 %_14, label %bb6, label %panic1, !dbg !39

bb2:                                              ; preds = %bb1
  %_9 = load i64, ptr %j, align 8, !dbg !40
  %_10 = icmp ult i64 %_9, 11, !dbg !41
  br i1 %_10, label %bb3, label %panic, !dbg !41

bb3:                                              ; preds = %bb2
  %0 = getelementptr inbounds nuw i32, ptr %a, i64 %_9, !dbg !41
  %_8 = load i32, ptr %0, align 4, !dbg !41
  %_7 = icmp slt i32 %_8, %val, !dbg !41
  br i1 %_7, label %bb4, label %bb5, !dbg !41

panic:                                            ; preds = %bb2
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_9, i64 11, ptr align 8 @alloc_1b6aad345a552ecadc4ef2f80a0f897d) #2, !dbg !41
  unreachable, !dbg !41

bb4:                                              ; preds = %bb3
  %_11 = load i64, ptr %j, align 8, !dbg !42
  %1 = add i64 %_11, 1, !dbg !43
  store i64 %1, ptr %j, align 8, !dbg !43
  br label %bb1, !dbg !34

bb6:                                              ; preds = %bb5
  %2 = getelementptr inbounds nuw i32, ptr %a, i64 %_13, !dbg !39
  store i32 %val, ptr %2, align 4, !dbg !39
  br label %bb7, !dbg !44

panic1:                                           ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_13, i64 11, ptr align 8 @alloc_a74a36876f5d89ac1dedf5b0e55c3dda) #2, !dbg !39
  unreachable, !dbg !39

bb7:                                              ; preds = %bb8, %bb6
  %_16 = load i64, ptr %j, align 8, !dbg !45
  %_15 = icmp ult i64 %_16, 11, !dbg !45
  br i1 %_15, label %bb8, label %bb9, !dbg !45

bb9:                                              ; preds = %bb7
  ret void, !dbg !46

bb8:                                              ; preds = %bb7
  %_17 = load i64, ptr %j, align 8, !dbg !48
  %3 = add i64 %_17, 1, !dbg !49
  store i64 %3, ptr %j, align 8, !dbg !49
  br label %bb7, !dbg !44
}

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #1

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
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
!6 = !DIFile(filename: "llvm-examples/array-insert/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !27, retainedNodes: !17)
!8 = !DIFile(filename: "llvm-examples/array-insert/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "b185310057b64b5ec4953581245b625f")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !14}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [i32; 11]", baseType: !13, size: 64, align: 64, dwarfAddressSpace: 0)
!13 = !DICompositeType(tag: DW_TAG_array_type, baseType: !14, size: 352, align: 32, elements: !15)
!14 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!15 = !{!16}
!16 = !DISubrange(count: 11, lowerBound: 0)
!17 = !{!18, !19, !20, !23, !25}
!18 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!19 = !DILocalVariable(name: "val", arg: 2, scope: !7, file: !8, line: 2, type: !14)
!20 = !DILocalVariable(name: "a_size", scope: !21, file: !8, line: 3, type: !22, align: 64)
!21 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!22 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!23 = !DILocalVariable(name: "j", scope: !24, file: !8, line: 4, type: !22, align: 64)
!24 = distinct !DILexicalBlock(scope: !21, file: !8, line: 4, column: 5)
!25 = !DILocalVariable(name: "len", scope: !26, file: !8, line: 10, type: !22, align: 64)
!26 = distinct !DILexicalBlock(scope: !24, file: !8, line: 10, column: 5)
!27 = !{}
!28 = !DILocation(line: 2, column: 14, scope: !7)
!29 = !DILocation(line: 2, column: 33, scope: !7)
!30 = !DILocation(line: 4, column: 9, scope: !24)
!31 = !DILocation(line: 3, column: 18, scope: !7)
!32 = !DILocation(line: 3, column: 9, scope: !21)
!33 = !DILocation(line: 4, column: 17, scope: !21)
!34 = !DILocation(line: 6, column: 5, scope: !24)
!35 = !DILocation(line: 6, column: 11, scope: !24)
!36 = !DILocation(line: 10, column: 15, scope: !24)
!37 = !DILocation(line: 10, column: 9, scope: !26)
!38 = !DILocation(line: 11, column: 7, scope: !26)
!39 = !DILocation(line: 11, column: 5, scope: !26)
!40 = !DILocation(line: 6, column: 27, scope: !24)
!41 = !DILocation(line: 6, column: 25, scope: !24)
!42 = !DILocation(line: 7, column: 13, scope: !24)
!43 = !DILocation(line: 7, column: 9, scope: !24)
!44 = !DILocation(line: 13, column: 5, scope: !26)
!45 = !DILocation(line: 13, column: 11, scope: !26)
!46 = !DILocation(line: 16, column: 2, scope: !47)
!47 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!48 = !DILocation(line: 14, column: 13, scope: !26)
!49 = !DILocation(line: 14, column: 9, scope: !26)
