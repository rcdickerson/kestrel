; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_d6ea669b398674e760a68487fbb40ba5 = private unnamed_addr constant [36 x i8] c"llvm-examples/array-insert/right.rs\00", align 1
@alloc_1b6aad345a552ecadc4ef2f80a0f897d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\06\00\00\00\19\00\00\00" }>, align 8
@alloc_a74a36876f5d89ac1dedf5b0e55c3dda = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\0B\00\00\00\05\00\00\00" }>, align 8
@alloc_6a05b4f1dc13a4b1e8be83728286bf0f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\0E\00\00\00\0D\00\00\00" }>, align 8
@alloc_c6a7a81a76189b99aa0755c4e24a8496 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_d6ea669b398674e760a68487fbb40ba5, [16 x i8] c"#\00\00\00\00\00\00\00\07\00\00\00\0D\00\00\00" }>, align 8

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

bb1:                                              ; preds = %bb5, %start
  %_6 = load i64, ptr %j, align 8, !dbg !35
  %_5 = icmp ult i64 %_6, 10, !dbg !35
  br i1 %_5, label %bb2, label %bb6, !dbg !35

bb6:                                              ; preds = %bb3, %bb1
  store i64 11, ptr %len.dbg.spill, align 8, !dbg !36
    #dbg_declare(ptr %len.dbg.spill, !25, !DIExpression(), !37)
  %_15 = load i64, ptr %j, align 8, !dbg !38
  %_16 = icmp ult i64 %_15, 11, !dbg !39
  br i1 %_16, label %bb8, label %panic1, !dbg !39

bb2:                                              ; preds = %bb1
  %_9 = load i64, ptr %j, align 8, !dbg !40
  %_10 = icmp ult i64 %_9, 11, !dbg !41
  br i1 %_10, label %bb3, label %panic, !dbg !41

bb3:                                              ; preds = %bb2
  %0 = getelementptr inbounds nuw i32, ptr %a, i64 %_9, !dbg !41
  %_8 = load i32, ptr %0, align 4, !dbg !41
  %_7 = icmp slt i32 %_8, %val, !dbg !41
  br i1 %_7, label %bb4, label %bb6, !dbg !41

panic:                                            ; preds = %bb2
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_9, i64 11, ptr align 8 @alloc_1b6aad345a552ecadc4ef2f80a0f897d) #3, !dbg !41
  unreachable, !dbg !41

bb4:                                              ; preds = %bb3
  %_11 = load i64, ptr %j, align 8, !dbg !42
  %_12.0 = add i64 %_11, 1, !dbg !42
  %_12.1 = icmp ult i64 %_12.0, %_11, !dbg !42
  br i1 %_12.1, label %panic3, label %bb5, !dbg !42

bb8:                                              ; preds = %bb6
  %1 = getelementptr inbounds nuw i32, ptr %a, i64 %_15, !dbg !39
  store i32 %val, ptr %1, align 4, !dbg !39
  br label %bb9, !dbg !43

panic1:                                           ; preds = %bb6
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_15, i64 11, ptr align 8 @alloc_a74a36876f5d89ac1dedf5b0e55c3dda) #3, !dbg !39
  unreachable, !dbg !39

bb9:                                              ; preds = %bb11, %bb8
  %_18 = load i64, ptr %j, align 8, !dbg !44
  %_17 = icmp ult i64 %_18, 11, !dbg !44
  br i1 %_17, label %bb10, label %bb12, !dbg !44

bb12:                                             ; preds = %bb9
  ret void, !dbg !45

bb10:                                             ; preds = %bb9
  %_19 = load i64, ptr %j, align 8, !dbg !47
  %_20.0 = add i64 %_19, 1, !dbg !47
  %_20.1 = icmp ult i64 %_20.0, %_19, !dbg !47
  br i1 %_20.1, label %panic2, label %bb11, !dbg !47

bb11:                                             ; preds = %bb10
  store i64 %_20.0, ptr %j, align 8, !dbg !48
  br label %bb9, !dbg !43

panic2:                                           ; preds = %bb10
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_6a05b4f1dc13a4b1e8be83728286bf0f) #3, !dbg !47
  unreachable, !dbg !47

bb5:                                              ; preds = %bb4
  store i64 %_12.0, ptr %j, align 8, !dbg !49
  br label %bb1, !dbg !34

panic3:                                           ; preds = %bb4
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_c6a7a81a76189b99aa0755c4e24a8496) #3, !dbg !42
  unreachable, !dbg !42
}

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { noreturn nounwind }

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
!8 = !DIFile(filename: "llvm-examples/array-insert/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "124fa5f44a15c8a1597f76efa1f89b83")
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
!43 = !DILocation(line: 13, column: 5, scope: !26)
!44 = !DILocation(line: 13, column: 11, scope: !26)
!45 = !DILocation(line: 16, column: 2, scope: !46)
!46 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!47 = !DILocation(line: 14, column: 13, scope: !26)
!48 = !DILocation(line: 14, column: 9, scope: !26)
!49 = !DILocation(line: 7, column: 9, scope: !24)
