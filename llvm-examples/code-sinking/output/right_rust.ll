; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_bf44ca51fc47be80b8773cb414d76a9d = private unnamed_addr constant [36 x i8] c"llvm-examples/code-sinking/right.rs\00", align 1
@alloc_b6a9a667e486e61363affc1a8f96404f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_bf44ca51fc47be80b8773cb414d76a9d, [16 x i8] c"#\00\00\00\00\00\00\00\0D\00\00\00\12\00\00\00" }>, align 8
@alloc_25839b1997cb2d6209d8d3c6ba0567b5 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_bf44ca51fc47be80b8773cb414d76a9d, [16 x i8] c"#\00\00\00\00\00\00\00\0E\00\00\00\13\00\00\00" }>, align 8
@alloc_f8b2f46ae7d9d9573fbd43ab55b46be9 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_bf44ca51fc47be80b8773cb414d76a9d, [16 x i8] c"#\00\00\00\00\00\00\00\14\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a) unnamed_addr #0 !dbg !7 {
start:
  %t.dbg.spill = alloca [4 x i8], align 4
  %n.dbg.spill = alloca [8 x i8], align 8
  %a.dbg.spill = alloca [8 x i8], align 8
  %maxi = alloca [8 x i8], align 8
  %max = alloca [4 x i8], align 4
  %j = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
    #dbg_declare(ptr %a.dbg.spill, !18, !DIExpression(), !31)
    #dbg_declare(ptr %j, !22, !DIExpression(), !32)
    #dbg_declare(ptr %max, !24, !DIExpression(), !33)
    #dbg_declare(ptr %maxi, !26, !DIExpression(), !34)
  store i64 10, ptr %n.dbg.spill, align 8, !dbg !35
    #dbg_declare(ptr %n.dbg.spill, !19, !DIExpression(), !36)
  store i64 0, ptr %j, align 8, !dbg !37
  store i32 0, ptr %max, align 4, !dbg !38
  store i64 0, ptr %maxi, align 8, !dbg !39
  br label %bb1, !dbg !40

bb1:                                              ; preds = %bb14, %start
  %_7 = load i64, ptr %j, align 8, !dbg !41
  %_6 = icmp ult i64 %_7, 10, !dbg !41
  br i1 %_6, label %bb2, label %bb15, !dbg !41

bb15:                                             ; preds = %bb1
  ret void, !dbg !42

bb2:                                              ; preds = %bb1
  %_9 = load i64, ptr %j, align 8, !dbg !44
  %_8 = icmp eq i64 %_9, 0, !dbg !44
  br i1 %_8, label %bb3, label %bb5, !dbg !44

bb5:                                              ; preds = %bb3, %bb2
  %_14 = load i32, ptr %max, align 4, !dbg !45
  %_16 = load i64, ptr %j, align 8, !dbg !46
  %_17 = icmp ult i64 %_16, 11, !dbg !47
  br i1 %_17, label %bb6, label %panic, !dbg !47

bb3:                                              ; preds = %bb2
  %0 = getelementptr inbounds nuw i32, ptr %a, i64 0, !dbg !48
  %_10 = load i32, ptr %0, align 4, !dbg !48
  store i32 %_10, ptr %max, align 4, !dbg !49
  store i64 0, ptr %maxi, align 8, !dbg !50
  br label %bb5, !dbg !51

bb6:                                              ; preds = %bb5
  %1 = getelementptr inbounds nuw i32, ptr %a, i64 %_16, !dbg !47
  %_15 = load i32, ptr %1, align 4, !dbg !47
  %_13 = icmp slt i32 %_14, %_15, !dbg !45
  br i1 %_13, label %bb7, label %bb9, !dbg !45

panic:                                            ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_16, i64 11, ptr align 8 @alloc_b6a9a667e486e61363affc1a8f96404f) #2, !dbg !47
  unreachable, !dbg !47

bb9:                                              ; preds = %bb8, %bb6
  %_23 = load i64, ptr %j, align 8, !dbg !52
  %_22 = icmp eq i64 %_23, 10, !dbg !52
  br i1 %_22, label %bb10, label %bb14, !dbg !52

bb7:                                              ; preds = %bb6
  %_19 = load i64, ptr %j, align 8, !dbg !53
  %_20 = icmp ult i64 %_19, 11, !dbg !54
  br i1 %_20, label %bb8, label %panic1, !dbg !54

bb8:                                              ; preds = %bb7
  %2 = getelementptr inbounds nuw i32, ptr %a, i64 %_19, !dbg !54
  %_18 = load i32, ptr %2, align 4, !dbg !54
  store i32 %_18, ptr %max, align 4, !dbg !55
  %_21 = load i64, ptr %j, align 8, !dbg !56
  store i64 %_21, ptr %maxi, align 8, !dbg !57
  br label %bb9, !dbg !58

panic1:                                           ; preds = %bb7
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_19, i64 11, ptr align 8 @alloc_25839b1997cb2d6209d8d3c6ba0567b5) #2, !dbg !54
  unreachable, !dbg !54

bb14:                                             ; preds = %bb13, %bb9
  %_30 = load i64, ptr %j, align 8, !dbg !59
  %3 = add i64 %_30, 1, !dbg !60
  store i64 %3, ptr %j, align 8, !dbg !60
  br label %bb1, !dbg !40

bb10:                                             ; preds = %bb9
  %4 = getelementptr inbounds nuw i32, ptr %a, i64 10, !dbg !61
  %t = load i32, ptr %4, align 4, !dbg !61
  store i32 %t, ptr %t.dbg.spill, align 4, !dbg !61
    #dbg_declare(ptr %t.dbg.spill, !28, !DIExpression(), !62)
  %_26 = load i32, ptr %max, align 4, !dbg !63
  %5 = getelementptr inbounds nuw i32, ptr %a, i64 10, !dbg !64
  store i32 %_26, ptr %5, align 4, !dbg !64
  %_28 = load i64, ptr %maxi, align 8, !dbg !65
  %_29 = icmp ult i64 %_28, 11, !dbg !66
  br i1 %_29, label %bb13, label %panic2, !dbg !66

bb13:                                             ; preds = %bb10
  %6 = getelementptr inbounds nuw i32, ptr %a, i64 %_28, !dbg !66
  store i32 %t, ptr %6, align 4, !dbg !66
  br label %bb14, !dbg !67

panic2:                                           ; preds = %bb10
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_28, i64 11, ptr align 8 @alloc_f8b2f46ae7d9d9573fbd43ab55b46be9) #2, !dbg !66
  unreachable, !dbg !66
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
!6 = !DIFile(filename: "llvm-examples/code-sinking/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !30, retainedNodes: !17)
!8 = !DIFile(filename: "llvm-examples/code-sinking/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "6b070d1ec55a9f1f424d82be93e0863f")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [i32; 11]", baseType: !13, size: 64, align: 64, dwarfAddressSpace: 0)
!13 = !DICompositeType(tag: DW_TAG_array_type, baseType: !14, size: 352, align: 32, elements: !15)
!14 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!15 = !{!16}
!16 = !DISubrange(count: 11, lowerBound: 0)
!17 = !{!18, !19, !22, !24, !26, !28}
!18 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!19 = !DILocalVariable(name: "n", scope: !20, file: !8, line: 3, type: !21, align: 64)
!20 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!21 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!22 = !DILocalVariable(name: "j", scope: !23, file: !8, line: 4, type: !21, align: 64)
!23 = distinct !DILexicalBlock(scope: !20, file: !8, line: 4, column: 5)
!24 = !DILocalVariable(name: "max", scope: !25, file: !8, line: 5, type: !14, align: 32)
!25 = distinct !DILexicalBlock(scope: !23, file: !8, line: 5, column: 5)
!26 = !DILocalVariable(name: "maxi", scope: !27, file: !8, line: 6, type: !21, align: 64)
!27 = distinct !DILexicalBlock(scope: !25, file: !8, line: 6, column: 5)
!28 = !DILocalVariable(name: "t", scope: !29, file: !8, line: 18, type: !14, align: 32)
!29 = distinct !DILexicalBlock(scope: !27, file: !8, line: 18, column: 13)
!30 = !{}
!31 = !DILocation(line: 2, column: 14, scope: !7)
!32 = !DILocation(line: 4, column: 9, scope: !23)
!33 = !DILocation(line: 5, column: 9, scope: !25)
!34 = !DILocation(line: 6, column: 9, scope: !27)
!35 = !DILocation(line: 3, column: 13, scope: !7)
!36 = !DILocation(line: 3, column: 9, scope: !20)
!37 = !DILocation(line: 4, column: 17, scope: !20)
!38 = !DILocation(line: 5, column: 19, scope: !23)
!39 = !DILocation(line: 6, column: 20, scope: !25)
!40 = !DILocation(line: 8, column: 5, scope: !27)
!41 = !DILocation(line: 8, column: 11, scope: !27)
!42 = !DILocation(line: 24, column: 2, scope: !43)
!43 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!44 = !DILocation(line: 9, column: 12, scope: !27)
!45 = !DILocation(line: 13, column: 12, scope: !27)
!46 = !DILocation(line: 13, column: 20, scope: !27)
!47 = !DILocation(line: 13, column: 18, scope: !27)
!48 = !DILocation(line: 10, column: 19, scope: !27)
!49 = !DILocation(line: 10, column: 13, scope: !27)
!50 = !DILocation(line: 11, column: 13, scope: !27)
!51 = !DILocation(line: 9, column: 9, scope: !27)
!52 = !DILocation(line: 17, column: 12, scope: !27)
!53 = !DILocation(line: 14, column: 21, scope: !27)
!54 = !DILocation(line: 14, column: 19, scope: !27)
!55 = !DILocation(line: 14, column: 13, scope: !27)
!56 = !DILocation(line: 15, column: 20, scope: !27)
!57 = !DILocation(line: 15, column: 13, scope: !27)
!58 = !DILocation(line: 13, column: 9, scope: !27)
!59 = !DILocation(line: 22, column: 13, scope: !27)
!60 = !DILocation(line: 22, column: 9, scope: !27)
!61 = !DILocation(line: 18, column: 21, scope: !27)
!62 = !DILocation(line: 18, column: 17, scope: !29)
!63 = !DILocation(line: 19, column: 20, scope: !29)
!64 = !DILocation(line: 19, column: 13, scope: !29)
!65 = !DILocation(line: 20, column: 15, scope: !29)
!66 = !DILocation(line: 20, column: 13, scope: !29)
!67 = !DILocation(line: 17, column: 9, scope: !27)
