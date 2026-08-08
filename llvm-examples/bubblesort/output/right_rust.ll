; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_ea4d054be0d9a3464770d70d8a04499f = private unnamed_addr constant [34 x i8] c"llvm-examples/bubblesort/right.rs\00", align 1
@alloc_d10824f57abd82b96f74d8a998900e37 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\08\00\00\00\10\00\00\00" }>, align 8
@alloc_c1472aaa99a0c9e01c4370a339afe9b1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\08\00\00\00\1B\00\00\00" }>, align 8
@alloc_b306f3c5835633be8c030b2750cb09fc = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\09\00\00\00\1C\00\00\00" }>, align 8
@alloc_a026c78e675b1169ca6570e96453f0ba = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\0A\00\00\00\18\00\00\00" }>, align 8
@alloc_991cfbf1566089e55fc7fedefbf4d17b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\0A\00\00\00\11\00\00\00" }>, align 8
@alloc_a660e85f91318953292432dd99f84179 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_ea4d054be0d9a3464770d70d8a04499f, [16 x i8] c"!\00\00\00\00\00\00\00\0B\00\00\00\11\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a) unnamed_addr #0 !dbg !7 {
start:
  %temp.dbg.spill = alloca [4 x i8], align 4
  %n.dbg.spill = alloca [8 x i8], align 8
  %a.dbg.spill = alloca [8 x i8], align 8
  %j = alloca [8 x i8], align 8
  %i = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
    #dbg_declare(ptr %a.dbg.spill, !18, !DIExpression(), !29)
    #dbg_declare(ptr %i, !22, !DIExpression(), !30)
    #dbg_declare(ptr %j, !24, !DIExpression(), !31)
  store i64 10, ptr %n.dbg.spill, align 8, !dbg !32
    #dbg_declare(ptr %n.dbg.spill, !19, !DIExpression(), !33)
  store i64 0, ptr %i, align 8, !dbg !34
  br label %bb1, !dbg !35

bb1:                                              ; preds = %bb13, %start
  %_5 = load i64, ptr %i, align 8, !dbg !36
  %_4 = icmp ult i64 %_5, 10, !dbg !36
  br i1 %_4, label %bb2, label %bb14, !dbg !36

bb14:                                             ; preds = %bb1
  ret void, !dbg !37

bb2:                                              ; preds = %bb1
  store i64 9, ptr %j, align 8, !dbg !39
  br label %bb3, !dbg !40

bb3:                                              ; preds = %bb12, %bb2
  %_8 = load i64, ptr %j, align 8, !dbg !41
  %_9 = load i64, ptr %i, align 8, !dbg !42
  %_7 = icmp ugt i64 %_8, %_9, !dbg !41
  br i1 %_7, label %bb4, label %bb13, !dbg !41

bb13:                                             ; preds = %bb3
  %_31 = load i64, ptr %i, align 8, !dbg !43
  %0 = add i64 %_31, 1, !dbg !44
  store i64 %0, ptr %i, align 8, !dbg !44
  br label %bb1, !dbg !35

bb4:                                              ; preds = %bb3
  %_13 = load i64, ptr %j, align 8, !dbg !45
  %_12 = sub i64 %_13, 1, !dbg !45
  %_14 = icmp ult i64 %_12, 10, !dbg !46
  br i1 %_14, label %bb5, label %panic, !dbg !46

bb5:                                              ; preds = %bb4
  %1 = getelementptr inbounds nuw float, ptr %a, i64 %_12, !dbg !46
  %_11 = load float, ptr %1, align 4, !dbg !46
  %_16 = load i64, ptr %j, align 8, !dbg !47
  %_17 = icmp ult i64 %_16, 10, !dbg !48
  br i1 %_17, label %bb6, label %panic1, !dbg !48

panic:                                            ; preds = %bb4
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_12, i64 10, ptr align 8 @alloc_d10824f57abd82b96f74d8a998900e37) #2, !dbg !46
  unreachable, !dbg !46

bb6:                                              ; preds = %bb5
  %2 = getelementptr inbounds nuw float, ptr %a, i64 %_16, !dbg !48
  %_15 = load float, ptr %2, align 4, !dbg !48
  %_10 = fcmp ogt float %_11, %_15, !dbg !46
  br i1 %_10, label %bb7, label %bb12, !dbg !46

panic1:                                           ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_16, i64 10, ptr align 8 @alloc_c1472aaa99a0c9e01c4370a339afe9b1) #2, !dbg !48
  unreachable, !dbg !48

bb12:                                             ; preds = %bb11, %bb6
  %_30 = load i64, ptr %j, align 8, !dbg !49
  %3 = sub i64 %_30, 1, !dbg !50
  store i64 %3, ptr %j, align 8, !dbg !50
  br label %bb3, !dbg !40

bb7:                                              ; preds = %bb6
  %_19 = load i64, ptr %j, align 8, !dbg !51
  %_20 = icmp ult i64 %_19, 10, !dbg !52
  br i1 %_20, label %bb8, label %panic2, !dbg !52

bb8:                                              ; preds = %bb7
  %4 = getelementptr inbounds nuw float, ptr %a, i64 %_19, !dbg !52
  %temp = load float, ptr %4, align 4, !dbg !52
  store float %temp, ptr %temp.dbg.spill, align 4, !dbg !52
    #dbg_declare(ptr %temp.dbg.spill, !26, !DIExpression(), !53)
  %_23 = load i64, ptr %j, align 8, !dbg !54
  %_22 = sub i64 %_23, 1, !dbg !54
  %_24 = icmp ult i64 %_22, 10, !dbg !55
  br i1 %_24, label %bb9, label %panic3, !dbg !55

panic2:                                           ; preds = %bb7
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_19, i64 10, ptr align 8 @alloc_b306f3c5835633be8c030b2750cb09fc) #2, !dbg !52
  unreachable, !dbg !52

bb9:                                              ; preds = %bb8
  %5 = getelementptr inbounds nuw float, ptr %a, i64 %_22, !dbg !55
  %_21 = load float, ptr %5, align 4, !dbg !55
  %_25 = load i64, ptr %j, align 8, !dbg !56
  %_26 = icmp ult i64 %_25, 10, !dbg !57
  br i1 %_26, label %bb10, label %panic4, !dbg !57

panic3:                                           ; preds = %bb8
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_22, i64 10, ptr align 8 @alloc_a026c78e675b1169ca6570e96453f0ba) #2, !dbg !55
  unreachable, !dbg !55

bb10:                                             ; preds = %bb9
  %6 = getelementptr inbounds nuw float, ptr %a, i64 %_25, !dbg !57
  store float %_21, ptr %6, align 4, !dbg !57
  %_28 = load i64, ptr %j, align 8, !dbg !58
  %_27 = sub i64 %_28, 1, !dbg !58
  %_29 = icmp ult i64 %_27, 10, !dbg !59
  br i1 %_29, label %bb11, label %panic5, !dbg !59

panic4:                                           ; preds = %bb9
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_25, i64 10, ptr align 8 @alloc_991cfbf1566089e55fc7fedefbf4d17b) #2, !dbg !57
  unreachable, !dbg !57

bb11:                                             ; preds = %bb10
  %7 = getelementptr inbounds nuw float, ptr %a, i64 %_27, !dbg !59
  store float %temp, ptr %7, align 4, !dbg !59
  br label %bb12, !dbg !60

panic5:                                           ; preds = %bb10
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_27, i64 10, ptr align 8 @alloc_a660e85f91318953292432dd99f84179) #2, !dbg !59
  unreachable, !dbg !59
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
!6 = !DIFile(filename: "llvm-examples/bubblesort/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !28, retainedNodes: !17)
!8 = !DIFile(filename: "llvm-examples/bubblesort/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "d58b3f2930bba9a7e84e62482eaad645")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [f32; 10]", baseType: !13, size: 64, align: 64, dwarfAddressSpace: 0)
!13 = !DICompositeType(tag: DW_TAG_array_type, baseType: !14, size: 320, align: 32, elements: !15)
!14 = !DIBasicType(name: "f32", size: 32, encoding: DW_ATE_float)
!15 = !{!16}
!16 = !DISubrange(count: 10, lowerBound: 0)
!17 = !{!18, !19, !22, !24, !26}
!18 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!19 = !DILocalVariable(name: "n", scope: !20, file: !8, line: 3, type: !21, align: 64)
!20 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!21 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!22 = !DILocalVariable(name: "i", scope: !23, file: !8, line: 4, type: !21, align: 64)
!23 = distinct !DILexicalBlock(scope: !20, file: !8, line: 4, column: 5)
!24 = !DILocalVariable(name: "j", scope: !25, file: !8, line: 6, type: !21, align: 64)
!25 = distinct !DILexicalBlock(scope: !23, file: !8, line: 6, column: 9)
!26 = !DILocalVariable(name: "temp", scope: !27, file: !8, line: 9, type: !14, align: 32)
!27 = distinct !DILexicalBlock(scope: !25, file: !8, line: 9, column: 17)
!28 = !{}
!29 = !DILocation(line: 2, column: 14, scope: !7)
!30 = !DILocation(line: 4, column: 9, scope: !23)
!31 = !DILocation(line: 6, column: 13, scope: !25)
!32 = !DILocation(line: 3, column: 13, scope: !7)
!33 = !DILocation(line: 3, column: 9, scope: !20)
!34 = !DILocation(line: 4, column: 17, scope: !20)
!35 = !DILocation(line: 5, column: 5, scope: !23)
!36 = !DILocation(line: 5, column: 11, scope: !23)
!37 = !DILocation(line: 17, column: 2, scope: !38)
!38 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!39 = !DILocation(line: 6, column: 21, scope: !23)
!40 = !DILocation(line: 7, column: 9, scope: !25)
!41 = !DILocation(line: 7, column: 15, scope: !25)
!42 = !DILocation(line: 7, column: 19, scope: !25)
!43 = !DILocation(line: 15, column: 13, scope: !25)
!44 = !DILocation(line: 15, column: 9, scope: !25)
!45 = !DILocation(line: 8, column: 18, scope: !25)
!46 = !DILocation(line: 8, column: 16, scope: !25)
!47 = !DILocation(line: 8, column: 29, scope: !25)
!48 = !DILocation(line: 8, column: 27, scope: !25)
!49 = !DILocation(line: 13, column: 17, scope: !25)
!50 = !DILocation(line: 13, column: 13, scope: !25)
!51 = !DILocation(line: 9, column: 30, scope: !25)
!52 = !DILocation(line: 9, column: 28, scope: !25)
!53 = !DILocation(line: 9, column: 21, scope: !27)
!54 = !DILocation(line: 10, column: 26, scope: !27)
!55 = !DILocation(line: 10, column: 24, scope: !27)
!56 = !DILocation(line: 10, column: 19, scope: !27)
!57 = !DILocation(line: 10, column: 17, scope: !27)
!58 = !DILocation(line: 11, column: 19, scope: !27)
!59 = !DILocation(line: 11, column: 17, scope: !27)
!60 = !DILocation(line: 8, column: 13, scope: !25)
