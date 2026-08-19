; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_df9fb36b3e50035d5a26429439c29ed9 = private unnamed_addr constant [40 x i8] c"llvm-examples/loop-unswitching/right.rs\00", align 1
@alloc_419ef0d9175c3c3d25b6349e67ee0cbd = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0E\00\00\00\14\00\00\00" }>, align 8
@alloc_d2d5579a465f4b0e260596020158df10 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0E\00\00\00\0D\00\00\00" }>, align 8
@alloc_e3f13fad5a0fb42e992397669711c193 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\14\00\00\00" }>, align 8
@alloc_bb2f62fcbec2afd6481e273b7e37fcc1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\1F\00\00\00" }>, align 8
@alloc_31ffd0f23462b2f4117f2c5301d8027b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\0D\00\00\00" }>, align 8
@alloc_a431e0af1f0a773d7894a8f7648fcbbb = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\07\00\00\00\14\00\00\00" }>, align 8
@alloc_86a95f0408d87e2b4012bd6715ad108d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\07\00\00\00\0D\00\00\00" }>, align 8
@alloc_72db5233068273f5dabaebf836ed1389 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\14\00\00\00" }>, align 8
@alloc_40b9f4e097b3d8001419ebb57560c155 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\1B\00\00\00" }>, align 8
@alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a, ptr align 4 %b, ptr align 4 %c, i32 %k, i32 %x) unnamed_addr #0 !dbg !7 {
start:
  %n.dbg.spill = alloca [8 x i8], align 8
  %x.dbg.spill = alloca [4 x i8], align 4
  %k.dbg.spill = alloca [4 x i8], align 4
  %c.dbg.spill = alloca [8 x i8], align 8
  %b.dbg.spill = alloca [8 x i8], align 8
  %a.dbg.spill = alloca [8 x i8], align 8
  %j1 = alloca [8 x i8], align 8
  %j = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %a.dbg.spill, metadata !18, metadata !DIExpression()), !dbg !31
  store ptr %b, ptr %b.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %b.dbg.spill, metadata !19, metadata !DIExpression()), !dbg !32
  store ptr %c, ptr %c.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %c.dbg.spill, metadata !20, metadata !DIExpression()), !dbg !33
  store i32 %k, ptr %k.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %k.dbg.spill, metadata !21, metadata !DIExpression()), !dbg !34
  store i32 %x, ptr %x.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !22, metadata !DIExpression()), !dbg !35
  call void @llvm.dbg.declare(metadata ptr %j, metadata !26, metadata !DIExpression()), !dbg !36
  call void @llvm.dbg.declare(metadata ptr %j1, metadata !28, metadata !DIExpression()), !dbg !37
  store i64 10, ptr %n.dbg.spill, align 8, !dbg !38
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !23, metadata !DIExpression()), !dbg !39
  %_7 = icmp slt i32 %x, 7, !dbg !40
  br i1 %_7, label %bb1, label %bb9, !dbg !40

bb9:                                              ; preds = %start
  store i64 0, ptr %j1, align 8, !dbg !41
  br label %bb10, !dbg !42

bb1:                                              ; preds = %start
  store i64 0, ptr %j, align 8, !dbg !43
  br label %bb2, !dbg !44

bb10:                                             ; preds = %bb16, %bb9
  %_27 = load i64, ptr %j1, align 8, !dbg !45
  %_26 = icmp ult i64 %_27, 10, !dbg !45
  br i1 %_26, label %bb11, label %bb17, !dbg !45

bb17:                                             ; preds = %bb2, %bb10
  ret void, !dbg !46

bb11:                                             ; preds = %bb10
  %_29 = load i64, ptr %j1, align 8, !dbg !47
  %_30 = icmp ult i64 %_29, 10, !dbg !48
  br i1 %_30, label %bb12, label %panic, !dbg !48

bb12:                                             ; preds = %bb11
  %0 = getelementptr inbounds i32, ptr %a, i64 %_29, !dbg !48
  %_28 = load i32, ptr %0, align 4, !dbg !48
  %_31 = load i64, ptr %j1, align 8, !dbg !49
  %_32 = icmp ult i64 %_31, 10, !dbg !50
  br i1 %_32, label %bb13, label %panic2, !dbg !50

panic:                                            ; preds = %bb11
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_29, i64 10, ptr align 8 @alloc_419ef0d9175c3c3d25b6349e67ee0cbd) #2, !dbg !48
  unreachable, !dbg !48

bb13:                                             ; preds = %bb12
  %1 = getelementptr inbounds i32, ptr %a, i64 %_31, !dbg !50
  %2 = add i32 %_28, %k, !dbg !50
  store i32 %2, ptr %1, align 4, !dbg !50
  %_35 = load i64, ptr %j1, align 8, !dbg !51
  %_34 = sub i64 %_35, 1, !dbg !51
  %_36 = icmp ult i64 %_34, 10, !dbg !52
  br i1 %_36, label %bb14, label %panic3, !dbg !52

panic2:                                           ; preds = %bb12
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_31, i64 10, ptr align 8 @alloc_d2d5579a465f4b0e260596020158df10) #2, !dbg !50
  unreachable, !dbg !50

bb14:                                             ; preds = %bb13
  %3 = getelementptr inbounds i32, ptr %a, i64 %_34, !dbg !52
  %_33 = load i32, ptr %3, align 4, !dbg !52
  %_39 = load i64, ptr %j1, align 8, !dbg !53
  %_38 = sub i64 %_39, 1, !dbg !53
  %_40 = icmp ult i64 %_38, 10, !dbg !54
  br i1 %_40, label %bb15, label %panic4, !dbg !54

panic3:                                           ; preds = %bb13
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_34, i64 10, ptr align 8 @alloc_e3f13fad5a0fb42e992397669711c193) #2, !dbg !52
  unreachable, !dbg !52

bb15:                                             ; preds = %bb14
  %4 = getelementptr inbounds i32, ptr %b, i64 %_38, !dbg !54
  %_37 = load i32, ptr %4, align 4, !dbg !54
  %_41 = load i64, ptr %j1, align 8, !dbg !55
  %_42 = icmp ult i64 %_41, 10, !dbg !56
  br i1 %_42, label %bb16, label %panic5, !dbg !56

panic4:                                           ; preds = %bb14
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_38, i64 10, ptr align 8 @alloc_bb2f62fcbec2afd6481e273b7e37fcc1) #2, !dbg !54
  unreachable, !dbg !54

bb16:                                             ; preds = %bb15
  %5 = getelementptr inbounds i32, ptr %b, i64 %_41, !dbg !56
  %6 = mul i32 %_33, %_37, !dbg !56
  store i32 %6, ptr %5, align 4, !dbg !56
  %_43 = load i64, ptr %j1, align 8, !dbg !57
  %7 = add i64 %_43, 1, !dbg !58
  store i64 %7, ptr %j1, align 8, !dbg !58
  br label %bb10, !dbg !42

panic5:                                           ; preds = %bb15
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_41, i64 10, ptr align 8 @alloc_31ffd0f23462b2f4117f2c5301d8027b) #2, !dbg !56
  unreachable, !dbg !56

bb2:                                              ; preds = %bb8, %bb1
  %_10 = load i64, ptr %j, align 8, !dbg !59
  %_9 = icmp ult i64 %_10, 10, !dbg !59
  br i1 %_9, label %bb3, label %bb17, !dbg !59

bb3:                                              ; preds = %bb2
  %_12 = load i64, ptr %j, align 8, !dbg !60
  %_13 = icmp ult i64 %_12, 10, !dbg !61
  br i1 %_13, label %bb4, label %panic6, !dbg !61

bb4:                                              ; preds = %bb3
  %8 = getelementptr inbounds i32, ptr %a, i64 %_12, !dbg !61
  %_11 = load i32, ptr %8, align 4, !dbg !61
  %_14 = load i64, ptr %j, align 8, !dbg !62
  %_15 = icmp ult i64 %_14, 10, !dbg !63
  br i1 %_15, label %bb5, label %panic7, !dbg !63

panic6:                                           ; preds = %bb3
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_12, i64 10, ptr align 8 @alloc_a431e0af1f0a773d7894a8f7648fcbbb) #2, !dbg !61
  unreachable, !dbg !61

bb5:                                              ; preds = %bb4
  %9 = getelementptr inbounds i32, ptr %a, i64 %_14, !dbg !63
  %10 = add i32 %_11, %k, !dbg !63
  store i32 %10, ptr %9, align 4, !dbg !63
  %_17 = load i64, ptr %j, align 8, !dbg !64
  %_18 = icmp ult i64 %_17, 10, !dbg !65
  br i1 %_18, label %bb6, label %panic8, !dbg !65

panic7:                                           ; preds = %bb4
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_14, i64 10, ptr align 8 @alloc_86a95f0408d87e2b4012bd6715ad108d) #2, !dbg !63
  unreachable, !dbg !63

bb6:                                              ; preds = %bb5
  %11 = getelementptr inbounds i32, ptr %a, i64 %_17, !dbg !65
  %_16 = load i32, ptr %11, align 4, !dbg !65
  %_20 = load i64, ptr %j, align 8, !dbg !66
  %_21 = icmp ult i64 %_20, 10, !dbg !67
  br i1 %_21, label %bb7, label %panic9, !dbg !67

panic8:                                           ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_17, i64 10, ptr align 8 @alloc_72db5233068273f5dabaebf836ed1389) #2, !dbg !65
  unreachable, !dbg !65

bb7:                                              ; preds = %bb6
  %12 = getelementptr inbounds i32, ptr %c, i64 %_20, !dbg !67
  %_19 = load i32, ptr %12, align 4, !dbg !67
  %_22 = load i64, ptr %j, align 8, !dbg !68
  %_23 = icmp ult i64 %_22, 10, !dbg !69
  br i1 %_23, label %bb8, label %panic10, !dbg !69

panic9:                                           ; preds = %bb6
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_20, i64 10, ptr align 8 @alloc_40b9f4e097b3d8001419ebb57560c155) #2, !dbg !67
  unreachable, !dbg !67

bb8:                                              ; preds = %bb7
  %13 = getelementptr inbounds i32, ptr %b, i64 %_22, !dbg !69
  %14 = mul i32 %_16, %_19, !dbg !69
  store i32 %14, ptr %13, align 4, !dbg !69
  %_24 = load i64, ptr %j, align 8, !dbg !70
  %15 = add i64 %_24, 1, !dbg !71
  store i64 %15, ptr %j, align 8, !dbg !71
  br label %bb2, !dbg !44

panic10:                                          ; preds = %bb7
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_22, i64 10, ptr align 8 @alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2) #2, !dbg !69
  unreachable, !dbg !69
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
!6 = !DIFile(filename: "llvm-examples/loop-unswitching/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !30, retainedNodes: !17)
!8 = !DIFile(filename: "llvm-examples/loop-unswitching/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "a75ec29d2434a02337ceec20447136f9")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12, !12, !14, !14}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [i32; 10]", baseType: !13, size: 64, align: 64, dwarfAddressSpace: 0)
!13 = !DICompositeType(tag: DW_TAG_array_type, baseType: !14, size: 320, align: 32, elements: !15)
!14 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!15 = !{!16}
!16 = !DISubrange(count: 10, lowerBound: 0)
!17 = !{!18, !19, !20, !21, !22, !23, !26, !28}
!18 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!19 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!20 = !DILocalVariable(name: "c", arg: 3, scope: !7, file: !8, line: 2, type: !12)
!21 = !DILocalVariable(name: "k", arg: 4, scope: !7, file: !8, line: 2, type: !14)
!22 = !DILocalVariable(name: "x", arg: 5, scope: !7, file: !8, line: 2, type: !14)
!23 = !DILocalVariable(name: "n", scope: !24, file: !8, line: 3, type: !25, align: 64)
!24 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!25 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!26 = !DILocalVariable(name: "j", scope: !27, file: !8, line: 5, type: !25, align: 64)
!27 = distinct !DILexicalBlock(scope: !24, file: !8, line: 5, column: 9)
!28 = !DILocalVariable(name: "j", scope: !29, file: !8, line: 12, type: !25, align: 64)
!29 = distinct !DILexicalBlock(scope: !24, file: !8, line: 12, column: 9)
!30 = !{}
!31 = !DILocation(line: 2, column: 14, scope: !7)
!32 = !DILocation(line: 2, column: 33, scope: !7)
!33 = !DILocation(line: 2, column: 52, scope: !7)
!34 = !DILocation(line: 2, column: 71, scope: !7)
!35 = !DILocation(line: 2, column: 79, scope: !7)
!36 = !DILocation(line: 5, column: 13, scope: !27)
!37 = !DILocation(line: 12, column: 13, scope: !29)
!38 = !DILocation(line: 3, column: 13, scope: !7)
!39 = !DILocation(line: 3, column: 9, scope: !24)
!40 = !DILocation(line: 4, column: 8, scope: !24)
!41 = !DILocation(line: 12, column: 21, scope: !24)
!42 = !DILocation(line: 13, column: 9, scope: !29)
!43 = !DILocation(line: 5, column: 21, scope: !24)
!44 = !DILocation(line: 6, column: 9, scope: !27)
!45 = !DILocation(line: 13, column: 15, scope: !29)
!46 = !DILocation(line: 19, column: 2, scope: !7)
!47 = !DILocation(line: 14, column: 22, scope: !29)
!48 = !DILocation(line: 14, column: 20, scope: !29)
!49 = !DILocation(line: 14, column: 15, scope: !29)
!50 = !DILocation(line: 14, column: 13, scope: !29)
!51 = !DILocation(line: 15, column: 22, scope: !29)
!52 = !DILocation(line: 15, column: 20, scope: !29)
!53 = !DILocation(line: 15, column: 33, scope: !29)
!54 = !DILocation(line: 15, column: 31, scope: !29)
!55 = !DILocation(line: 15, column: 15, scope: !29)
!56 = !DILocation(line: 15, column: 13, scope: !29)
!57 = !DILocation(line: 16, column: 17, scope: !29)
!58 = !DILocation(line: 16, column: 13, scope: !29)
!59 = !DILocation(line: 6, column: 15, scope: !27)
!60 = !DILocation(line: 7, column: 22, scope: !27)
!61 = !DILocation(line: 7, column: 20, scope: !27)
!62 = !DILocation(line: 7, column: 15, scope: !27)
!63 = !DILocation(line: 7, column: 13, scope: !27)
!64 = !DILocation(line: 8, column: 22, scope: !27)
!65 = !DILocation(line: 8, column: 20, scope: !27)
!66 = !DILocation(line: 8, column: 29, scope: !27)
!67 = !DILocation(line: 8, column: 27, scope: !27)
!68 = !DILocation(line: 8, column: 15, scope: !27)
!69 = !DILocation(line: 8, column: 13, scope: !27)
!70 = !DILocation(line: 9, column: 17, scope: !27)
!71 = !DILocation(line: 9, column: 13, scope: !27)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
