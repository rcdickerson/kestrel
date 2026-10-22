; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_73bde3e7b336b23eb02372fcd1f1cbca = private unnamed_addr constant [35 x i8] c"llvm-examples/loop-tiling/right.rs\00", align 1
@alloc_dad866affc51c6a11cc22d96a0bd7a9d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_73bde3e7b336b23eb02372fcd1f1cbca, [16 x i8] c"\22\00\00\00\00\00\00\00\0E\00\00\00\0D\00\00\00" }>, align 8
@alloc_b9657f3f085e25834298a1b8ce58ca04 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_73bde3e7b336b23eb02372fcd1f1cbca, [16 x i8] c"\22\00\00\00\00\00\00\00\0B\00\00\00\1A\00\00\00" }>, align 8
@alloc_d856e642920ae99522851566029b1170 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_73bde3e7b336b23eb02372fcd1f1cbca, [16 x i8] c"\22\00\00\00\00\00\00\00\0B\00\00\00\19\00\00\00" }>, align 8
@alloc_a549888368d39939078ca63aa1dda3a4 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_73bde3e7b336b23eb02372fcd1f1cbca, [16 x i8] c"\22\00\00\00\00\00\00\00\0B\00\00\00\0D\00\00\00" }>, align 8
@alloc_fdb4c44327b85399d26ef100d2b9a33e = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_73bde3e7b336b23eb02372fcd1f1cbca, [16 x i8] c"\22\00\00\00\00\00\00\00\0C\00\00\00\11\00\00\00" }>, align 8

; right::f
; Function Attrs: nounwind nonlazybind uwtable
define i32 @_RNvCs7Hul5VkTjfJ_5right1f(i32 %x) unnamed_addr #0 !dbg !7 {
start:
  %x.dbg.spill = alloca [4 x i8], align 4
  store i32 %x, ptr %x.dbg.spill, align 4
  call void @llvm.dbg.declare(metadata ptr %x.dbg.spill, metadata !14, metadata !DIExpression()), !dbg !16
  ret i32 %x, !dbg !17
}

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a) unnamed_addr #0 !dbg !18 {
start:
  %n.dbg.spill = alloca [8 x i8], align 8
  %m.dbg.spill = alloca [8 x i8], align 8
  %a.dbg.spill = alloca [8 x i8], align 8
  %j = alloca [8 x i8], align 8
  %i = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
  call void @llvm.dbg.declare(metadata ptr %a.dbg.spill, metadata !27, metadata !DIExpression()), !dbg !37
  call void @llvm.dbg.declare(metadata ptr %i, metadata !33, metadata !DIExpression()), !dbg !38
  call void @llvm.dbg.declare(metadata ptr %j, metadata !35, metadata !DIExpression()), !dbg !39
  store i64 10, ptr %m.dbg.spill, align 8, !dbg !40
  call void @llvm.dbg.declare(metadata ptr %m.dbg.spill, metadata !31, metadata !DIExpression()), !dbg !40
  store i64 10, ptr %n.dbg.spill, align 8, !dbg !41
  call void @llvm.dbg.declare(metadata ptr %n.dbg.spill, metadata !28, metadata !DIExpression()), !dbg !42
  store i64 0, ptr %i, align 8, !dbg !43
  br label %bb1, !dbg !44

bb1:                                              ; preds = %bb12, %start
  %_5 = load i64, ptr %i, align 8, !dbg !45
  %_4 = icmp ult i64 %_5, 10, !dbg !45
  br i1 %_4, label %bb2, label %bb13, !dbg !45

bb13:                                             ; preds = %bb1
  ret void, !dbg !46

bb2:                                              ; preds = %bb1
  store i64 0, ptr %j, align 8, !dbg !48
  br label %bb3, !dbg !49

bb3:                                              ; preds = %bb10, %bb2
  %_8 = load i64, ptr %j, align 8, !dbg !50
  %_7 = icmp ult i64 %_8, 10, !dbg !50
  br i1 %_7, label %bb4, label %bb11, !dbg !50

bb11:                                             ; preds = %bb3
  %_24 = load i64, ptr %i, align 8, !dbg !51
  %_25.0 = add i64 %_24, 1, !dbg !51
  %_25.1 = icmp ult i64 %_25.0, %_24, !dbg !51
  br i1 %_25.1, label %panic, label %bb12, !dbg !51

bb4:                                              ; preds = %bb3
  %_14 = load i64, ptr %i, align 8, !dbg !52
  %0 = call { i64, i1 } @llvm.umul.with.overflow.i64(i64 %_14, i64 10), !dbg !52
  %_15.0 = extractvalue { i64, i1 } %0, 0, !dbg !52
  %_15.1 = extractvalue { i64, i1 } %0, 1, !dbg !52
  br i1 %_15.1, label %panic1, label %bb5, !dbg !52

bb12:                                             ; preds = %bb11
  store i64 %_25.0, ptr %i, align 8, !dbg !53
  br label %bb1, !dbg !44

panic:                                            ; preds = %bb11
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_dad866affc51c6a11cc22d96a0bd7a9d) #4, !dbg !51
  unreachable, !dbg !51

bb5:                                              ; preds = %bb4
  %_16 = load i64, ptr %j, align 8, !dbg !54
  %_17.0 = add i64 %_15.0, %_16, !dbg !55
  %_17.1 = icmp ult i64 %_17.0, %_15.0, !dbg !55
  br i1 %_17.1, label %panic2, label %bb6, !dbg !55

panic1:                                           ; preds = %bb4
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8 @alloc_b9657f3f085e25834298a1b8ce58ca04) #4, !dbg !52
  unreachable, !dbg !52

bb6:                                              ; preds = %bb5
  %_11 = trunc i64 %_17.0 to i32, !dbg !55
; call right::f
  %_10 = call i32 @_RNvCs7Hul5VkTjfJ_5right1f(i32 %_11) #5, !dbg !56
  %_18 = load i64, ptr %i, align 8, !dbg !57
  %_19 = icmp ult i64 %_18, 10, !dbg !58
  br i1 %_19, label %bb8, label %panic3, !dbg !58

panic2:                                           ; preds = %bb5
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_d856e642920ae99522851566029b1170) #4, !dbg !55
  unreachable, !dbg !55

bb8:                                              ; preds = %bb6
  %_20 = load i64, ptr %j, align 8, !dbg !59
  %_21 = icmp ult i64 %_20, 10, !dbg !58
  br i1 %_21, label %bb9, label %panic4, !dbg !58

panic3:                                           ; preds = %bb6
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_18, i64 10, ptr align 8 @alloc_a549888368d39939078ca63aa1dda3a4) #4, !dbg !58
  unreachable, !dbg !58

bb9:                                              ; preds = %bb8
  %1 = getelementptr inbounds [10 x i32], ptr %a, i64 %_18, !dbg !58
  %2 = getelementptr inbounds i32, ptr %1, i64 %_20, !dbg !58
  store i32 %_10, ptr %2, align 4, !dbg !58
  %_22 = load i64, ptr %j, align 8, !dbg !60
  %_23.0 = add i64 %_22, 1, !dbg !60
  %_23.1 = icmp ult i64 %_23.0, %_22, !dbg !60
  br i1 %_23.1, label %panic5, label %bb10, !dbg !60

panic4:                                           ; preds = %bb8
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_20, i64 10, ptr align 8 @alloc_a549888368d39939078ca63aa1dda3a4) #4, !dbg !58
  unreachable, !dbg !58

bb10:                                             ; preds = %bb9
  store i64 %_23.0, ptr %j, align 8, !dbg !61
  br label %bb3, !dbg !49

panic5:                                           ; preds = %bb9
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_fdb4c44327b85399d26ef100d2b9a33e) #4, !dbg !60
  unreachable, !dbg !60
}

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #1

; Function Attrs: nosync nounwind speculatable
declare { i64, i1 } @llvm.umul.with.overflow.i64(i64, i64) #2

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8) unnamed_addr #1

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #3

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nosync nounwind speculatable }
attributes #3 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { noreturn nounwind }
attributes #5 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}
!llvm.dbg.cu = !{!5}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"Dwarf Version", i32 4}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{!"rustc version 1.97.0 (2d8144b78 2026-07-07)"}
!5 = distinct !DICompileUnit(language: DW_LANG_Rust, file: !6, producer: "clang LLVM (rustc version 1.97.0 (2d8144b78 2026-07-07))", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!6 = !DIFile(filename: "llvm-examples/loop-tiling/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "f", linkageName: "_RNvCs7Hul5VkTjfJ_5right1f", scope: !9, file: !8, line: 1, type: !10, scopeLine: 1, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !15, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/loop-tiling/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "ea1e5f127a3da6a475868c18c29e7e2e")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{!12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14}
!14 = !DILocalVariable(name: "x", arg: 1, scope: !7, file: !8, line: 1, type: !12)
!15 = !{}
!16 = !DILocation(line: 1, column: 10, scope: !7)
!17 = !DILocation(line: 1, column: 30, scope: !7)
!18 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 4, type: !19, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !15, retainedNodes: !26)
!19 = !DISubroutineType(types: !20)
!20 = !{null, !21}
!21 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [[i32; 10]; 10]", baseType: !22, size: 64, align: 64, dwarfAddressSpace: 0)
!22 = !DICompositeType(tag: DW_TAG_array_type, baseType: !23, size: 3200, align: 32, elements: !24)
!23 = !DICompositeType(tag: DW_TAG_array_type, baseType: !12, size: 320, align: 32, elements: !24)
!24 = !{!25}
!25 = !DISubrange(count: 10, lowerBound: 0)
!26 = !{!27, !28, !31, !33, !35}
!27 = !DILocalVariable(name: "a", arg: 1, scope: !18, file: !8, line: 4, type: !21)
!28 = !DILocalVariable(name: "n", scope: !29, file: !8, line: 5, type: !30, align: 64)
!29 = distinct !DILexicalBlock(scope: !18, file: !8, line: 5, column: 5)
!30 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!31 = !DILocalVariable(name: "m", scope: !32, file: !8, line: 6, type: !30, align: 64)
!32 = distinct !DILexicalBlock(scope: !29, file: !8, line: 6, column: 5)
!33 = !DILocalVariable(name: "i", scope: !34, file: !8, line: 7, type: !30, align: 64)
!34 = distinct !DILexicalBlock(scope: !32, file: !8, line: 7, column: 5)
!35 = !DILocalVariable(name: "j", scope: !36, file: !8, line: 9, type: !30, align: 64)
!36 = distinct !DILexicalBlock(scope: !34, file: !8, line: 9, column: 9)
!37 = !DILocation(line: 4, column: 14, scope: !18)
!38 = !DILocation(line: 7, column: 9, scope: !34)
!39 = !DILocation(line: 9, column: 13, scope: !36)
!40 = !DILocation(line: 6, column: 9, scope: !32)
!41 = !DILocation(line: 5, column: 13, scope: !18)
!42 = !DILocation(line: 5, column: 9, scope: !29)
!43 = !DILocation(line: 7, column: 17, scope: !32)
!44 = !DILocation(line: 8, column: 5, scope: !34)
!45 = !DILocation(line: 8, column: 11, scope: !34)
!46 = !DILocation(line: 16, column: 2, scope: !47)
!47 = !DILexicalBlockFile(scope: !18, file: !8, discriminator: 0)
!48 = !DILocation(line: 9, column: 21, scope: !34)
!49 = !DILocation(line: 10, column: 9, scope: !36)
!50 = !DILocation(line: 10, column: 15, scope: !36)
!51 = !DILocation(line: 14, column: 13, scope: !36)
!52 = !DILocation(line: 11, column: 26, scope: !36)
!53 = !DILocation(line: 14, column: 9, scope: !36)
!54 = !DILocation(line: 11, column: 34, scope: !36)
!55 = !DILocation(line: 11, column: 25, scope: !36)
!56 = !DILocation(line: 11, column: 23, scope: !36)
!57 = !DILocation(line: 11, column: 15, scope: !36)
!58 = !DILocation(line: 11, column: 13, scope: !36)
!59 = !DILocation(line: 11, column: 18, scope: !36)
!60 = !DILocation(line: 12, column: 17, scope: !36)
!61 = !DILocation(line: 12, column: 13, scope: !36)

declare void @llvm.dbg.declare(metadata, metadata, metadata)
