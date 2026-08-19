; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_5d2ee394d6cfc9bc3d9d880d91fe8220 = private unnamed_addr constant [38 x i8] c"llvm-examples/loop-alignment/right.rs\00", align 1
@alloc_0b8d4325adacc96c98125829e397f6bf = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5d2ee394d6cfc9bc3d9d880d91fe8220, [16 x i8] c"%\00\00\00\00\00\00\00\09\00\00\00\10\00\00\00" }>, align 8
@alloc_e08b8f2b0a3e293c3668d56d940f8468 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5d2ee394d6cfc9bc3d9d880d91fe8220, [16 x i8] c"%\00\00\00\00\00\00\00\09\00\00\00\09\00\00\00" }>, align 8
@alloc_cc41d17d5a9f127d988c0a9be0945e9f = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5d2ee394d6cfc9bc3d9d880d91fe8220, [16 x i8] c"%\00\00\00\00\00\00\00\0A\00\00\00\14\00\00\00" }>, align 8
@alloc_2a88a997bb9f1e7a11884c35234a2edc = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_5d2ee394d6cfc9bc3d9d880d91fe8220, [16 x i8] c"%\00\00\00\00\00\00\00\0A\00\00\00\09\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(ptr align 4 %a, ptr align 4 %b) unnamed_addr #0 !dbg !7 {
start:
  %n.dbg.spill = alloca [8 x i8], align 8
  %b.dbg.spill = alloca [8 x i8], align 8
  %a.dbg.spill = alloca [8 x i8], align 8
  %d = alloca [84 x i8], align 4
  %j = alloca [8 x i8], align 8
  store ptr %a, ptr %a.dbg.spill, align 8
    #dbg_declare(ptr %a.dbg.spill, !18, !DIExpression(), !28)
  store ptr %b, ptr %b.dbg.spill, align 8
    #dbg_declare(ptr %b.dbg.spill, !19, !DIExpression(), !29)
    #dbg_declare(ptr %j, !23, !DIExpression(), !30)
    #dbg_declare(ptr %d, !25, !DIExpression(), !31)
  store i64 20, ptr %n.dbg.spill, align 8, !dbg !32
    #dbg_declare(ptr %n.dbg.spill, !20, !DIExpression(), !33)
  store i64 1, ptr %j, align 8, !dbg !34
  call void @llvm.memset.p0.i64(ptr align 4 %d, i8 0, i64 84, i1 false), !dbg !35
  %0 = getelementptr inbounds nuw i32, ptr %b, i64 0, !dbg !36
  %_6 = load i32, ptr %0, align 4, !dbg !36
  %1 = getelementptr inbounds nuw i32, ptr %d, i64 1, !dbg !37
  store i32 %_6, ptr %1, align 4, !dbg !37
  br label %bb3, !dbg !38

bb3:                                              ; preds = %bb8, %start
  %_12 = load i64, ptr %j, align 8, !dbg !39
  %_11 = icmp ule i64 %_12, 19, !dbg !39
  br i1 %_11, label %bb4, label %bb9, !dbg !39

bb9:                                              ; preds = %bb3
  %2 = getelementptr inbounds nuw i32, ptr %a, i64 20, !dbg !40
  %_26 = load i32, ptr %2, align 4, !dbg !40
  %3 = getelementptr inbounds nuw i32, ptr %b, i64 20, !dbg !41
  store i32 %_26, ptr %3, align 4, !dbg !41
  ret void, !dbg !42

bb4:                                              ; preds = %bb3
  %_15 = load i64, ptr %j, align 8, !dbg !44
  %_16 = icmp ult i64 %_15, 21, !dbg !45
  br i1 %_16, label %bb5, label %panic, !dbg !45

bb5:                                              ; preds = %bb4
  %4 = getelementptr inbounds nuw i32, ptr %a, i64 %_15, !dbg !45
  %_14 = load i32, ptr %4, align 4, !dbg !45
  %_17 = load i64, ptr %j, align 8, !dbg !46
  %_18 = icmp ult i64 %_17, 21, !dbg !47
  br i1 %_18, label %bb6, label %panic1, !dbg !47

panic:                                            ; preds = %bb4
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_15, i64 21, ptr align 8 @alloc_0b8d4325adacc96c98125829e397f6bf) #3, !dbg !45
  unreachable, !dbg !45

bb6:                                              ; preds = %bb5
  %5 = getelementptr inbounds nuw i32, ptr %b, i64 %_17, !dbg !47
  store i32 %_14, ptr %5, align 4, !dbg !47
  %_20 = load i64, ptr %j, align 8, !dbg !48
  %_21 = icmp ult i64 %_20, 21, !dbg !49
  br i1 %_21, label %bb7, label %panic2, !dbg !49

panic1:                                           ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_17, i64 21, ptr align 8 @alloc_e08b8f2b0a3e293c3668d56d940f8468) #3, !dbg !47
  unreachable, !dbg !47

bb7:                                              ; preds = %bb6
  %6 = getelementptr inbounds nuw i32, ptr %b, i64 %_20, !dbg !49
  %_19 = load i32, ptr %6, align 4, !dbg !49
  %_23 = load i64, ptr %j, align 8, !dbg !50
  %_22 = add i64 %_23, 1, !dbg !50
  %_24 = icmp ult i64 %_22, 21, !dbg !51
  br i1 %_24, label %bb8, label %panic3, !dbg !51

panic2:                                           ; preds = %bb6
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_20, i64 21, ptr align 8 @alloc_cc41d17d5a9f127d988c0a9be0945e9f) #3, !dbg !49
  unreachable, !dbg !49

bb8:                                              ; preds = %bb7
  %7 = getelementptr inbounds nuw i32, ptr %d, i64 %_22, !dbg !51
  store i32 %_19, ptr %7, align 4, !dbg !51
  %_25 = load i64, ptr %j, align 8, !dbg !52
  %8 = add i64 %_25, 1, !dbg !53
  store i64 %8, ptr %j, align 8, !dbg !53
  br label %bb3, !dbg !38

panic3:                                           ; preds = %bb7
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_22, i64 21, ptr align 8 @alloc_2a88a997bb9f1e7a11884c35234a2edc) #3, !dbg !51
  unreachable, !dbg !51
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #1

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #2 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
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
!6 = !DIFile(filename: "llvm-examples/loop-alignment/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !27, retainedNodes: !17)
!8 = !DIFile(filename: "llvm-examples/loop-alignment/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "d1689f2b8fe5e039edf83eca4ebccffc")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12}
!12 = !DIDerivedType(tag: DW_TAG_pointer_type, name: "&mut [i32; 21]", baseType: !13, size: 64, align: 64, dwarfAddressSpace: 0)
!13 = !DICompositeType(tag: DW_TAG_array_type, baseType: !14, size: 672, align: 32, elements: !15)
!14 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!15 = !{!16}
!16 = !DISubrange(count: 21, lowerBound: 0)
!17 = !{!18, !19, !20, !23, !25}
!18 = !DILocalVariable(name: "a", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!19 = !DILocalVariable(name: "b", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!20 = !DILocalVariable(name: "n", scope: !21, file: !8, line: 3, type: !22, align: 64)
!21 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!22 = !DIBasicType(name: "usize", size: 64, encoding: DW_ATE_unsigned)
!23 = !DILocalVariable(name: "j", scope: !24, file: !8, line: 4, type: !22, align: 64)
!24 = distinct !DILexicalBlock(scope: !21, file: !8, line: 4, column: 5)
!25 = !DILocalVariable(name: "d", scope: !26, file: !8, line: 5, type: !13, align: 32)
!26 = distinct !DILexicalBlock(scope: !24, file: !8, line: 5, column: 5)
!27 = !{}
!28 = !DILocation(line: 2, column: 14, scope: !7)
!29 = !DILocation(line: 2, column: 33, scope: !7)
!30 = !DILocation(line: 4, column: 9, scope: !24)
!31 = !DILocation(line: 5, column: 9, scope: !26)
!32 = !DILocation(line: 3, column: 13, scope: !7)
!33 = !DILocation(line: 3, column: 9, scope: !21)
!34 = !DILocation(line: 4, column: 17, scope: !21)
!35 = !DILocation(line: 5, column: 17, scope: !24)
!36 = !DILocation(line: 7, column: 12, scope: !26)
!37 = !DILocation(line: 7, column: 5, scope: !26)
!38 = !DILocation(line: 8, column: 5, scope: !26)
!39 = !DILocation(line: 8, column: 11, scope: !26)
!40 = !DILocation(line: 13, column: 12, scope: !26)
!41 = !DILocation(line: 13, column: 5, scope: !26)
!42 = !DILocation(line: 14, column: 2, scope: !43)
!43 = !DILexicalBlockFile(scope: !7, file: !8, discriminator: 0)
!44 = !DILocation(line: 9, column: 18, scope: !26)
!45 = !DILocation(line: 9, column: 16, scope: !26)
!46 = !DILocation(line: 9, column: 11, scope: !26)
!47 = !DILocation(line: 9, column: 9, scope: !26)
!48 = !DILocation(line: 10, column: 22, scope: !26)
!49 = !DILocation(line: 10, column: 20, scope: !26)
!50 = !DILocation(line: 10, column: 11, scope: !26)
!51 = !DILocation(line: 10, column: 9, scope: !26)
!52 = !DILocation(line: 11, column: 13, scope: !26)
!53 = !DILocation(line: 11, column: 9, scope: !26)
