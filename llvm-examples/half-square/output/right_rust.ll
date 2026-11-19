; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_03a35d05e04eaf3719edd360c435efa7 = private unnamed_addr constant [35 x i8] c"llvm-examples/half-square/right.rs\00", align 1
@alloc_5226b2b75d0e08cb6fc5c2c41dda925a = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_03a35d05e04eaf3719edd360c435efa7, [16 x i8] c"\22\00\00\00\00\00\00\00\0C\00\00\00\0D\00\00\00" }>, align 8
@alloc_f8dde4f15ee28c197639570fd35cd7b2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_03a35d05e04eaf3719edd360c435efa7, [16 x i8] c"\22\00\00\00\00\00\00\00\0D\00\00\00\0D\00\00\00" }>, align 8
@alloc_96afc6a1128a90fa2f96d3a013ab6783 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_03a35d05e04eaf3719edd360c435efa7, [16 x i8] c"\22\00\00\00\00\00\00\00\07\00\00\00\0D\00\00\00" }>, align 8
@alloc_154f041ad698425be7055c1e90ab35fe = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_03a35d05e04eaf3719edd360c435efa7, [16 x i8] c"\22\00\00\00\00\00\00\00\08\00\00\00\0D\00\00\00" }>, align 8

; Function Attrs: nounwind nonlazybind uwtable
define void @right(i32 %low, i32 %h) unnamed_addr #0 !dbg !7 {
start:
  %h.dbg.spill = alloca [4 x i8], align 4
  %low.dbg.spill = alloca [4 x i8], align 4
  %v = alloca [4 x i8], align 4
  %y = alloca [4 x i8], align 4
  %i = alloca [4 x i8], align 4
  store i32 %low, ptr %low.dbg.spill, align 4
    #dbg_declare(ptr %low.dbg.spill, !14, !DIExpression(), !23)
  store i32 %h, ptr %h.dbg.spill, align 4
    #dbg_declare(ptr %h.dbg.spill, !15, !DIExpression(), !24)
    #dbg_declare(ptr %i, !16, !DIExpression(), !25)
    #dbg_declare(ptr %y, !18, !DIExpression(), !26)
    #dbg_declare(ptr %v, !20, !DIExpression(), !27)
  store i32 0, ptr %i, align 4, !dbg !28
  store i32 0, ptr %y, align 4, !dbg !29
  store i32 0, ptr %v, align 4, !dbg !30
  br label %bb1, !dbg !31

bb1:                                              ; preds = %bb4, %start
  %_7 = load i32, ptr %i, align 4, !dbg !32
  %_6 = icmp sgt i32 %h, %_7, !dbg !33
  br i1 %_6, label %bb2, label %bb5, !dbg !33

bb5:                                              ; preds = %bb1
  store i32 1, ptr %v, align 4, !dbg !34
  br label %bb6, !dbg !35

bb2:                                              ; preds = %bb1
  %_8 = load i32, ptr %i, align 4, !dbg !36
  %0 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_8, i32 1), !dbg !36
  %_9.0 = extractvalue { i32, i1 } %0, 0, !dbg !36
  %_9.1 = extractvalue { i32, i1 } %0, 1, !dbg !36
  br i1 %_9.1, label %panic2, label %bb3, !dbg !36

bb6:                                              ; preds = %bb9, %bb5
  %_14 = load i32, ptr %i, align 4, !dbg !37
  %_13 = icmp sgt i32 %low, %_14, !dbg !38
  br i1 %_13, label %bb7, label %bb10, !dbg !38

bb10:                                             ; preds = %bb6
  ret void, !dbg !39

bb7:                                              ; preds = %bb6
  %_15 = load i32, ptr %i, align 4, !dbg !40
  %1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_15, i32 1), !dbg !40
  %_16.0 = extractvalue { i32, i1 } %1, 0, !dbg !40
  %_16.1 = extractvalue { i32, i1 } %1, 1, !dbg !40
  br i1 %_16.1, label %panic, label %bb8, !dbg !40

bb8:                                              ; preds = %bb7
  store i32 %_16.0, ptr %i, align 4, !dbg !41
  %_17 = load i32, ptr %y, align 4, !dbg !42
  %_18 = load i32, ptr %y, align 4, !dbg !43
  %2 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_17, i32 %_18), !dbg !42
  %_19.0 = extractvalue { i32, i1 } %2, 0, !dbg !42
  %_19.1 = extractvalue { i32, i1 } %2, 1, !dbg !42
  br i1 %_19.1, label %panic1, label %bb9, !dbg !42

panic:                                            ; preds = %bb7
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_5226b2b75d0e08cb6fc5c2c41dda925a) #3, !dbg !40
  unreachable, !dbg !40

bb9:                                              ; preds = %bb8
  store i32 %_19.0, ptr %y, align 4, !dbg !44
  br label %bb6, !dbg !35

panic1:                                           ; preds = %bb8
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_f8dde4f15ee28c197639570fd35cd7b2) #3, !dbg !42
  unreachable, !dbg !42

bb3:                                              ; preds = %bb2
  store i32 %_9.0, ptr %i, align 4, !dbg !45
  %_10 = load i32, ptr %y, align 4, !dbg !46
  %_11 = load i32, ptr %y, align 4, !dbg !47
  %3 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_10, i32 %_11), !dbg !46
  %_12.0 = extractvalue { i32, i1 } %3, 0, !dbg !46
  %_12.1 = extractvalue { i32, i1 } %3, 1, !dbg !46
  br i1 %_12.1, label %panic3, label %bb4, !dbg !46

panic2:                                           ; preds = %bb2
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_96afc6a1128a90fa2f96d3a013ab6783) #3, !dbg !36
  unreachable, !dbg !36

bb4:                                              ; preds = %bb3
  store i32 %_12.0, ptr %y, align 4, !dbg !48
  br label %bb1, !dbg !31

panic3:                                           ; preds = %bb3
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_154f041ad698425be7055c1e90ab35fe) #3, !dbg !46
  unreachable, !dbg !46
}

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #1

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #2

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
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
!6 = !DIFile(filename: "llvm-examples/half-square/right.rs/@/right.59b4154acb9ecd45-cgu.0", directory: "/kestrel")
!7 = distinct !DISubprogram(name: "right", scope: !9, file: !8, line: 2, type: !10, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !5, templateParams: !22, retainedNodes: !13)
!8 = !DIFile(filename: "llvm-examples/half-square/right.rs", directory: "/kestrel", checksumkind: CSK_MD5, checksum: "b5ae4c684422c79960ff6f7055eaa149")
!9 = !DINamespace(name: "right", scope: null)
!10 = !DISubroutineType(types: !11)
!11 = !{null, !12, !12}
!12 = !DIBasicType(name: "i32", size: 32, encoding: DW_ATE_signed)
!13 = !{!14, !15, !16, !18, !20}
!14 = !DILocalVariable(name: "low", arg: 1, scope: !7, file: !8, line: 2, type: !12)
!15 = !DILocalVariable(name: "h", arg: 2, scope: !7, file: !8, line: 2, type: !12)
!16 = !DILocalVariable(name: "i", scope: !17, file: !8, line: 3, type: !12, align: 32)
!17 = distinct !DILexicalBlock(scope: !7, file: !8, line: 3, column: 5)
!18 = !DILocalVariable(name: "y", scope: !19, file: !8, line: 4, type: !12, align: 32)
!19 = distinct !DILexicalBlock(scope: !17, file: !8, line: 4, column: 5)
!20 = !DILocalVariable(name: "v", scope: !21, file: !8, line: 5, type: !12, align: 32)
!21 = distinct !DILexicalBlock(scope: !19, file: !8, line: 5, column: 5)
!22 = !{}
!23 = !DILocation(line: 2, column: 14, scope: !7)
!24 = !DILocation(line: 2, column: 24, scope: !7)
!25 = !DILocation(line: 3, column: 9, scope: !17)
!26 = !DILocation(line: 4, column: 9, scope: !19)
!27 = !DILocation(line: 5, column: 9, scope: !21)
!28 = !DILocation(line: 3, column: 17, scope: !7)
!29 = !DILocation(line: 4, column: 17, scope: !17)
!30 = !DILocation(line: 5, column: 17, scope: !19)
!31 = !DILocation(line: 6, column: 5, scope: !21)
!32 = !DILocation(line: 6, column: 15, scope: !21)
!33 = !DILocation(line: 6, column: 11, scope: !21)
!34 = !DILocation(line: 10, column: 5, scope: !21)
!35 = !DILocation(line: 11, column: 5, scope: !21)
!36 = !DILocation(line: 7, column: 13, scope: !21)
!37 = !DILocation(line: 11, column: 17, scope: !21)
!38 = !DILocation(line: 11, column: 11, scope: !21)
!39 = !DILocation(line: 15, column: 2, scope: !7)
!40 = !DILocation(line: 12, column: 13, scope: !21)
!41 = !DILocation(line: 12, column: 9, scope: !21)
!42 = !DILocation(line: 13, column: 13, scope: !21)
!43 = !DILocation(line: 13, column: 17, scope: !21)
!44 = !DILocation(line: 13, column: 9, scope: !21)
!45 = !DILocation(line: 7, column: 9, scope: !21)
!46 = !DILocation(line: 8, column: 13, scope: !21)
!47 = !DILocation(line: 8, column: 17, scope: !21)
!48 = !DILocation(line: 8, column: 9, scope: !21)
