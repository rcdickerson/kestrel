; ModuleID = 'right.59b4154acb9ecd45-cgu.0'
source_filename = "right.59b4154acb9ecd45-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@alloc_df9fb36b3e50035d5a26429439c29ed9 = private unnamed_addr constant [40 x i8] c"llvm-examples/loop-unswitching/right.rs\00", align 1
@alloc_419ef0d9175c3c3d25b6349e67ee0cbd = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0E\00\00\00\14\00\00\00" }>, align 8
@alloc_d2d5579a465f4b0e260596020158df10 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0E\00\00\00\0D\00\00\00" }>, align 8
@alloc_3851e86263c4f1dc61060dfc24bfb5f8 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\16\00\00\00" }>, align 8
@alloc_e3f13fad5a0fb42e992397669711c193 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\14\00\00\00" }>, align 8
@alloc_a71056d669a165115308cd734a984c01 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00!\00\00\00" }>, align 8
@alloc_bb2f62fcbec2afd6481e273b7e37fcc1 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\1F\00\00\00" }>, align 8
@alloc_31ffd0f23462b2f4117f2c5301d8027b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\0F\00\00\00\0D\00\00\00" }>, align 8
@alloc_abbc3ba085879e0c58420fdd90df364b = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\10\00\00\00\11\00\00\00" }>, align 8
@alloc_a431e0af1f0a773d7894a8f7648fcbbb = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\07\00\00\00\14\00\00\00" }>, align 8
@alloc_86a95f0408d87e2b4012bd6715ad108d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\07\00\00\00\0D\00\00\00" }>, align 8
@alloc_72db5233068273f5dabaebf836ed1389 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\14\00\00\00" }>, align 8
@alloc_40b9f4e097b3d8001419ebb57560c155 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\1B\00\00\00" }>, align 8
@alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2 = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\08\00\00\00\0D\00\00\00" }>, align 8
@alloc_9a0d9beb0fd0d5747443c939bdea398d = private unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_df9fb36b3e50035d5a26429439c29ed9, [16 x i8] c"'\00\00\00\00\00\00\00\09\00\00\00\11\00\00\00" }>, align 8

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
    #dbg_declare(ptr %a.dbg.spill, !18, !DIExpression(), !31)
  store ptr %b, ptr %b.dbg.spill, align 8
    #dbg_declare(ptr %b.dbg.spill, !19, !DIExpression(), !32)
  store ptr %c, ptr %c.dbg.spill, align 8
    #dbg_declare(ptr %c.dbg.spill, !20, !DIExpression(), !33)
  store i32 %k, ptr %k.dbg.spill, align 4
    #dbg_declare(ptr %k.dbg.spill, !21, !DIExpression(), !34)
  store i32 %x, ptr %x.dbg.spill, align 4
    #dbg_declare(ptr %x.dbg.spill, !22, !DIExpression(), !35)
    #dbg_declare(ptr %j, !26, !DIExpression(), !36)
    #dbg_declare(ptr %j1, !28, !DIExpression(), !37)
  store i64 10, ptr %n.dbg.spill, align 8, !dbg !38
    #dbg_declare(ptr %n.dbg.spill, !23, !DIExpression(), !39)
  %_7 = icmp slt i32 %x, 7, !dbg !40
  br i1 %_7, label %bb1, label %bb12, !dbg !40

bb12:                                             ; preds = %start
  store i64 0, ptr %j1, align 8, !dbg !41
  br label %bb13, !dbg !42

bb1:                                              ; preds = %start
  store i64 0, ptr %j, align 8, !dbg !43
  br label %bb2, !dbg !44

bb13:                                             ; preds = %bb24, %bb12
  %_30 = load i64, ptr %j1, align 8, !dbg !45
  %_29 = icmp ult i64 %_30, 10, !dbg !45
  br i1 %_29, label %bb14, label %bb25, !dbg !45

bb25:                                             ; preds = %bb2, %bb13
  ret void, !dbg !46

bb14:                                             ; preds = %bb13
  %_32 = load i64, ptr %j1, align 8, !dbg !47
  %_33 = icmp ult i64 %_32, 10, !dbg !48
  br i1 %_33, label %bb15, label %panic, !dbg !48

bb15:                                             ; preds = %bb14
  %0 = getelementptr inbounds nuw i32, ptr %a, i64 %_32, !dbg !48
  %_31 = load i32, ptr %0, align 4, !dbg !48
  %1 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_31, i32 %k), !dbg !48
  %_34.0 = extractvalue { i32, i1 } %1, 0, !dbg !48
  %_34.1 = extractvalue { i32, i1 } %1, 1, !dbg !48
  br i1 %_34.1, label %panic2, label %bb16, !dbg !48

panic:                                            ; preds = %bb14
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_32, i64 10, ptr align 8 @alloc_419ef0d9175c3c3d25b6349e67ee0cbd) #4, !dbg !48
  unreachable, !dbg !48

bb16:                                             ; preds = %bb15
  %_35 = load i64, ptr %j1, align 8, !dbg !49
  %_36 = icmp ult i64 %_35, 10, !dbg !50
  br i1 %_36, label %bb17, label %panic3, !dbg !50

panic2:                                           ; preds = %bb15
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_419ef0d9175c3c3d25b6349e67ee0cbd) #4, !dbg !48
  unreachable, !dbg !48

bb17:                                             ; preds = %bb16
  %2 = getelementptr inbounds nuw i32, ptr %a, i64 %_35, !dbg !50
  store i32 %_34.0, ptr %2, align 4, !dbg !50
  %_39 = load i64, ptr %j1, align 8, !dbg !51
  %_40.0 = sub i64 %_39, 1, !dbg !51
  %_40.1 = icmp ult i64 %_39, 1, !dbg !51
  br i1 %_40.1, label %panic4, label %bb18, !dbg !51

panic3:                                           ; preds = %bb16
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_35, i64 10, ptr align 8 @alloc_d2d5579a465f4b0e260596020158df10) #4, !dbg !50
  unreachable, !dbg !50

bb18:                                             ; preds = %bb17
  %_41 = icmp ult i64 %_40.0, 10, !dbg !52
  br i1 %_41, label %bb19, label %panic5, !dbg !52

panic4:                                           ; preds = %bb17
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8 @alloc_3851e86263c4f1dc61060dfc24bfb5f8) #4, !dbg !51
  unreachable, !dbg !51

bb19:                                             ; preds = %bb18
  %3 = getelementptr inbounds nuw i32, ptr %a, i64 %_40.0, !dbg !52
  %_37 = load i32, ptr %3, align 4, !dbg !52
  %_44 = load i64, ptr %j1, align 8, !dbg !53
  %_45.0 = sub i64 %_44, 1, !dbg !53
  %_45.1 = icmp ult i64 %_44, 1, !dbg !53
  br i1 %_45.1, label %panic6, label %bb20, !dbg !53

panic5:                                           ; preds = %bb18
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_40.0, i64 10, ptr align 8 @alloc_e3f13fad5a0fb42e992397669711c193) #4, !dbg !52
  unreachable, !dbg !52

bb20:                                             ; preds = %bb19
  %_46 = icmp ult i64 %_45.0, 10, !dbg !54
  br i1 %_46, label %bb21, label %panic7, !dbg !54

panic6:                                           ; preds = %bb19
; call core::panicking::panic_const::panic_const_sub_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8 @alloc_a71056d669a165115308cd734a984c01) #4, !dbg !53
  unreachable, !dbg !53

bb21:                                             ; preds = %bb20
  %4 = getelementptr inbounds nuw i32, ptr %b, i64 %_45.0, !dbg !54
  %_42 = load i32, ptr %4, align 4, !dbg !54
  %5 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %_37, i32 %_42), !dbg !52
  %_47.0 = extractvalue { i32, i1 } %5, 0, !dbg !52
  %_47.1 = extractvalue { i32, i1 } %5, 1, !dbg !52
  br i1 %_47.1, label %panic8, label %bb22, !dbg !52

panic7:                                           ; preds = %bb20
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_45.0, i64 10, ptr align 8 @alloc_bb2f62fcbec2afd6481e273b7e37fcc1) #4, !dbg !54
  unreachable, !dbg !54

bb22:                                             ; preds = %bb21
  %_48 = load i64, ptr %j1, align 8, !dbg !55
  %_49 = icmp ult i64 %_48, 10, !dbg !56
  br i1 %_49, label %bb23, label %panic9, !dbg !56

panic8:                                           ; preds = %bb21
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8 @alloc_e3f13fad5a0fb42e992397669711c193) #4, !dbg !52
  unreachable, !dbg !52

bb23:                                             ; preds = %bb22
  %6 = getelementptr inbounds nuw i32, ptr %b, i64 %_48, !dbg !56
  store i32 %_47.0, ptr %6, align 4, !dbg !56
  %_50 = load i64, ptr %j1, align 8, !dbg !57
  %_51.0 = add i64 %_50, 1, !dbg !57
  %_51.1 = icmp ult i64 %_51.0, %_50, !dbg !57
  br i1 %_51.1, label %panic10, label %bb24, !dbg !57

panic9:                                           ; preds = %bb22
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_48, i64 10, ptr align 8 @alloc_31ffd0f23462b2f4117f2c5301d8027b) #4, !dbg !56
  unreachable, !dbg !56

bb24:                                             ; preds = %bb23
  store i64 %_51.0, ptr %j1, align 8, !dbg !58
  br label %bb13, !dbg !42

panic10:                                          ; preds = %bb23
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_abbc3ba085879e0c58420fdd90df364b) #4, !dbg !57
  unreachable, !dbg !57

bb2:                                              ; preds = %bb11, %bb1
  %_10 = load i64, ptr %j, align 8, !dbg !59
  %_9 = icmp ult i64 %_10, 10, !dbg !59
  br i1 %_9, label %bb3, label %bb25, !dbg !59

bb3:                                              ; preds = %bb2
  %_12 = load i64, ptr %j, align 8, !dbg !60
  %_13 = icmp ult i64 %_12, 10, !dbg !61
  br i1 %_13, label %bb4, label %panic11, !dbg !61

bb4:                                              ; preds = %bb3
  %7 = getelementptr inbounds nuw i32, ptr %a, i64 %_12, !dbg !61
  %_11 = load i32, ptr %7, align 4, !dbg !61
  %8 = call { i32, i1 } @llvm.sadd.with.overflow.i32(i32 %_11, i32 %k), !dbg !61
  %_14.0 = extractvalue { i32, i1 } %8, 0, !dbg !61
  %_14.1 = extractvalue { i32, i1 } %8, 1, !dbg !61
  br i1 %_14.1, label %panic12, label %bb5, !dbg !61

panic11:                                          ; preds = %bb3
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_12, i64 10, ptr align 8 @alloc_a431e0af1f0a773d7894a8f7648fcbbb) #4, !dbg !61
  unreachable, !dbg !61

bb5:                                              ; preds = %bb4
  %_15 = load i64, ptr %j, align 8, !dbg !62
  %_16 = icmp ult i64 %_15, 10, !dbg !63
  br i1 %_16, label %bb6, label %panic13, !dbg !63

panic12:                                          ; preds = %bb4
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_a431e0af1f0a773d7894a8f7648fcbbb) #4, !dbg !61
  unreachable, !dbg !61

bb6:                                              ; preds = %bb5
  %9 = getelementptr inbounds nuw i32, ptr %a, i64 %_15, !dbg !63
  store i32 %_14.0, ptr %9, align 4, !dbg !63
  %_18 = load i64, ptr %j, align 8, !dbg !64
  %_19 = icmp ult i64 %_18, 10, !dbg !65
  br i1 %_19, label %bb7, label %panic14, !dbg !65

panic13:                                          ; preds = %bb5
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_15, i64 10, ptr align 8 @alloc_86a95f0408d87e2b4012bd6715ad108d) #4, !dbg !63
  unreachable, !dbg !63

bb7:                                              ; preds = %bb6
  %10 = getelementptr inbounds nuw i32, ptr %a, i64 %_18, !dbg !65
  %_17 = load i32, ptr %10, align 4, !dbg !65
  %_21 = load i64, ptr %j, align 8, !dbg !66
  %_22 = icmp ult i64 %_21, 10, !dbg !67
  br i1 %_22, label %bb8, label %panic15, !dbg !67

panic14:                                          ; preds = %bb6
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_18, i64 10, ptr align 8 @alloc_72db5233068273f5dabaebf836ed1389) #4, !dbg !65
  unreachable, !dbg !65

bb8:                                              ; preds = %bb7
  %11 = getelementptr inbounds nuw i32, ptr %c, i64 %_21, !dbg !67
  %_20 = load i32, ptr %11, align 4, !dbg !67
  %12 = call { i32, i1 } @llvm.smul.with.overflow.i32(i32 %_17, i32 %_20), !dbg !65
  %_23.0 = extractvalue { i32, i1 } %12, 0, !dbg !65
  %_23.1 = extractvalue { i32, i1 } %12, 1, !dbg !65
  br i1 %_23.1, label %panic16, label %bb9, !dbg !65

panic15:                                          ; preds = %bb7
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_21, i64 10, ptr align 8 @alloc_40b9f4e097b3d8001419ebb57560c155) #4, !dbg !67
  unreachable, !dbg !67

bb9:                                              ; preds = %bb8
  %_24 = load i64, ptr %j, align 8, !dbg !68
  %_25 = icmp ult i64 %_24, 10, !dbg !69
  br i1 %_25, label %bb10, label %panic17, !dbg !69

panic16:                                          ; preds = %bb8
; call core::panicking::panic_const::panic_const_mul_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8 @alloc_72db5233068273f5dabaebf836ed1389) #4, !dbg !65
  unreachable, !dbg !65

bb10:                                             ; preds = %bb9
  %13 = getelementptr inbounds nuw i32, ptr %b, i64 %_24, !dbg !69
  store i32 %_23.0, ptr %13, align 4, !dbg !69
  %_26 = load i64, ptr %j, align 8, !dbg !70
  %_27.0 = add i64 %_26, 1, !dbg !70
  %_27.1 = icmp ult i64 %_27.0, %_26, !dbg !70
  br i1 %_27.1, label %panic18, label %bb11, !dbg !70

panic17:                                          ; preds = %bb9
; call core::panicking::panic_bounds_check
  call void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64 %_24, i64 10, ptr align 8 @alloc_6ccfbbdd552b4c0101c2de9d1f6e9ee2) #4, !dbg !69
  unreachable, !dbg !69

bb11:                                             ; preds = %bb10
  store i64 %_27.0, ptr %j, align 8, !dbg !71
  br label %bb2, !dbg !44

panic18:                                          ; preds = %bb10
; call core::panicking::panic_const::panic_const_add_overflow
  call void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8 @alloc_9a0d9beb0fd0d5747443c939bdea398d) #4, !dbg !70
  unreachable, !dbg !70
}

; core::panicking::panic_bounds_check
; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCscI6d9CVNmLh_4core9panicking18panic_bounds_check(i64, i64, ptr align 8) unnamed_addr #1

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.sadd.with.overflow.i32(i32, i32) #2

; core::panicking::panic_const::panic_const_add_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_add_overflow(ptr align 8) unnamed_addr #3

; core::panicking::panic_const::panic_const_sub_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_sub_overflow(ptr align 8) unnamed_addr #3

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare { i32, i1 } @llvm.smul.with.overflow.i32(i32, i32) #2

; core::panicking::panic_const::panic_const_mul_overflow
; Function Attrs: cold noinline noreturn nounwind nonlazybind uwtable
declare void @_RNvNtNtCscI6d9CVNmLh_4core9panicking11panic_const24panic_const_mul_overflow(ptr align 8) unnamed_addr #3

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #3 = { cold noinline noreturn nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { noreturn nounwind }

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
