; ModuleID = 'vec.c'
source_filename = "vec.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @vec_expand_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3) #0 {
  %5 = alloca i32, align 4
  %6 = alloca ptr, align 8
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca i32, align 4
  %10 = alloca ptr, align 8
  %11 = alloca i32, align 4
  store ptr %0, ptr %6, align 8
  store ptr %1, ptr %7, align 8
  store ptr %2, ptr %8, align 8
  store i32 %3, ptr %9, align 4
  %12 = load ptr, ptr %7, align 8
  %13 = load i32, ptr %12, align 4
  %14 = add nsw i32 %13, 1
  %15 = load ptr, ptr %8, align 8
  %16 = load i32, ptr %15, align 4
  %17 = icmp sgt i32 %14, %16
  br i1 %17, label %18, label %44

18:                                               ; preds = %4
  %19 = load ptr, ptr %8, align 8
  %20 = load i32, ptr %19, align 4
  %21 = icmp eq i32 %20, 0
  br i1 %21, label %22, label %23

22:                                               ; preds = %18
  br label %27

23:                                               ; preds = %18
  %24 = load ptr, ptr %8, align 8
  %25 = load i32, ptr %24, align 4
  %26 = shl i32 %25, 1
  br label %27

27:                                               ; preds = %23, %22
  %28 = phi i32 [ 1, %22 ], [ %26, %23 ]
  store i32 %28, ptr %11, align 4
  %29 = load ptr, ptr %6, align 8
  %30 = load ptr, ptr %29, align 8
  %31 = load i32, ptr %11, align 4
  %32 = load i32, ptr %9, align 4
  %33 = mul nsw i32 %31, %32
  %34 = sext i32 %33 to i64
  %35 = call ptr @realloc(ptr noundef %30, i64 noundef %34) #4
  store ptr %35, ptr %10, align 8
  %36 = load ptr, ptr %10, align 8
  %37 = icmp eq ptr %36, null
  br i1 %37, label %38, label %39

38:                                               ; preds = %27
  store i32 -1, ptr %5, align 4
  br label %45

39:                                               ; preds = %27
  %40 = load ptr, ptr %10, align 8
  %41 = load ptr, ptr %6, align 8
  store ptr %40, ptr %41, align 8
  %42 = load i32, ptr %11, align 4
  %43 = load ptr, ptr %8, align 8
  store i32 %42, ptr %43, align 4
  br label %44

44:                                               ; preds = %39, %4
  store i32 0, ptr %5, align 4
  br label %45

45:                                               ; preds = %44, %38
  %46 = load i32, ptr %5, align 4
  ret i32 %46
}

; Function Attrs: nounwind allocsize(1)
declare ptr @realloc(ptr noundef, i64 noundef) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @vec_reserve_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4) #0 {
  %6 = alloca i32, align 4
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca ptr, align 8
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  %13 = load ptr, ptr %8, align 8
  %14 = load i32, ptr %11, align 4
  %15 = load ptr, ptr %9, align 8
  %16 = load i32, ptr %15, align 4
  %17 = icmp sgt i32 %14, %16
  br i1 %17, label %18, label %34

18:                                               ; preds = %5
  %19 = load ptr, ptr %7, align 8
  %20 = load ptr, ptr %19, align 8
  %21 = load i32, ptr %11, align 4
  %22 = load i32, ptr %10, align 4
  %23 = mul nsw i32 %21, %22
  %24 = sext i32 %23 to i64
  %25 = call ptr @realloc(ptr noundef %20, i64 noundef %24) #4
  store ptr %25, ptr %12, align 8
  %26 = load ptr, ptr %12, align 8
  %27 = icmp eq ptr %26, null
  br i1 %27, label %28, label %29

28:                                               ; preds = %18
  store i32 -1, ptr %6, align 4
  br label %35

29:                                               ; preds = %18
  %30 = load ptr, ptr %12, align 8
  %31 = load ptr, ptr %7, align 8
  store ptr %30, ptr %31, align 8
  %32 = load i32, ptr %11, align 4
  %33 = load ptr, ptr %9, align 8
  store i32 %32, ptr %33, align 4
  br label %34

34:                                               ; preds = %29, %5
  store i32 0, ptr %6, align 4
  br label %35

35:                                               ; preds = %34, %28
  %36 = load i32, ptr %6, align 4
  ret i32 %36
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @vec_reserve_po2_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4) #0 {
  %6 = alloca i32, align 4
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  store i32 1, ptr %12, align 4
  %13 = load i32, ptr %11, align 4
  %14 = icmp eq i32 %13, 0
  br i1 %14, label %15, label %16

15:                                               ; preds = %5
  store i32 0, ptr %6, align 4
  br label %31

16:                                               ; preds = %5
  br label %17

17:                                               ; preds = %21, %16
  %18 = load i32, ptr %12, align 4
  %19 = load i32, ptr %11, align 4
  %20 = icmp slt i32 %18, %19
  br i1 %20, label %21, label %24

21:                                               ; preds = %17
  %22 = load i32, ptr %12, align 4
  %23 = shl i32 %22, 1
  store i32 %23, ptr %12, align 4
  br label %17, !llvm.loop !6

24:                                               ; preds = %17
  %25 = load ptr, ptr %7, align 8
  %26 = load ptr, ptr %8, align 8
  %27 = load ptr, ptr %9, align 8
  %28 = load i32, ptr %10, align 4
  %29 = load i32, ptr %12, align 4
  %30 = call i32 @vec_reserve_(ptr noundef %25, ptr noundef %26, ptr noundef %27, i32 noundef %28, i32 noundef %29)
  store i32 %30, ptr %6, align 4
  br label %31

31:                                               ; preds = %24, %15
  %32 = load i32, ptr %6, align 4
  ret i32 %32
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @vec_compact_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3) #0 {
  %5 = alloca i32, align 4
  %6 = alloca ptr, align 8
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca i32, align 4
  %10 = alloca ptr, align 8
  %11 = alloca i32, align 4
  store ptr %0, ptr %6, align 8
  store ptr %1, ptr %7, align 8
  store ptr %2, ptr %8, align 8
  store i32 %3, ptr %9, align 4
  %12 = load ptr, ptr %7, align 8
  %13 = load i32, ptr %12, align 4
  %14 = icmp eq i32 %13, 0
  br i1 %14, label %15, label %20

15:                                               ; preds = %4
  %16 = load ptr, ptr %6, align 8
  %17 = load ptr, ptr %16, align 8
  call void @free(ptr noundef %17) #5
  %18 = load ptr, ptr %6, align 8
  store ptr null, ptr %18, align 8
  %19 = load ptr, ptr %8, align 8
  store i32 0, ptr %19, align 4
  store i32 0, ptr %5, align 4
  br label %39

20:                                               ; preds = %4
  %21 = load ptr, ptr %7, align 8
  %22 = load i32, ptr %21, align 4
  store i32 %22, ptr %11, align 4
  %23 = load ptr, ptr %6, align 8
  %24 = load ptr, ptr %23, align 8
  %25 = load i32, ptr %11, align 4
  %26 = load i32, ptr %9, align 4
  %27 = mul nsw i32 %25, %26
  %28 = sext i32 %27 to i64
  %29 = call ptr @realloc(ptr noundef %24, i64 noundef %28) #4
  store ptr %29, ptr %10, align 8
  %30 = load ptr, ptr %10, align 8
  %31 = icmp eq ptr %30, null
  br i1 %31, label %32, label %33

32:                                               ; preds = %20
  store i32 -1, ptr %5, align 4
  br label %39

33:                                               ; preds = %20
  %34 = load i32, ptr %11, align 4
  %35 = load ptr, ptr %8, align 8
  store i32 %34, ptr %35, align 4
  %36 = load ptr, ptr %10, align 8
  %37 = load ptr, ptr %6, align 8
  store ptr %36, ptr %37, align 8
  br label %38

38:                                               ; preds = %33
  store i32 0, ptr %5, align 4
  br label %39

39:                                               ; preds = %38, %32, %15
  %40 = load i32, ptr %5, align 4
  ret i32 %40
}

; Function Attrs: nounwind
declare void @free(ptr noundef) #2

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @vec_insert_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4) #0 {
  %6 = alloca i32, align 4
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  %13 = load ptr, ptr %7, align 8
  %14 = load ptr, ptr %8, align 8
  %15 = load ptr, ptr %9, align 8
  %16 = load i32, ptr %10, align 4
  %17 = call i32 @vec_expand_(ptr noundef %13, ptr noundef %14, ptr noundef %15, i32 noundef %16)
  store i32 %17, ptr %12, align 4
  %18 = load i32, ptr %12, align 4
  %19 = icmp ne i32 %18, 0
  br i1 %19, label %20, label %22

20:                                               ; preds = %5
  %21 = load i32, ptr %12, align 4
  store i32 %21, ptr %6, align 4
  br label %45

22:                                               ; preds = %5
  %23 = load ptr, ptr %7, align 8
  %24 = load ptr, ptr %23, align 8
  %25 = load i32, ptr %11, align 4
  %26 = add nsw i32 %25, 1
  %27 = load i32, ptr %10, align 4
  %28 = mul nsw i32 %26, %27
  %29 = sext i32 %28 to i64
  %30 = getelementptr inbounds i8, ptr %24, i64 %29
  %31 = load ptr, ptr %7, align 8
  %32 = load ptr, ptr %31, align 8
  %33 = load i32, ptr %11, align 4
  %34 = load i32, ptr %10, align 4
  %35 = mul nsw i32 %33, %34
  %36 = sext i32 %35 to i64
  %37 = getelementptr inbounds i8, ptr %32, i64 %36
  %38 = load ptr, ptr %8, align 8
  %39 = load i32, ptr %38, align 4
  %40 = load i32, ptr %11, align 4
  %41 = sub nsw i32 %39, %40
  %42 = load i32, ptr %10, align 4
  %43 = mul nsw i32 %41, %42
  %44 = sext i32 %43 to i64
  call void @llvm.memmove.p0.p0.i64(ptr align 1 %30, ptr align 1 %37, i64 %44, i1 false)
  store i32 0, ptr %6, align 4
  br label %45

45:                                               ; preds = %22, %20
  %46 = load i32, ptr %6, align 4
  ret i32 %46
}

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memmove.p0.p0.i64(ptr writeonly captures(none), ptr readonly captures(none), i64, i1 immarg) #3

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @vec_splice_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  store i32 %5, ptr %12, align 4
  %13 = load ptr, ptr %9, align 8
  %14 = load ptr, ptr %7, align 8
  %15 = load ptr, ptr %14, align 8
  %16 = load i32, ptr %11, align 4
  %17 = load i32, ptr %10, align 4
  %18 = mul nsw i32 %16, %17
  %19 = sext i32 %18 to i64
  %20 = getelementptr inbounds i8, ptr %15, i64 %19
  %21 = load ptr, ptr %7, align 8
  %22 = load ptr, ptr %21, align 8
  %23 = load i32, ptr %11, align 4
  %24 = load i32, ptr %12, align 4
  %25 = add nsw i32 %23, %24
  %26 = load i32, ptr %10, align 4
  %27 = mul nsw i32 %25, %26
  %28 = sext i32 %27 to i64
  %29 = getelementptr inbounds i8, ptr %22, i64 %28
  %30 = load ptr, ptr %8, align 8
  %31 = load i32, ptr %30, align 4
  %32 = load i32, ptr %11, align 4
  %33 = sub nsw i32 %31, %32
  %34 = load i32, ptr %12, align 4
  %35 = sub nsw i32 %33, %34
  %36 = load i32, ptr %10, align 4
  %37 = mul nsw i32 %35, %36
  %38 = sext i32 %37 to i64
  call void @llvm.memmove.p0.p0.i64(ptr align 1 %20, ptr align 1 %29, i64 %38, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @vec_swapsplice_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  store i32 %5, ptr %12, align 4
  %13 = load ptr, ptr %9, align 8
  %14 = load ptr, ptr %7, align 8
  %15 = load ptr, ptr %14, align 8
  %16 = load i32, ptr %11, align 4
  %17 = load i32, ptr %10, align 4
  %18 = mul nsw i32 %16, %17
  %19 = sext i32 %18 to i64
  %20 = getelementptr inbounds i8, ptr %15, i64 %19
  %21 = load ptr, ptr %7, align 8
  %22 = load ptr, ptr %21, align 8
  %23 = load ptr, ptr %8, align 8
  %24 = load i32, ptr %23, align 4
  %25 = load i32, ptr %12, align 4
  %26 = sub nsw i32 %24, %25
  %27 = load i32, ptr %10, align 4
  %28 = mul nsw i32 %26, %27
  %29 = sext i32 %28 to i64
  %30 = getelementptr inbounds i8, ptr %22, i64 %29
  %31 = load i32, ptr %12, align 4
  %32 = load i32, ptr %10, align 4
  %33 = mul nsw i32 %31, %32
  %34 = sext i32 %33 to i64
  call void @llvm.memmove.p0.p0.i64(ptr align 1 %20, ptr align 1 %30, i64 %34, i1 false)
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @vec_swap_(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4, i32 noundef %5) #0 {
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca ptr, align 8
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca ptr, align 8
  %14 = alloca ptr, align 8
  %15 = alloca i8, align 1
  %16 = alloca i32, align 4
  store ptr %0, ptr %7, align 8
  store ptr %1, ptr %8, align 8
  store ptr %2, ptr %9, align 8
  store i32 %3, ptr %10, align 4
  store i32 %4, ptr %11, align 4
  store i32 %5, ptr %12, align 4
  %17 = load ptr, ptr %8, align 8
  %18 = load ptr, ptr %9, align 8
  %19 = load i32, ptr %11, align 4
  %20 = load i32, ptr %12, align 4
  %21 = icmp eq i32 %19, %20
  br i1 %21, label %22, label %23

22:                                               ; preds = %6
  br label %55

23:                                               ; preds = %6
  %24 = load ptr, ptr %7, align 8
  %25 = load ptr, ptr %24, align 8
  %26 = load i32, ptr %11, align 4
  %27 = load i32, ptr %10, align 4
  %28 = mul nsw i32 %26, %27
  %29 = sext i32 %28 to i64
  %30 = getelementptr inbounds i8, ptr %25, i64 %29
  store ptr %30, ptr %13, align 8
  %31 = load ptr, ptr %7, align 8
  %32 = load ptr, ptr %31, align 8
  %33 = load i32, ptr %12, align 4
  %34 = load i32, ptr %10, align 4
  %35 = mul nsw i32 %33, %34
  %36 = sext i32 %35 to i64
  %37 = getelementptr inbounds i8, ptr %32, i64 %36
  store ptr %37, ptr %14, align 8
  %38 = load i32, ptr %10, align 4
  store i32 %38, ptr %16, align 4
  br label %39

39:                                               ; preds = %43, %23
  %40 = load i32, ptr %16, align 4
  %41 = add nsw i32 %40, -1
  store i32 %41, ptr %16, align 4
  %42 = icmp ne i32 %40, 0
  br i1 %42, label %43, label %55

43:                                               ; preds = %39
  %44 = load ptr, ptr %13, align 8
  %45 = load i8, ptr %44, align 1
  store i8 %45, ptr %15, align 1
  %46 = load ptr, ptr %14, align 8
  %47 = load i8, ptr %46, align 1
  %48 = load ptr, ptr %13, align 8
  store i8 %47, ptr %48, align 1
  %49 = load i8, ptr %15, align 1
  %50 = load ptr, ptr %14, align 8
  store i8 %49, ptr %50, align 1
  %51 = load ptr, ptr %13, align 8
  %52 = getelementptr inbounds nuw i8, ptr %51, i32 1
  store ptr %52, ptr %13, align 8
  %53 = load ptr, ptr %14, align 8
  %54 = getelementptr inbounds nuw i8, ptr %53, i32 1
  store ptr %54, ptr %14, align 8
  br label %39, !llvm.loop !8

55:                                               ; preds = %22, %39
  ret void
}

attributes #0 = { noinline nounwind optnone sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nounwind allocsize(1) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nounwind allocsize(1) }
attributes #5 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 22.1.6"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
