target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare void @vastitas_initialize_v1()
declare i32 @vastitas_exit_status_v1(ptr)
declare void @vastitas_retain_v1(ptr)
declare void @vastitas_release_v1(ptr)
declare ptr @vastitas_int_decimal_v1(ptr)
declare i32 @vastitas_int_lt_v1(ptr, ptr)
declare i32 @vastitas_int_gt_v1(ptr, ptr)
declare ptr @vastitas_int_add_v1(ptr, ptr)
; flow -> Bool
define internal i32 @vq_f0(i32 %b0v0, i32 %b0v1) {
; block (Bool, Bool)
b0:
  %cmp0_2 = icmp eq i32 %b0v0, %b0v1
  %b0v2 = zext i1 %cmp0_2 to i32
  ret i32 %b0v2
}
; flow -> Int
@c1_2_0 = private constant [2 x i8] c"0\00"
define internal ptr @vq_f1(i32 %b0v0, i32 %b0v1, ptr %b0v2) {
; block (Bool, Bool, Int)
b0:
  %b0v3 = call i32 @vq_f0(i32 %b0v0, i32 %b0v1)
  %cond0 = icmp ne i32 %b0v3, 0
  br i1 %cond0, label %e0_1, label %e0_2
e0_1:
  call void @vastitas_retain_v1(ptr %b0v2)
  br label %b1
e0_2:
  br label %b2
; block (Int)
b1:
  %b1v0 = phi ptr [ %b0v2, %e0_1 ]
  br label %e1_3
e1_3:
  call void @vastitas_retain_v1(ptr %b1v0)
  call void @vastitas_release_v1(ptr %b1v0)
  br label %b3
; block ()
b2:
  %b2v0 = call ptr @vastitas_int_decimal_v1(ptr @c1_2_0)
  br label %e2_3
e2_3:
  call void @vastitas_retain_v1(ptr %b2v0)
  call void @vastitas_release_v1(ptr %b2v0)
  br label %b3
; block (Int)
b3:
  %b3v0 = phi ptr [ %b1v0, %e1_3 ], [ %b2v0, %e2_3 ]
  call void @vastitas_retain_v1(ptr %b3v0)
  call void @vastitas_release_v1(ptr %b3v0)
  ret ptr %b3v0
}
; flow -> Int
@c2_0_0 = private constant [40 x i8] c"340282366920938463463374607431768211457\00"
@c2_0_1 = private constant [2 x i8] c"0\00"
@c2_0_3 = private constant [2 x i8] c"0\00"
@c2_0_5 = private constant [2 x i8] c"1\00"
@c2_0_7 = private constant [2 x i8] c"2\00"
@c2_0_10 = private constant [2 x i8] c"4\00"
@c2_0_12 = private constant [2 x i8] c"8\00"
define internal ptr @vq_f2() {
; block ()
b0:
  %b0v0 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_0)
  %b0v1 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_1)
  %b0v2 = call i32 @vastitas_int_lt_v1(ptr %b0v0, ptr %b0v1)
  %b0v3 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_3)
  %b0v4 = call i32 @vastitas_int_gt_v1(ptr %b0v0, ptr %b0v3)
  %b0v5 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_5)
  %b0v6 = call ptr @vq_f1(i32 %b0v2, i32 %b0v2, ptr %b0v5)
  %b0v7 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_7)
  %b0v8 = call ptr @vq_f1(i32 %b0v2, i32 %b0v4, ptr %b0v7)
  %b0v9 = call ptr @vastitas_int_add_v1(ptr %b0v6, ptr %b0v8)
  %b0v10 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_10)
  %b0v11 = call ptr @vq_f1(i32 %b0v4, i32 %b0v2, ptr %b0v10)
  %b0v12 = call ptr @vastitas_int_decimal_v1(ptr @c2_0_12)
  %b0v13 = call ptr @vq_f1(i32 %b0v4, i32 %b0v4, ptr %b0v12)
  %b0v14 = call ptr @vastitas_int_add_v1(ptr %b0v11, ptr %b0v13)
  %b0v15 = call ptr @vastitas_int_add_v1(ptr %b0v9, ptr %b0v14)
  %b0v16 = call ptr @vastitas_int_add_v1(ptr %b0v0, ptr %b0v15)
  call void @vastitas_retain_v1(ptr %b0v16)
  call void @vastitas_release_v1(ptr %b0v16)
  call void @vastitas_release_v1(ptr %b0v15)
  call void @vastitas_release_v1(ptr %b0v14)
  call void @vastitas_release_v1(ptr %b0v13)
  call void @vastitas_release_v1(ptr %b0v12)
  call void @vastitas_release_v1(ptr %b0v11)
  call void @vastitas_release_v1(ptr %b0v10)
  call void @vastitas_release_v1(ptr %b0v9)
  call void @vastitas_release_v1(ptr %b0v8)
  call void @vastitas_release_v1(ptr %b0v7)
  call void @vastitas_release_v1(ptr %b0v6)
  call void @vastitas_release_v1(ptr %b0v5)
  call void @vastitas_release_v1(ptr %b0v3)
  call void @vastitas_release_v1(ptr %b0v1)
  call void @vastitas_release_v1(ptr %b0v0)
  ret ptr %b0v16
}
; flow -> Bool
define internal i32 @vq_f3(i32 %b0v0, i32 %b0v1) {
; block (Bool, Bool)
b0:
  %cmp0_2 = icmp ne i32 %b0v0, %b0v1
  %b0v2 = zext i1 %cmp0_2 to i32
  ret i32 %b0v2
}
define i32 @main() {
entry:
  call void @vastitas_initialize_v1()
  %result = call ptr @vq_f2()
  %status = call i32 @vastitas_exit_status_v1(ptr %result)
  ret i32 %status
}
