target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare void @vastitas_initialize_v1()
declare i32 @vastitas_exit_status_v1(ptr)
declare void @vastitas_retain_v1(ptr)
declare void @vastitas_release_v1(ptr)
declare i32 @vastitas_int_lt_v1(ptr, ptr)
declare ptr @vastitas_int_decimal_v1(ptr)
; flow -> Bool
define internal i32 @vq_f0(ptr %b0v0, ptr %b0v1) {
; block (Int, Int)
b0:
  %b0v2 = call i32 @vastitas_int_lt_v1(ptr %b0v0, ptr %b0v1)
  ret i32 %b0v2
}
; flow -> Int
@c1_0_0 = private constant [41 x i8] c"-340282366920938463463374607431768211457\00"
@c1_0_1 = private constant [3 x i8] c"-1\00"
@c1_1_0 = private constant [3 x i8] c"42\00"
@c1_2_0 = private constant [2 x i8] c"7\00"
define internal ptr @vq_f1() {
; block ()
b0:
  %b0v0 = call ptr @vastitas_int_decimal_v1(ptr @c1_0_0)
  %b0v1 = call ptr @vastitas_int_decimal_v1(ptr @c1_0_1)
  %b0v2 = call i32 @vq_f0(ptr %b0v0, ptr %b0v1)
  %cond0 = icmp ne i32 %b0v2, 0
  br i1 %cond0, label %e0_1, label %e0_2
e0_1:
  call void @vastitas_release_v1(ptr %b0v1)
  call void @vastitas_release_v1(ptr %b0v0)
  br label %b1
e0_2:
  call void @vastitas_release_v1(ptr %b0v1)
  call void @vastitas_release_v1(ptr %b0v0)
  br label %b2
; block ()
b1:
  %b1v0 = call ptr @vastitas_int_decimal_v1(ptr @c1_1_0)
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
; flow -> Bool
define internal i32 @vq_f2(ptr %b0v0, ptr %b0v1) {
; block (Int, Int)
b0:
  %b0v2 = call i32 @vastitas_int_lt_v1(ptr %b0v1, ptr %b0v0)
  ret i32 %b0v2
}
define i32 @main() {
entry:
  call void @vastitas_initialize_v1()
  %result = call ptr @vq_f1()
  %status = call i32 @vastitas_exit_status_v1(ptr %result)
  ret i32 %status
}
