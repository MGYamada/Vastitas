target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare void @vastitas_initialize_v1()
declare i32 @vastitas_exit_status_v1(ptr)
declare void @vastitas_retain_v1(ptr)
declare void @vastitas_release_v1(ptr)
declare ptr @vastitas_int_decimal_v1(ptr)
declare ptr @vastitas_int_mul_v1(ptr, ptr)
declare ptr @vastitas_int_div_v1(ptr, ptr)
; boxed () -> Int
@c0_0 = private constant [2 x i8] c"3\00"
@c0_9 = private constant [2 x i8] c"7\00"
define internal ptr @vq_f0() {
entry:
  %v0 = call ptr @vastitas_int_decimal_v1(ptr @c0_0)
  %v1 = call ptr @vastitas_int_mul_v1(ptr %v0, ptr %v0)
  %v2 = call ptr @vastitas_int_mul_v1(ptr %v1, ptr %v1)
  %v3 = call ptr @vastitas_int_mul_v1(ptr %v2, ptr %v2)
  %v4 = call ptr @vastitas_int_mul_v1(ptr %v3, ptr %v3)
  %v5 = call ptr @vastitas_int_mul_v1(ptr %v4, ptr %v4)
  %v6 = call ptr @vastitas_int_mul_v1(ptr %v5, ptr %v5)
  %v7 = call ptr @vastitas_int_mul_v1(ptr %v6, ptr %v6)
  %v8 = call ptr @vastitas_int_mul_v1(ptr %v7, ptr %v7)
  %v9 = call ptr @vastitas_int_decimal_v1(ptr @c0_9)
  %v10 = call ptr @vastitas_int_div_v1(ptr %v8, ptr %v9)
  call void @vastitas_release_v1(ptr %v9)
  call void @vastitas_release_v1(ptr %v8)
  call void @vastitas_release_v1(ptr %v7)
  call void @vastitas_release_v1(ptr %v6)
  call void @vastitas_release_v1(ptr %v5)
  call void @vastitas_release_v1(ptr %v4)
  call void @vastitas_release_v1(ptr %v3)
  call void @vastitas_release_v1(ptr %v2)
  call void @vastitas_release_v1(ptr %v1)
  call void @vastitas_release_v1(ptr %v0)
  ret ptr %v10
}
define i32 @main() {
entry:
  call void @vastitas_initialize_v1()
  %result = call ptr @vq_f0()
  %status = call i32 @vastitas_exit_status_v1(ptr %result)
  ret i32 %status
}
