target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare void @vastitas_initialize_v1()
declare i32 @vastitas_exit_status_v1(ptr)
declare void @vastitas_retain_v1(ptr)
declare void @vastitas_release_v1(ptr)
declare ptr @vastitas_int_neg_v1(ptr)
declare ptr @vastitas_int_decimal_v1(ptr)
; boxed (Int) -> Int
define internal ptr @vq_f0(ptr %v0) {
entry:
  %v1 = call ptr @vastitas_int_neg_v1(ptr %v0)
  ret ptr %v1
}
; boxed (Int) -> Int
define internal ptr @vq_f1(ptr %v0) {
entry:
  %v1 = call ptr @vq_f0(ptr %v0)
  ret ptr %v1
}
; boxed () -> Int
@c2_0 = private constant [40 x i8] c"340282366920938463463374607431768211499\00"
define internal ptr @vq_f2() {
entry:
  %v0 = call ptr @vastitas_int_decimal_v1(ptr @c2_0)
  %v1 = call ptr @vq_f1(ptr %v0)
  call void @vastitas_release_v1(ptr %v0)
  ret ptr %v1
}
; boxed (Int) -> Int
define internal ptr @vq_f3(ptr %v0) {
entry:
  call void @vastitas_retain_v1(ptr %v0)
  ret ptr %v0
}
define i32 @main() {
entry:
  call void @vastitas_initialize_v1()
  %result = call ptr @vq_f2()
  %status = call i32 @vastitas_exit_status_v1(ptr %result)
  ret i32 %status
}
