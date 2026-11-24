target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

; boxed (Int, Int) -> Bool
@c2 = private constant [4 x i8] c"256\00"
declare ptr @vastitas_int_decimal_v1(ptr)
declare ptr @vastitas_int_sub_v1(ptr, ptr)
declare i32 @vastitas_int_le_v1(ptr, ptr)
declare void @vastitas_release_v1(ptr)
define i32 @vq_exact(ptr %v0, ptr %v1) {
entry:
  %v2 = call ptr @vastitas_int_decimal_v1(ptr @c2)
  %v3 = call ptr @vastitas_int_sub_v1(ptr %v0, ptr %v2)
  %v4 = call i32 @vastitas_int_le_v1(ptr %v3, ptr %v1)
  call void @vastitas_release_v1(ptr %v3)
  call void @vastitas_release_v1(ptr %v2)
  ret i32 %v4
}
