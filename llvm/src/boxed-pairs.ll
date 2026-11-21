target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare void @vastitas_initialize_v1()
declare i32 @vastitas_exit_status_v1(ptr)
declare void @vastitas_retain_v1(ptr)
declare void @vastitas_release_v1(ptr)
declare ptr @vastitas_nat_decimal_v1(ptr)
declare ptr @vastitas_nat_sub_v1(ptr, ptr)
declare ptr @vastitas_nat_pair_v1(ptr, ptr)
declare ptr @vastitas_int_pair_second_v1(ptr)
declare ptr @vastitas_int_pair_first_v1(ptr)
declare ptr @vastitas_int_pair_v1(ptr, ptr)
declare ptr @vastitas_int_decimal_v1(ptr)
declare ptr @vastitas_nat_pair_second_v1(ptr)
declare ptr @vastitas_nat_pair_first_v1(ptr)
declare ptr @vastitas_nat_to_int_v1(ptr)
declare ptr @vastitas_int_add_v1(ptr, ptr)
; boxed (Nat) -> Pair<Nat>
@c0_1 = private constant [2 x i8] c"1\00"
define internal ptr @vq_f0(ptr %v0) {
entry:
  %v1 = call ptr @vastitas_nat_decimal_v1(ptr @c0_1)
  %v2 = call ptr @vastitas_nat_sub_v1(ptr %v0, ptr %v1)
  %v3 = call ptr @vastitas_nat_pair_v1(ptr %v2, ptr %v0)
  call void @vastitas_release_v1(ptr %v2)
  call void @vastitas_release_v1(ptr %v1)
  ret ptr %v3
}
; boxed (Pair<Int>) -> Pair<Int>
define internal ptr @vq_f1(ptr %v0) {
entry:
  %v1 = call ptr @vastitas_int_pair_second_v1(ptr %v0)
  %v2 = call ptr @vastitas_int_pair_first_v1(ptr %v0)
  %v3 = call ptr @vastitas_int_pair_v1(ptr %v1, ptr %v2)
  call void @vastitas_release_v1(ptr %v2)
  call void @vastitas_release_v1(ptr %v1)
  ret ptr %v3
}
; boxed (Int) -> Pair<Int>
@c2_1 = private constant [2 x i8] c"0\00"
define internal ptr @vq_f2(ptr %v0) {
entry:
  %v1 = call ptr @vastitas_int_decimal_v1(ptr @c2_1)
  %v2 = call ptr @vastitas_int_pair_v1(ptr %v0, ptr %v1)
  call void @vastitas_release_v1(ptr %v1)
  ret ptr %v2
}
; boxed () -> Int
@c3_0 = private constant [40 x i8] c"340282366920938463463374607431768211457\00"
@c3_2 = private constant [41 x i8] c"-340282366920938463463374607431768211457\00"
@c3_14 = private constant [3 x i8] c"42\00"
define internal ptr @vq_f3() {
entry:
  %v0 = call ptr @vastitas_nat_decimal_v1(ptr @c3_0)
  %v1 = call ptr @vq_f0(ptr %v0)
  %v2 = call ptr @vastitas_int_decimal_v1(ptr @c3_2)
  %v3 = call ptr @vq_f2(ptr %v2)
  %v4 = call ptr @vq_f1(ptr %v3)
  %v5 = call ptr @vastitas_nat_pair_second_v1(ptr %v1)
  %v6 = call ptr @vastitas_nat_pair_first_v1(ptr %v1)
  %v7 = call ptr @vastitas_nat_sub_v1(ptr %v5, ptr %v6)
  %v8 = call ptr @vastitas_int_pair_second_v1(ptr %v4)
  %v9 = call ptr @vastitas_nat_pair_first_v1(ptr %v1)
  %v10 = call ptr @vastitas_nat_to_int_v1(ptr %v9)
  %v11 = call ptr @vastitas_int_add_v1(ptr %v8, ptr %v10)
  %v12 = call ptr @vastitas_nat_to_int_v1(ptr %v7)
  %v13 = call ptr @vastitas_int_add_v1(ptr %v11, ptr %v12)
  %v14 = call ptr @vastitas_int_decimal_v1(ptr @c3_14)
  %v15 = call ptr @vastitas_int_add_v1(ptr %v13, ptr %v14)
  call void @vastitas_release_v1(ptr %v14)
  call void @vastitas_release_v1(ptr %v13)
  call void @vastitas_release_v1(ptr %v12)
  call void @vastitas_release_v1(ptr %v11)
  call void @vastitas_release_v1(ptr %v10)
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
  ret ptr %v15
}
; boxed (Int) -> Pair<Int>
@c4_1 = private constant [2 x i8] c"0\00"
define internal ptr @vq_f4(ptr %v0) {
entry:
  %v1 = call ptr @vastitas_int_decimal_v1(ptr @c4_1)
  %v2 = call ptr @vastitas_int_pair_v1(ptr %v1, ptr %v0)
  call void @vastitas_release_v1(ptr %v1)
  ret ptr %v2
}
define i32 @main() {
entry:
  call void @vastitas_initialize_v1()
  %result = call ptr @vq_f3()
  %status = call i32 @vastitas_exit_status_v1(ptr %result)
  ret i32 %status
}
