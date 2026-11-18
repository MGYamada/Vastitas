; Hand-authored ABI fixture. No compiler-acceptance or proof claim.
target triple = "arm64-apple-darwin27.2.0"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"

declare i32 @vq_initialize()
declare ptr @vq_big()
declare ptr @vq_nat_mul(ptr, ptr)
declare i32 @vq_check_big(ptr)
declare i32 @vq_check_integer()
declare i32 @vq_check_indexed()
declare i32 @vq_check_blas()
declare void @vq_release(ptr)

; Monomorphic family targets after selection. Subtraction borrows its operands;
; the Nat-to-Int conversion consumes the owned subtraction result.
declare ptr @vq_nat_sub_five(ptr)
declare ptr @vq_int_sub_five(ptr)
declare ptr @vq_nat_to_int_owned(ptr)
declare i32 @vq_check_family()

declare void @vq_retain(ptr)
declare ptr @vq_int_ediv(ptr, ptr)

; Both mixed signatures use the consuming Nat-to-Int shim. Borrowed inputs
; survive either call and the temporary owned Int is released after ediv.
define ptr @vq_div_nat_int(ptr %n, ptr %i) {
entry:
  call void @vq_retain(ptr %n)
  %converted = call ptr @vq_nat_to_int_owned(ptr %n)
  %q = call ptr @vq_int_ediv(ptr %converted, ptr %i)
  call void @vq_release(ptr %converted)
  ret ptr %q
}

define ptr @vq_div_int_nat(ptr %i, ptr %n) {
entry:
  call void @vq_retain(ptr %n)
  %converted = call ptr @vq_nat_to_int_owned(ptr %n)
  %q = call ptr @vq_int_ediv(ptr %i, ptr %converted)
  call void @vq_release(ptr %converted)
  ret ptr %q
}

define ptr @vq_family_evaluate(i8 %flag, ptr %n, ptr %i) {
entry:
  %is_nat = icmp ne i8 %flag, 0
  br i1 %is_nat, label %nat, label %int
nat:
  %difference = call ptr @vq_nat_sub_five(ptr %n)
  %converted = call ptr @vq_nat_to_int_owned(ptr %difference)
  br label %join
int:
  %signed = call ptr @vq_int_sub_five(ptr %i)
  br label %join
join:
  %result = phi ptr [ %converted, %nat ], [ %signed, %int ]
  ret ptr %result
}

define i32 @main() {
entry:
  %initialized = call i32 @vq_initialize()
  %ready = icmp eq i32 %initialized, 0
  br i1 %ready, label %run, label %failed
run:
  %big = call ptr @vq_big()
  %square = call ptr @vq_nat_mul(ptr %big, ptr %big)
  %big_status = call i32 @vq_check_big(ptr %square)
  call void @vq_release(ptr %square)
  call void @vq_release(ptr %big)
  %integer_status = call i32 @vq_check_integer()
  %indexed_status = call i32 @vq_check_indexed()
  %blas_status = call i32 @vq_check_blas()
  %s1 = or i32 %big_status, %integer_status
  %s2 = or i32 %s1, %indexed_status
  %s3 = or i32 %s2, %blas_status
  %family_status = call i32 @vq_check_family()
  %s4 = or i32 %s3, %family_status
  br label %finish
failed:
  br label %finish
finish:
  %status = phi i32 [ %s4, %run ], [ 1, %failed ]
  ret i32 %status
}
