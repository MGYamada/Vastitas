target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare ptr @vq_storage_new(i64)
declare void @vstorage_delete(ptr)
declare i32 @vq_storage_allocate(ptr, i64, i64, i64)
declare i32 @vq_storage_drop(ptr, i64)
declare i32 @vq_storage_fill(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64)
declare i32 @vq_storage_expect(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)
declare i32 @vq_storage_gemm(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)

define i32 @main() {
entry:
  %arena = call ptr @vq_storage_new(i64 9223372036854775807)
  %created = icmp ne ptr %arena, null
  br i1 %created, label %next0, label %unavailable
next0:
  %status0 = call i32 @vq_storage_allocate(ptr %arena, i64 0, i64 0, i64 1)
  %ok0 = icmp eq i32 %status0, 0
  br i1 %ok0, label %next1, label %failed
next1:
  %status1 = call i32 @vq_storage_allocate(ptr %arena, i64 1, i64 0, i64 1)
  %ok1 = icmp eq i32 %status1, 0
  br i1 %ok1, label %next2, label %failed
next2:
  %status2 = call i32 @vq_storage_allocate(ptr %arena, i64 2, i64 0, i64 1)
  %ok2 = icmp eq i32 %status2, 0
  br i1 %ok2, label %next3, label %failed
next3:
  %status3 = call i32 @vq_storage_allocate(ptr %arena, i64 3, i64 0, i64 1)
  %ok3 = icmp eq i32 %status3, 0
  br i1 %ok3, label %next4, label %failed
next4:
  %status4 = call i32 @vq_storage_fill(ptr %arena, i64 0, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 4611686018427387904, i64 0)
  %ok4 = icmp eq i32 %status4, 0
  br i1 %ok4, label %next5, label %failed
next5:
  %status5 = call i32 @vq_storage_fill(ptr %arena, i64 1, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 4613937818241073152, i64 0)
  %ok5 = icmp eq i32 %status5, 0
  br i1 %ok5, label %next6, label %failed
next6:
  %status6 = call i32 @vq_storage_fill(ptr %arena, i64 3, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 4616189618054758400, i64 0)
  %ok6 = icmp eq i32 %status6, 0
  br i1 %ok6, label %next7, label %failed
next7:
  %status7 = call i32 @vq_storage_gemm(ptr %arena, i64 0, i64 0, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 1, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 2, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 1, i64 0, i64 4602678819172646912, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0)
  %ok7 = icmp eq i32 %status7, 0
  br i1 %ok7, label %next8, label %failed
next8:
  %status8 = call i32 @vq_storage_expect(ptr %arena, i64 2, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 0, i64 0, i64 4613937818241073152, i64 0)
  %ok8 = icmp eq i32 %status8, 0
  br i1 %ok8, label %next9, label %failed
next9:
  %status9 = call i32 @vq_storage_gemm(ptr %arena, i64 0, i64 0, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 1, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 2, i64 0, i64 1, i64 1, i64 1, i64 0, i64 1, i64 2, i64 0, i64 0, i64 0, i64 3, i64 0, i64 1, i64 0, i64 4611686018427387904, i64 0, i64 0, i64 0)
  %ok9 = icmp eq i32 %status9, 0
  br i1 %ok9, label %next10, label %failed
next10:
  %status10 = call i32 @vq_storage_expect(ptr %arena, i64 2, i64 0, i64 1, i64 1, i64 1, i64 0, i64 0, i64 0, i64 0, i64 4629137466983448576, i64 0)
  %ok10 = icmp eq i32 %status10, 0
  br i1 %ok10, label %next11, label %failed
next11:
  %status11 = call i32 @vq_storage_drop(ptr %arena, i64 3)
  %ok11 = icmp eq i32 %status11, 0
  br i1 %ok11, label %next12, label %failed
next12:
  %status12 = call i32 @vq_storage_drop(ptr %arena, i64 2)
  %ok12 = icmp eq i32 %status12, 0
  br i1 %ok12, label %next13, label %failed
next13:
  %status13 = call i32 @vq_storage_drop(ptr %arena, i64 1)
  %ok13 = icmp eq i32 %status13, 0
  br i1 %ok13, label %next14, label %failed
next14:
  %status14 = call i32 @vq_storage_drop(ptr %arena, i64 0)
  %ok14 = icmp eq i32 %status14, 0
  br i1 %ok14, label %next15, label %failed
next15:
  call void @vstorage_delete(ptr %arena)
  ret i32 0
failed:
  call void @vstorage_delete(ptr %arena)
  ret i32 1
unavailable:
  ret i32 1
}
