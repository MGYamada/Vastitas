target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

declare ptr @vq_storage_new(i64)
declare void @vstorage_delete(ptr)
declare i32 @vq_storage_allocate(ptr, i64, i64, i64)
declare i32 @vq_storage_drop(ptr, i64)
declare i32 @vq_storage_store(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)
declare i32 @vq_storage_expect(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)
declare i32 @vq_storage_copy(ptr, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)

define i32 @main() {
entry:
  %arena = call ptr @vq_storage_new(i64 9223372036854775807)
  %created = icmp ne ptr %arena, null
  br i1 %created, label %next0, label %unavailable
next0:
  %status0 = call i32 @vq_storage_allocate(ptr %arena, i64 0, i64 2, i64 2)
  %ok0 = icmp eq i32 %status0, 0
  br i1 %ok0, label %next1, label %failed
next1:
  %status1 = call i32 @vq_storage_allocate(ptr %arena, i64 1, i64 2, i64 2)
  %ok1 = icmp eq i32 %status1, 0
  br i1 %ok1, label %next2, label %failed
next2:
  %status2 = call i32 @vq_storage_store(ptr %arena, i64 0, i64 0, i64 2, i64 1, i64 2, i64 0, i64 0, i64 0, i64 2, i64 2147483648, i64 0)
  %ok2 = icmp eq i32 %status2, 0
  br i1 %ok2, label %next3, label %failed
next3:
  %status3 = call i32 @vq_storage_store(ptr %arena, i64 0, i64 0, i64 2, i64 1, i64 2, i64 0, i64 1, i64 0, i64 2, i64 2139095106, i64 0)
  %ok3 = icmp eq i32 %status3, 0
  br i1 %ok3, label %next4, label %failed
next4:
  %status4 = call i32 @vq_storage_copy(ptr %arena, i64 0, i64 0, i64 2, i64 1, i64 2, i64 0, i64 1, i64 0, i64 2, i64 1, i64 2, i64 0)
  %ok4 = icmp eq i32 %status4, 0
  br i1 %ok4, label %next5, label %failed
next5:
  %status5 = call i32 @vq_storage_expect(ptr %arena, i64 1, i64 0, i64 2, i64 1, i64 2, i64 0, i64 0, i64 0, i64 2, i64 2147483648, i64 0)
  %ok5 = icmp eq i32 %status5, 0
  br i1 %ok5, label %next6, label %failed
next6:
  %status6 = call i32 @vq_storage_expect(ptr %arena, i64 1, i64 0, i64 2, i64 1, i64 2, i64 0, i64 1, i64 0, i64 2, i64 2139095106, i64 0)
  %ok6 = icmp eq i32 %status6, 0
  br i1 %ok6, label %next7, label %failed
next7:
  %status7 = call i32 @vq_storage_drop(ptr %arena, i64 1)
  %ok7 = icmp eq i32 %status7, 0
  br i1 %ok7, label %next8, label %failed
next8:
  %status8 = call i32 @vq_storage_drop(ptr %arena, i64 0)
  %ok8 = icmp eq i32 %status8, 0
  br i1 %ok8, label %next9, label %failed
next9:
  call void @vstorage_delete(ptr %arena)
  ret i32 0
failed:
  call void @vstorage_delete(ptr %arena)
  ret i32 1
unavailable:
  ret i32 1
}
