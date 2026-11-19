target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

; rows 0003
define i32 @vq_lookup(i32 %tag) {
entry:
  switch i32 %tag, label %miss [
    i32 u0x0000, label %k0000
    i32 u0x0001, label %k0001
    i32 u0x0002, label %k0002
  ]
miss:
  ret i32 -1
k0000:
  ret i32 u0x0001
k0001:
  ret i32 u0x0000
k0002:
  ret i32 u0x0001
}

define i32 @vq_forward(i32 %tag) {
entry:
  %result = call i32 @vq_lookup(i32 %tag)
  ret i32 %result
}
