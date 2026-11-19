target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

define i32 @vq_lookup2(i32 %row, i32 %col) {
entry:
  %r = icmp ult i32 %row, u0x0006
  %c = icmp ult i32 %col, u0x0006
  %ok = and i1 %r, %c
  br i1 %ok, label %lookup, label %miss
lookup:
  %base = mul i32 %row, u0x0006
  %index = add i32 %base, %col
  switch i32 %index, label %miss [
    i32 u0x0000, label %k0000
    i32 u0x0001, label %k0001
    i32 u0x0002, label %k0002
    i32 u0x0003, label %k0003
    i32 u0x0004, label %k0004
    i32 u0x0005, label %k0005
    i32 u0x0006, label %k0006
    i32 u0x0007, label %k0007
    i32 u0x0008, label %k0008
    i32 u0x0009, label %k0009
    i32 u0x000A, label %k000A
    i32 u0x000B, label %k000B
    i32 u0x000C, label %k000C
    i32 u0x000D, label %k000D
    i32 u0x000E, label %k000E
    i32 u0x000F, label %k000F
    i32 u0x0010, label %k0010
    i32 u0x0011, label %k0011
    i32 u0x0012, label %k0012
    i32 u0x0013, label %k0013
    i32 u0x0014, label %k0014
    i32 u0x0015, label %k0015
    i32 u0x0016, label %k0016
    i32 u0x0017, label %k0017
    i32 u0x0018, label %k0018
    i32 u0x0019, label %k0019
    i32 u0x001A, label %k001A
    i32 u0x001B, label %k001B
    i32 u0x001C, label %k001C
    i32 u0x001D, label %k001D
    i32 u0x001E, label %k001E
    i32 u0x001F, label %k001F
    i32 u0x0020, label %k0020
    i32 u0x0021, label %k0021
    i32 u0x0022, label %k0022
    i32 u0x0023, label %k0023
  ]
miss:
  ret i32 -1
k0000:
  ret i32 u0x0000
k0001:
  ret i32 u0x0001
k0002:
  ret i32 u0x0002
k0003:
  ret i32 u0x0003
k0004:
  ret i32 u0x0004
k0005:
  ret i32 u0x0005
k0006:
  ret i32 u0x0001
k0007:
  ret i32 u0x0000
k0008:
  ret i32 u0x0004
k0009:
  ret i32 u0x0005
k000A:
  ret i32 u0x0002
k000B:
  ret i32 u0x0003
k000C:
  ret i32 u0x0002
k000D:
  ret i32 u0x0003
k000E:
  ret i32 u0x0000
k000F:
  ret i32 u0x0001
k0010:
  ret i32 u0x0005
k0011:
  ret i32 u0x0004
k0012:
  ret i32 u0x0003
k0013:
  ret i32 u0x0002
k0014:
  ret i32 u0x0005
k0015:
  ret i32 u0x0004
k0016:
  ret i32 u0x0000
k0017:
  ret i32 u0x0001
k0018:
  ret i32 u0x0004
k0019:
  ret i32 u0x0005
k001A:
  ret i32 u0x0001
k001B:
  ret i32 u0x0000
k001C:
  ret i32 u0x0003
k001D:
  ret i32 u0x0002
k001E:
  ret i32 u0x0005
k001F:
  ret i32 u0x0004
k0020:
  ret i32 u0x0003
k0021:
  ret i32 u0x0002
k0022:
  ret i32 u0x0001
k0023:
  ret i32 u0x0000
}
