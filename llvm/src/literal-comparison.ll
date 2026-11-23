target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

define internal i1 @f0 ( i1 %v0_0 ) {
b0:
  %v0_1 = or i1 0 , 1
  %v0_2 = and i1 %v0_0 , %v0_1
  ret i1 %v0_2
}

define internal i32 @f1 ( ) {
b0:
  %v0_0 = or i1 0 , 1
  %v0_1 = call i1 @f0 ( i1 %v0_0 )
  br i1 %v0_1 , label %b1 , label %b2
b1:
  %v1_0 = add i32 0 , 42
  br label %b3
b2:
  %v2_0 = add i32 0 , 7
  br label %b3
b3:
  %v3_0 = phi i32 [ %v1_0 , %b1 ] , [ %v2_0 , %b2 ]
  ret i32 %v3_0
}

define internal i1 @f2 ( i1 %v0_0 ) {
b0:
  %v0_1 = or i1 0 , 0
  %v0_2 = and i1 %v0_0 , %v0_1
  ret i1 %v0_2
}

define i32 @main ( ) {
start:
  %result = call i32 @f1 ( )
  ret i32 %result
}
