target triple = "\78\38\36\5F\36\34\2D\75\6E\6B\6E\6F\77\6E\2D\6C\69\6E\75\78\2D\67\6E\75"
target datalayout = "\65\2D\6D\3A\65\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\66\38\30\3A\31\32\38\2D\6E\38\3A\31\36\3A\33\32\3A\36\34\2D\53\31\32\38"

define internal i32 @t0_0_3 ( i32 %x , i32 %y , i32 %axis2 ) {
start:
  %rowOK = icmp ult i32 %x , 2
  %colOK = icmp ult i32 %y , 3
  %both = and i1 %rowOK , %colOK
  %ok2 = icmp ult i32 %axis2 , 2
  %inside2 = and i1 %both , %ok2
  br i1 %inside2 , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 3
  %index = add i32 %base , %y
  %base2 = mul i32 %index , 2
  %index2 = add i32 %base2 , %axis2
  switch i32 %index2 , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 i32 4 , label %case4 i32 5 , label %case5 i32 6 , label %case6 i32 7 , label %case7 i32 8 , label %case8 i32 9 , label %case9 i32 10 , label %case10 i32 11 , label %case11 ]
case0:
  ret i32 0
case1:
  ret i32 1
case2:
  ret i32 2
case3:
  ret i32 3
case4:
  ret i32 4
case5:
  ret i32 5
case6:
  ret i32 6
case7:
  ret i32 7
case8:
  ret i32 8
case9:
  ret i32 9
case10:
  ret i32 10
case11:
  ret i32 11
miss:
  ret i32 4294967295
}

define internal i32 @f0 ( i32 %v0_0 , i32 %v0_1 , i32 %v0_2 ) {
b0:
  %v0_3 = call i32 @t0_0_3 ( i32 %v0_0 , i32 %v0_1 , i32 %v0_2 )
  ret i32 %v0_3
}

define internal i1 @f1 ( i1 %v0_0 , i1 %v0_1 ) {
b0:
  %v0_2 = icmp eq i1 %v0_0 , 0
  %v0_3 = or i1 %v0_2 , %v0_1
  ret i1 %v0_3
}

define internal i32 @t2_0_4 ( ) {
start:
  switch i32 0 , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 9
miss:
  ret i32 4294967295
}

define internal i32 @f2 ( ) {
b0:
  %v0_0 = add i32 0 , 1
  %v0_1 = add i32 0 , 1
  %v0_2 = add i32 0 , 1
  %v0_3 = call i32 @f0 ( i32 %v0_0 , i32 %v0_1 , i32 %v0_2 )
  %v0_4 = call i32 @t2_0_4 ( )
  %v0_5 = icmp eq i32 %v0_3 , %v0_4
  %v0_6 = or i1 0 , 1
  %v0_7 = call i1 @f1 ( i1 %v0_6 , i1 %v0_5 )
  %v0_8 = or i1 0 , 1
  %v0_9 = or i1 0 , 0
  %v0_10 = call i1 @f1 ( i1 %v0_8 , i1 %v0_9 )
  %v0_11 = icmp eq i1 %v0_10 , 0
  %v0_12 = and i1 %v0_7 , %v0_11
  br i1 %v0_12 , label %b1 , label %b2
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

define internal i1 @f3 ( i1 %v0_0 , i1 %v0_1 ) {
b0:
  %v0_2 = icmp eq i1 %v0_0 , 0
  %v0_3 = icmp eq i1 %v0_1 , 0
  %v0_4 = and i1 %v0_2 , %v0_3
  ret i1 %v0_4
}

define i32 @main ( ) {
start:
  %result = call i32 @f2 ( )
  ret i32 %result
}
