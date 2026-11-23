target triple = "\78\38\36\5F\36\34\2D\75\6E\6B\6E\6F\77\6E\2D\6C\69\6E\75\78\2D\67\6E\75"
target datalayout = "\65\2D\6D\3A\65\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\66\38\30\3A\31\32\38\2D\6E\38\3A\31\36\3A\33\32\3A\36\34\2D\53\31\32\38"

define internal i32 @f0 ( ) {
b0:
  %v0_0 = add i32 0 , 1
  ret i32 %v0_0
}

define internal i32 @t1_0_2 ( i32 %x ) {
start:
  switch i32 %x , label %miss [ i32 0 , label %case0 i32 1 , label %case1 ]
case0:
  ret i32 0
case1:
  ret i32 1
miss:
  ret i32 4294967295
}

define internal i32 @t1_0_4 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 2
  %colOK = icmp ult i32 %y , 2
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 2
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 ]
case0:
  ret i32 0
case1:
  ret i32 1
case2:
  ret i32 1
case3:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @t1_0_5 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 2
  %colOK = icmp ult i32 %y , 2
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 2
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 ]
case0:
  ret i32 0
case1:
  ret i32 1
case2:
  ret i32 1
case3:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f1 ( i32 %v0_0 , i32 %v0_1 ) {
b0:
  %v0_2 = call i32 @t1_0_2 ( i32 %v0_1 )
  %v0_3 = add i32 0 , 1
  %v0_4 = call i32 @t1_0_4 ( i32 %v0_3 , i32 %v0_2 )
  %v0_5 = call i32 @t1_0_5 ( i32 %v0_4 , i32 %v0_0 )
  ret i32 %v0_5
}

define internal i32 @f2 ( i32 %v0_0 ) {
b0:
  %v0_1 = or i1 0 , 0
  %v0_2 = call i32 @f0 ( )
  %v0_3 = call i32 @f1 ( i32 %v0_0 , i32 %v0_2 )
  ret i32 %v0_3
}

define internal i32 @f3 ( ) {
b0:
  %v0_0 = or i1 0 , 0
  %v0_1 = add i32 0 , 1
  %v0_2 = or i1 0 , 0
  %v0_3 = call i32 @f2 ( i32 %v0_1 )
  %v0_4 = add i32 0 , 1
  %v0_5 = icmp eq i32 %v0_3 , %v0_4
  br i1 %v0_5 , label %b1 , label %b2
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

define i32 @main ( ) {
start:
  %result = call i32 @f3 ( )
  ret i32 %result
}
