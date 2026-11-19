target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

define internal i32 @t0_0_2 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 6
  %colOK = icmp ult i32 %y , 6
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 6
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 i32 4 , label %case4 i32 5 , label %case5 i32 6 , label %case6 i32 7 , label %case7 i32 8 , label %case8 i32 9 , label %case9 i32 10 , label %case10 i32 11 , label %case11 i32 12 , label %case12 i32 13 , label %case13 i32 14 , label %case14 i32 15 , label %case15 i32 16 , label %case16 i32 17 , label %case17 i32 18 , label %case18 i32 19 , label %case19 i32 20 , label %case20 i32 21 , label %case21 i32 22 , label %case22 i32 23 , label %case23 i32 24 , label %case24 i32 25 , label %case25 i32 26 , label %case26 i32 27 , label %case27 i32 28 , label %case28 i32 29 , label %case29 i32 30 , label %case30 i32 31 , label %case31 i32 32 , label %case32 i32 33 , label %case33 i32 34 , label %case34 i32 35 , label %case35 ]
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
  ret i32 1
case7:
  ret i32 0
case8:
  ret i32 3
case9:
  ret i32 2
case10:
  ret i32 5
case11:
  ret i32 4
case12:
  ret i32 2
case13:
  ret i32 4
case14:
  ret i32 0
case15:
  ret i32 5
case16:
  ret i32 1
case17:
  ret i32 3
case18:
  ret i32 3
case19:
  ret i32 5
case20:
  ret i32 1
case21:
  ret i32 4
case22:
  ret i32 0
case23:
  ret i32 2
case24:
  ret i32 4
case25:
  ret i32 2
case26:
  ret i32 5
case27:
  ret i32 0
case28:
  ret i32 3
case29:
  ret i32 1
case30:
  ret i32 5
case31:
  ret i32 3
case32:
  ret i32 4
case33:
  ret i32 1
case34:
  ret i32 2
case35:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f0 ( i32 %v0_0 , i32 %v0_1 ) {
b0:
  %v0_2 = call i32 @t0_0_2 ( i32 %v0_0 , i32 %v0_1 )
  ret i32 %v0_2
}

define internal i32 @t1_0_2 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 6
  %colOK = icmp ult i32 %y , 6
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 6
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 i32 4 , label %case4 i32 5 , label %case5 i32 6 , label %case6 i32 7 , label %case7 i32 8 , label %case8 i32 9 , label %case9 i32 10 , label %case10 i32 11 , label %case11 i32 12 , label %case12 i32 13 , label %case13 i32 14 , label %case14 i32 15 , label %case15 i32 16 , label %case16 i32 17 , label %case17 i32 18 , label %case18 i32 19 , label %case19 i32 20 , label %case20 i32 21 , label %case21 i32 22 , label %case22 i32 23 , label %case23 i32 24 , label %case24 i32 25 , label %case25 i32 26 , label %case26 i32 27 , label %case27 i32 28 , label %case28 i32 29 , label %case29 i32 30 , label %case30 i32 31 , label %case31 i32 32 , label %case32 i32 33 , label %case33 i32 34 , label %case34 i32 35 , label %case35 ]
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
  ret i32 1
case7:
  ret i32 0
case8:
  ret i32 4
case9:
  ret i32 5
case10:
  ret i32 2
case11:
  ret i32 3
case12:
  ret i32 2
case13:
  ret i32 3
case14:
  ret i32 0
case15:
  ret i32 1
case16:
  ret i32 5
case17:
  ret i32 4
case18:
  ret i32 3
case19:
  ret i32 2
case20:
  ret i32 5
case21:
  ret i32 4
case22:
  ret i32 0
case23:
  ret i32 1
case24:
  ret i32 4
case25:
  ret i32 5
case26:
  ret i32 1
case27:
  ret i32 0
case28:
  ret i32 3
case29:
  ret i32 2
case30:
  ret i32 5
case31:
  ret i32 4
case32:
  ret i32 3
case33:
  ret i32 2
case34:
  ret i32 1
case35:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f1 ( i32 %v0_0 , i32 %v0_1 ) {
b0:
  %v0_2 = call i32 @t1_0_2 ( i32 %v0_0 , i32 %v0_1 )
  ret i32 %v0_2
}

define internal i32 @t2_0_7 ( i32 %x ) {
start:
  switch i32 %x , label %miss [ i32 0 , label %case0 i32 1 , label %case1 i32 2 , label %case2 i32 3 , label %case3 i32 4 , label %case4 i32 5 , label %case5 ]
case0:
  ret i32 0
case1:
  ret i32 1
case2:
  ret i32 2
case3:
  ret i32 4
case4:
  ret i32 3
case5:
  ret i32 5
miss:
  ret i32 4294967295
}

define internal i32 @f2 ( ) {
b0:
  %v0_0 = add i32 0 , 1
  %v0_1 = add i32 0 , 2
  %v0_2 = call i32 @f0 ( i32 %v0_0 , i32 %v0_1 )
  %v0_3 = add i32 0 , 1
  %v0_4 = add i32 0 , 2
  %v0_5 = call i32 @f1 ( i32 %v0_3 , i32 %v0_4 )
  %v0_6 = add i32 0 , 3
  %v0_7 = call i32 @t2_0_7 ( i32 %v0_6 )
  %v0_8 = add i32 0 , 3
  %v0_9 = icmp eq i32 %v0_2 , %v0_8
  %v0_10 = add i32 0 , 4
  %v0_11 = icmp eq i32 %v0_5 , %v0_10
  %v0_12 = and i1 %v0_9 , %v0_11
  %v0_13 = add i32 0 , 4
  %v0_14 = icmp eq i32 %v0_7 , %v0_13
  %v0_15 = and i1 %v0_12 , %v0_14
  br i1 %v0_15 , label %b1 , label %b2
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
  %result = call i32 @f2 ( )
  ret i32 %result
}
