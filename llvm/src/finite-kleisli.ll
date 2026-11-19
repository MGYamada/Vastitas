target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

define internal i32 @t0_0_1 ( i32 %x ) {
start:
  switch i32 %x , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f0 ( i32 %v0_0 ) {
b0:
  %v0_1 = call i32 @t0_0_1 ( i32 %v0_0 )
  ret i32 %v0_1
}

define internal i32 @f1 ( ) {
b0:
  %v0_0 = add i32 0 , 0
  ret i32 %v0_0
}

define internal i32 @t2_0_2 ( i32 %x ) {
start:
  switch i32 %x , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @t2_0_4 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 1
  %colOK = icmp ult i32 %y , 1
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 1
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @t2_0_5 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 1
  %colOK = icmp ult i32 %y , 1
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 1
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f2 ( i32 %v0_0 , i32 %v0_1 ) {
b0:
  %v0_2 = call i32 @t2_0_2 ( i32 %v0_1 )
  %v0_3 = add i32 0 , 0
  %v0_4 = call i32 @t2_0_4 ( i32 %v0_3 , i32 %v0_2 )
  %v0_5 = call i32 @t2_0_5 ( i32 %v0_4 , i32 %v0_0 )
  ret i32 %v0_5
}

define internal i32 @t3_0_2 ( i32 %x ) {
start:
  switch i32 %x , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @t3_0_4 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 1
  %colOK = icmp ult i32 %y , 1
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 1
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @t3_0_5 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 1
  %colOK = icmp ult i32 %y , 1
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 1
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f3 ( i32 %v0_0 , i32 %v0_1 ) {
b0:
  %v0_2 = call i32 @t3_0_2 ( i32 %v0_0 )
  %v0_3 = add i32 0 , 0
  %v0_4 = call i32 @t3_0_4 ( i32 %v0_3 , i32 %v0_2 )
  %v0_5 = call i32 @t3_0_5 ( i32 %v0_4 , i32 %v0_1 )
  ret i32 %v0_5
}

define internal i32 @t4_0_2 ( i32 %x , i32 %y ) {
start:
  %rowOK = icmp ult i32 %x , 1
  %colOK = icmp ult i32 %y , 1
  %both = and i1 %rowOK , %colOK
  br i1 %both , label %lookup , label %miss
lookup:
  %base = mul i32 %x , 1
  %index = add i32 %base , %y
  switch i32 %index , label %miss [ i32 0 , label %case0 ]
case0:
  ret i32 0
miss:
  ret i32 4294967295
}

define internal i32 @f4 ( i32 %v0_0 ) {
b0:
  %v0_1 = add i32 0 , 0
  %v0_2 = call i32 @t4_0_2 ( i32 %v0_1 , i32 %v0_0 )
  ret i32 %v0_2
}

define internal i32 @f5 ( ) {
b0:
  %v0_0 = call i32 @f1 ( )
  %v0_1 = add i32 0 , 0
  %v0_2 = call i32 @f2 ( i32 %v0_0 , i32 %v0_1 )
  %v0_3 = add i32 0 , 0
  %v0_4 = call i32 @f3 ( i32 %v0_3 , i32 %v0_0 )
  %v0_5 = add i32 0 , 0
  %v0_6 = call i32 @f4 ( i32 %v0_5 )
  %v0_7 = add i32 0 , 0
  %v0_8 = icmp eq i32 %v0_0 , %v0_7
  %v0_9 = add i32 0 , 0
  %v0_10 = icmp eq i32 %v0_2 , %v0_9
  %v0_11 = and i1 %v0_8 , %v0_10
  %v0_12 = icmp eq i32 %v0_4 , %v0_2
  %v0_13 = and i1 %v0_11 , %v0_12
  %v0_14 = add i32 0 , 0
  %v0_15 = icmp eq i32 %v0_6 , %v0_14
  %v0_16 = and i1 %v0_13 , %v0_15
  %v0_17 = add i32 0 , 0
  %v0_18 = call i32 @f0 ( i32 %v0_17 )
  %v0_19 = add i32 0 , 0
  %v0_20 = icmp eq i32 %v0_18 , %v0_19
  %v0_21 = and i1 %v0_16 , %v0_20
  br i1 %v0_21 , label %b1 , label %b2
b1:
  %v1_0 = add i32 0 , 0
  br label %b3
b2:
  %v2_0 = add i32 0 , 1
  br label %b3
b3:
  %v3_0 = phi i32 [ %v1_0 , %b1 ] , [ %v2_0 , %b2 ]
  ret i32 %v3_0
}

define i32 @main ( ) {
start:
  %result = call i32 @f5 ( )
  ret i32 %result
}
