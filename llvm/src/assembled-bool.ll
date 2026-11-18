target triple = "\61\72\6D\36\34\2D\61\70\70\6C\65\2D\64\61\72\77\69\6E\32\37\2E\32\2E\30"
target datalayout = "\65\2D\6D\3A\6F\2D\70\32\37\30\3A\33\32\3A\33\32\2D\70\32\37\31\3A\33\32\3A\33\32\2D\70\32\37\32\3A\36\34\3A\36\34\2D\69\36\34\3A\36\34\2D\69\31\32\38\3A\31\32\38\2D\6E\33\32\3A\36\34\2D\53\31\32\38\2D\46\6E\33\32"

define i32 @main() {
entry:
  %choice = call i1 @vq_selected(i1 1)
  br i1 %choice, label %yes, label %no
yes:
  br label %exit
no:
  br label %exit
exit:
  %status = phi i32 [ u0x2A, %yes ], [ u0x07, %no ]
  ret i32 %status
}

define internal i1 @vq_selected(i1 %arg) {
entry:
  ret i1 %arg
}

define internal i1 @vq_method0000(i1 %arg) {
entry:
  ret i1 0
}
