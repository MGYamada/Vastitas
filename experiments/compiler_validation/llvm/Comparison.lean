/- Inputs shared with the LLVM ABI fixture. This is a comparison corpus,
not proof that either compiler preserves Vastitas semantics. -/
@[noinline] def square (n : Nat) : Nat := n * n
@[noinline] def quotient (n d : Int) : Int := n / d
@[noinline] def saturating (n m : Nat) : Nat := n - m
@[noinline] def choose (b : Bool) (x y : Nat) : Nat := if b then x else y
@[noinline] def pair (x y : Nat) : Nat × Nat := (x, y)

def main : IO UInt32 := do
  let n := 18446744073709551616
  pure <| if square n == 340282366920938463463374607431768211456 &&
    quotient (-7) 3 == -3 && quotient (-7) 0 == 0 && saturating 2 5 == 0 &&
    choose true 7 9 == 7 && (pair 4 5).2 == 5 then 0 else 1
