/- Hand translation of FamilyComparison.vast after static method selection.
   Distinct symbols model separate monomorphic call targets, not an oracle
   for the resolution of Vastitas declarations. -/
@[noinline] def adjustNat (x : Nat) : Nat := x - 5
@[noinline] def adjustInt (x : Int) : Int := x - 5
@[noinline] def evaluate (flag : Bool) (n : Nat) (i : Int) : Int :=
  if flag then Int.ofNat (adjustNat n) else adjustInt i

-- Both inputs are borrowed across the C ABI. Explicitly retain the Nat
-- before its consuming conversion when using the C runtime from LLVM.
@[noinline]
def divNatInt (n : @& Nat) (i : @& Int) : Int := Int.ofNat n / i
@[noinline]
def divIntNat (i : @& Int) (n : @& Nat) : Int := i / Int.ofNat n

def main : IO UInt32 :=
  pure <| if evaluate true 2 2 == 0 && evaluate false 2 2 == -3 && divIntNat (-7) 3 == -3 && divNatInt 7 (-3) == -2 then 0 else 1
