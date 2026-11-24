@[export vastitas_int_compare_reference]
def compareInt (op : UInt8) (a b : Int) : Bool :=
  match op with
  | 0 => a == b | 1 => a != b
  | 2 => decide (a < b) | 3 => decide (a ≤ b)
  | 4 => decide (a > b) | _ => decide (a ≥ b)

@[export vastitas_nat_compare_reference]
def compareNat (op : UInt8) (a b : Nat) : Bool :=
  match op with
  | 0 => a == b | 1 => a != b
  | 2 => decide (a < b) | 3 => decide (a ≤ b)
  | 4 => decide (a > b) | _ => decide (a ≥ b)

@[noinline, export vastitas_bool_compare_reference]
def compareBool (different a b : Bool) : Bool :=
  if different then a != b else a == b

def main (args : List String) : IO Unit := do
  if let ["Bool", op] := args then
    let different ← match op with
      | "eq" => pure false | "ne" => pure true | _ => throw (IO.userError "invalid Boolean predicate")
    let mut total : Int := 2^128 + 1
    for (a,b,weight) in [(false,false,1), (false,true,2), (true,false,4), (true,true,8)] do
      if compareBool different a b then total := total + weight
    IO.println total
    return
  let [ty, code, left, right] := args | throw (IO.userError "expected type, predicate and both operands")
  let some c := code.toNat? | throw (IO.userError "invalid predicate")
  let result ← match ty with
    | "Int" => do
      let some a := left.toInt? | throw (IO.userError "invalid Int")
      let some b := right.toInt? | throw (IO.userError "invalid Int")
      pure (compareInt c.toUInt8 a b)
    | "Nat" => do
      let some a := left.toNat? | throw (IO.userError "invalid Nat")
      let some b := right.toNat? | throw (IO.userError "invalid Nat")
      pure (compareNat c.toUInt8 a b)
    | _ => throw (IO.userError "invalid type")
  IO.println (if result then 42 else 7)
