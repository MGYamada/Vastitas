@[export assembled_negate]
def reverseSign (x : Int) : Int := -x

def main (args : List String) : IO Unit := do
  let x : Int := 2^128 + 43
  IO.println (if args.isEmpty then x else reverseSign x)
