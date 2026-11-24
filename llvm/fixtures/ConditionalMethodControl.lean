@[export vastitas_conditional_reference]
def chooseInteger (flag : Bool) (left right : Int) : Int :=
  if flag then left else right

def main (args : List String) : IO Unit := do
  IO.println (chooseInteger args.isEmpty (2^128 + 43) (-19))
