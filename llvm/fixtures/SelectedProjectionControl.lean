@[export field_first]
def fieldFirst (p : Nat × Nat) : Nat := p.1

@[export field_second]
def fieldSecond (p : Nat × Nat) : Nat := p.2

def main (args : List String) : IO UInt32 :=
  let p := (7, 19)
  pure (if args.isEmpty then fieldFirst p else fieldSecond p).toUInt32
