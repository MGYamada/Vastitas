@[export corpus_component32]
def component32 (first : Bool) : UInt32 :=
  if first then 2147483648 else 2139095106

def main : IO Unit := do
  IO.println s!"{component32 true} {component32 false}"
