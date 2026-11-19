/- A constructor case for comparison with Lean.Compiler.IR.EmitLLVM.emitCase.
The outer UInt32 ABI defines behavior for foreign ordinals too. -/
inductive Input where | first | second | third

@[noinline] def image : Input → UInt32
  | .first => 1
  | .second => 0
  | .third => 1

@[noinline] def lookup (i : UInt32) : UInt32 :=
  match i with
  | 0 => image .first
  | 1 => image .second
  | 2 => image .third
  | _ => 0xFFFFFFFF

@[noinline] def forward (i : UInt32) : UInt32 := lookup i

def main : IO Unit := do
  for i in [0, 1, 2, 3, 4095, 0xFFFFFFFF] do IO.println (forward i)
