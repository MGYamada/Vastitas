import VastitasStorageTest.NumericalFixture

open VastitasKernel Storage NumericalFixture

/-! Closed test-only typed fixtures, not a public input format. The actual
function compiler reconstructs the values, checks the product and generates the
same accepted schedule; no manually fabricated product receipt is consumed. -/
def main (args : List String) : IO UInt32 := do
  let [kind, output] := args
    | IO.eprintln "expected real|complex output.lean"; return 1
  let scalar ← match kind with
    | "real" => pure Scalar.f64
    | "complex" => pure Scalar.complexF64
    | _ => IO.eprintln "unknown numerical fixture"; return 1
  let .ok checked := Indexed.Source.checkDeclarations source
    | IO.eprintln "numerical fixture declarations rejected"; return 1
  let implementation := if kind == "real" then "Real" else "Complex"
  let expected := if kind == "real" then Literal.f64 0x4008000000000000
    else Literal.complexF64 0xc008000000000000 0
  let cleanup := cleanup.flatMap fun statement => match statement with
    | .action (.borrow 25 ..) => [statement] ++ ([0,1].flatMap fun row =>
        [0,1].map fun column => Functions.Statement.action (.expect 25 row column expected))
    | _ => [statement]
  let input := program (setup scalar implementation ++ [multiply] ++ cleanup)
  match Functions.generate input true 1024 checked.resolved.declarations.indexed with
  | .error error => IO.eprintln s!"numerical fixture rejected: {error.code}: {error.message}"; return 1
  | .ok result => IO.FS.writeFile output result; return 0
