import VastitasOracle.BoxedCertificate

open Lean VastitasKernel VastitasKernel.LLVM
open VastitasOracle.BoxedCertificate

private def instruction : ExactProgram.Instruction → Json
  | .primitive (.nat n) => toJson ["nat", toString n]
  | .primitive (.int n) => toJson ["int", toString n]
  | .primitive (.apply op refs) => Json.arr #[toJson "apply", toJson op.name, toJson refs]
  | .invoke callee refs => Json.arr #[toJson "invoke", toJson callee, toJson refs]

private def body (f : ExactProgram.Function) := Json.mkObj [
  ("params", toJson (f.params.map ExactLibrary.Kind.name)), ("result", toJson f.output.name),
  ("ops", toJson (f.ops.map instruction)), ("slot", toJson f.result)]

/-- Return independent witness data from the actual linked program. The
driver compares its entire revision and bytes with the public CLI capture. -/
def main (args : List String) : IO Unit := do
  let [file,triple,layout] := args | throw (IO.userError "expected revision file, triple and data layout")
  let rev ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let wire ← IO.ofExcept (rev.getObjVal? "input")
  let some t := checkTargetText .triple triple.toUTF8.data.toList | throw (IO.userError "invalid target")
  let some l := checkTargetText .dataLayout layout.toUTF8.data.toList | throw (IO.userError "invalid layout")
  let some ⟨s,_⟩ := capture wire ⟨t,l⟩ true | throw (IO.userError "expected a checked boxed executable")
  unless s.revision.compress == rev.compress do throw (IO.userError "different complete function revision")
  let some text := String.fromUTF8? ⟨s.bytes.toArray⟩ | throw (IO.userError "invalid LLVM bytes")
  IO.println (Json.mkObj [("ir",toJson text), ("entry",toJson s.code.entry), ("value",toJson (toString s.value)),
    ("functions",toJson (s.code.functions.map body))]).compress
