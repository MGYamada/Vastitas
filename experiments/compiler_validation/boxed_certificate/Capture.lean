import VastitasOracle.BoxedCertificate
import VastitasOracle.FlowCertificate

open Lean VastitasKernel VastitasKernel.LLVM
open VastitasOracle.BoxedCertificate

private def instruction : ExactProgram.Instruction → Json
  | .primitive (.nat n) => toJson ["nat", toString n]
  | .primitive (.int n) => toJson ["int", toString n]
  | .primitive (.apply op refs) => Json.arr #[toJson "apply", toJson op.name, toJson refs]
  | .primitive (.compare sort op left right) =>
    Json.arr #[toJson "compare", toJson sort.label, toJson op.tag, toJson left, toJson right]
  | .invoke callee refs => Json.arr #[toJson "invoke", toJson callee, toJson refs]

private def body (f : ExactProgram.Function) := Json.mkObj [
  ("params", toJson (f.params.map ExactLibrary.Kind.name)), ("result", toJson f.output.name),
  ("ops", toJson (f.ops.map instruction)), ("slot", toJson f.result)]

private def flowOp : ExactFlow.Op → Json
  | .exact s => instruction (.primitive s)
  | .invoke i args => instruction (.invoke i args)
  | .boolean b => Json.arr #[toJson "bool",toJson b]
  | .boolNot a => Json.arr #[toJson "not",toJson a]
  | .boolAnd a b => Json.arr #[toJson "and",toJson a,toJson b]
  | .boolOr a b => Json.arr #[toJson "or",toJson a,toJson b]
  | .boolEq a b => Json.arr #[toJson "eq",toJson a,toJson b]
  | .boolNe a b => Json.arr #[toJson "ne",toJson a,toJson b]

private def edge (e : ExactFlow.Edge) := Json.arr #[toJson e.dest,toJson e.args]

private def flowBlock (b : ExactFlow.Block) := Json.mkObj [
  ("params",toJson (b.params.map ExactLibrary.Kind.name)), ("ops",toJson (b.ops.map flowOp)),
  ("exit",match b.exit with
    | .ret r => Json.arr #[toJson "ret",toJson r]
    | .jump e => Json.arr #[toJson "jump",edge e]
    | .branch r y n => Json.arr #[toJson "branch",toJson r,edge y,edge n])]

private def flowFunction (f : ExactFlow.Func) := Json.mkObj [
  ("result",toJson f.result.name), ("blocks",toJson (f.blocks.map flowBlock))]

/-- Return independent witness data from the actual linked program. The
driver compares its entire revision and bytes with the public CLI capture. -/
def main (args : List String) : IO Unit := do
  let [file,triple,layout,kind] := args | throw (IO.userError "expected revision file, triple, data layout and graph kind")
  let rev ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let wire ← IO.ofExcept (rev.getObjVal? "input")
  let some t := checkTargetText .triple triple.toUTF8.data.toList | throw (IO.userError "invalid target")
  let some l := checkTargetText .dataLayout layout.toUTF8.data.toList | throw (IO.userError "invalid layout")
  let (revision,bytes,entry,value,functions) ← match kind with
    | "flow" => do
      let some ⟨s,_⟩ := VastitasOracle.FlowCertificate.capture wire ⟨t,l⟩ true
        | throw (IO.userError "expected a checked control-flow program")
      pure (s.revision,s.bytes,s.code.entry,s.value,s.code.functions.map flowFunction)
    | "program" => do
      let some ⟨s,_⟩ := capture wire ⟨t,l⟩ true | throw (IO.userError "expected a checked boxed program")
      pure (s.revision,s.bytes,s.code.entry,s.value,s.code.functions.map body)
    | _ => throw (IO.userError "unknown graph kind")
  unless revision.compress == rev.compress do throw (IO.userError "different complete function revision")
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw (IO.userError "invalid LLVM bytes")
  IO.println (Json.mkObj [("kind",toJson kind), ("ir",toJson text), ("entry",toJson entry),
    ("value",toJson (toString value)), ("functions",toJson functions)]).compress
