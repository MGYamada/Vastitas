import VastitasKernel.OperatorNames
import VastitasKernel.IndexedCore

namespace VastitasKernel.Indexed.ExactOperators

structure Selection where
  family : Namespace.FunctionId
  key : List Core.DataType
  deriving Repr, Inhabited, DecidableEq

def Selection.scalarKey (s : Selection) : List String :=
  s.key.map fun t => match t with | .pure .nat => "Nat" | .pure .int => "Int" | _ => "invalid"

def selection? : Core.Term → Option Selection
  | .unary .neg arg _ => some ⟨Namespace.operatorId "neg", [arg.result.type]⟩
  | .binary op a b _ => do
    let name ← match op with
      | .add => some "add" | .sub => some "sub" | .mul => some "mul" | .div => some "div" | _ => none
    return ⟨Namespace.operatorId name, [a.result.type, b.result.type]⟩
  | _ => none

private def collect (t : Core.Term) : List Selection :=
  (selection? t).toList ++ match t with
  | .call _ args _ _ | .primitive _ args _ => args.flatMap collect
  | .unary _ v _ | .project _ _ v | .ascribe _ v | .natToInt v | .scope v => collect v
  | .binary _ a b _ | .pair _ a b | .unpack _ _ a b | .letE _ a b => collect a ++ collect b
  | .branch c a b _ => collect c ++ collect a ++ collect b
  | .pack _ w fs => collect w ++ fs.flatMap collect
  | .finiteLookup .. | .finiteTag .. | .natural _ | .integer _ | .boolean _ | .unit | .variable .. => []

def selections (m : Core.Module) : List (Nat × Selection) :=
  m.functions.flatMap fun f => (collect f.body).map fun s => (f.id, s)

end VastitasKernel.Indexed.ExactOperators
