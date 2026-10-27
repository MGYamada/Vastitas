import VastitasKernel.Abstract
import VastitasKernel.FunctionChecker

namespace VastitasKernel.Abstract.Regression
private def path (name : String) : TypePath := ⟨[name], {}⟩
private def decl (name : String) (parents : List String := []) : RawAbstractType :=
  ⟨name, parents.map path, {}⟩
private def member (scalar target : String) : RawSubtype := ⟨scalar, path target, {}⟩
private def accepts (types : List RawAbstractType) (members : List RawSubtype := []) : Bool :=
  ((prepare types members).run {}).isOk
private def check (label : String) (valid : Bool) : IO Unit :=
  unless valid do throw (IO.userError s!"abstract hierarchy regression failed: {label}")

#eval check "uninhabited selectors" (accepts [decl "Variety", decl "Manifold"])
#eval check "multiple parents" (accepts [decl "A", decl "B", decl "C" ["A", "B"]] [member "Nat" "C"])
#eval check "self cycle" (!accepts [decl "A" ["A"]])
#eval check "cycle" (!accepts [decl "A" ["B"], decl "B" ["A"]])
#eval check "builtin relation preservation" (!accepts [decl "A" ["Number"]] [member "Bool" "A"])
#eval check "cannot edit builtins" (!accepts [] [member "Int" "Any"])
#eval check "duplicate names" (!accepts [decl "A", decl "A"])
#eval check "duplicate memberships" (!accepts [decl "A"] [member "Int" "A", member "Int" "A"])
#eval check "bad scalar" (!accepts [decl "A"] [member "Scheme" "A"])
#eval check "64 includes builtins" (accepts ((List.range 58).map fun i => decl s!"A{i}"))
#eval check "65 rejected" (!accepts ((List.range 59).map fun i => decl s!"A{i}"))

private def nominal : Bool := match (prepare [decl "A", decl "B"] [member "Int" "A", member "Int" "B"]).run {} with
  | .error _ => false
  | .ok (checked, _) =>
    let a := checked.names.idxOf "A"
    let b := checked.names.idxOf "B"
    checked.hierarchy.subtype 1 a && checked.hierarchy.subtype 1 b &&
      !checked.hierarchy.subtype a b && !checked.hierarchy.subtype b a
#eval check "same inhabitants remain nominally distinct" nominal

end VastitasKernel.Abstract.Regression
