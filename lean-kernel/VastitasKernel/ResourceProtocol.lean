import VastitasKernel.ResourceCodegen
import VastitasKernel.StorageFunctionProtocol
import VastitasKernel.IndexedProtocol

namespace VastitasKernel.ResourceSource.Wire
open Lean JsonDecode

private def size (j : Json) (key : String) : Except String Nat := do
  let value ← j.getObjValAs? Nat key
  if value ≥ 2^64 then throw "resource source integer exceeds 64 bits"
  return value

private def parameter (j : Json) : Except String Parameter := do
  let span ← decodeSpan j
  match ← str j "kind" with
  | "owned" =>
    fields j ["kind", "name", "type", "span"]
    return .owned (← str j "name") (← Storage.Functions.Wire.ownedType (← field j "type")) span
  | "borrowed" =>
    fields j ["kind", "name", "scalar", "rows", "columns", "access", "initializes", "span"]
    return .borrowed (← str j "name") (← Storage.Wire.scalar (← str j "scalar"))
      (← size j "rows") (← size j "columns") (← Storage.Wire.access (← str j "access"))
      (← j.getObjValAs? Bool "initializes") span
  | "space" =>
    fields j ["kind", "name", "implementation", "dimension", "span"]
    return .space (← str j "name") (← Indexed.Wire.path (← field j "implementation"))
      (← size j "dimension") span
  | "basis" =>
    fields j ["kind", "name", "space", "span"]
    return .basis (← str j "name") (← str j "space") span
  | "involution" =>
    fields j ["kind", "name", "space", "span"]
    return .involution (← str j "name") (← str j "space") span
  | "dual_space" =>
    fields j ["kind", "name", "parent", "span"]
    return .dualSpace (← str j "name") (← str j "parent") span
  | "conjugate_space" =>
    fields j ["kind", "name", "parent", "involution", "span"]
    return .conjugateSpace (← str j "name") (← str j "parent") (← str j "involution") span
  | "derived_basis" =>
    fields j ["kind", "name", "parent", "space", "span"]
    return .derivedBasis (← str j "name") (← str j "parent") (← str j "space") span
  | "metric" =>
    fields j ["kind", "name", "basis", "involution", "orthonormal", "span"]
    return .metric (← str j "name") (← str j "basis") (← str j "involution")
      (← j.getObjValAs? Bool "orthonormal") span
  | "map" =>
    fields j ["kind", "name", "source", "target", "access", "initializes", "span"]
    return .map (← str j "name") (← str j "source") (← str j "target")
      (← Storage.Wire.access (← str j "access")) (← j.getObjValAs? Bool "initializes") span
  | "owned_map" =>
    fields j ["kind", "name", "source", "target", "span"]
    return .ownedMap (← str j "name") (← str j "source") (← str j "target") span
  | _ => throw "unknown resource source parameter kind"

private def action (j : Json) : Except String Action := do
  match ← str j "op" with
  | "allocate" =>
    fields j ["op", "owner", "scalar", "elements"]
    return .allocate (← str j "owner") (← Storage.Wire.scalar (← str j "scalar")) (← size j "elements")
  | "move" => fields j ["op", "source", "target"]; return .move (← str j "source") (← str j "target")
  | "drop" => fields j ["op", "owner"]; return .drop (← str j "owner")
  | "borrow" =>
    fields j ["op", "name", "source", "layout", "access"]
    return .borrow (← str j "name") (← str j "source") (← Storage.Wire.layout (← field j "layout"))
      (← Storage.Wire.access (← str j "access"))
  | "release" => fields j ["op", "loan"]; return .release (← str j "loan")
  | "transpose" => fields j ["op", "loan"]; return .transpose (← str j "loan")
  | "fill" =>
    fields j ["op", "loan", "value"]
    return .fill (← str j "loan") (← Storage.Wire.literal (← field j "value"))
  | "store" | "expect" =>
    fields j ["op", "loan", "row", "column", "value"]
    let operation := if (← str j "op") == "store" then Action.store else Action.expect
    return operation (← str j "loan") (← size j "row") (← size j "column")
      (← Storage.Wire.literal (← field j "value"))
  | "copy" => fields j ["op", "source", "target"]; return .copy (← str j "source") (← str j "target")
  | _ => throw "unknown resource source operation"

private def coefficient (j : Json) : Except String Coefficient := do
  match ← str j "kind" with
  | "literal" => fields j ["kind", "value"]; return .literal (← Storage.Wire.literal (← field j "value"))
  | "loan" => fields j ["kind", "loan"]; return .loan (← str j "loan")
  | _ => throw "unknown numerical coefficient kind"

private def optionalCoefficient (j : Json) (name : String) : Except String (Option Coefficient) :=
  match j.getObjVal? name with
  | .error _ => pure none
  | .ok value => some <$> coefficient value

private def exactInteger (value : String) : Except String Int :=
  match value.toInt? with | some integer => pure integer | none => throw "Gram entries require exact decimal integers"

private def gram (j : Json) : Except String Storage.Numerical.Gram := do
  match ← str j "kind" with
  | "identity" => fields j ["kind"]; return .identity
  | "scaled_identity" =>
    fields j ["kind", "entry"]
    return .scaledIdentity (← exactInteger (← str j "entry"))
  | "diagonal" =>
    fields j ["kind", "entries"]
    let entries ← array j "entries"
    if entries.length > 4096 then throw "diagonal Gram data exceeds the 4096-entry bound"
    return .diagonal (← entries.mapM fun entry => do exactInteger (← entry.getStr?))
  | _ => throw "unknown declared Gram representation"

private def transform (j : Json) : Except String (Storage.Numerical.Transform String) := do
  match ← str j "kind" with
  | "dual" =>
    fields j ["kind", "source", "target"]
    return .dual (← str j "source") (← str j "target")
  | "conjugate" =>
    fields j ["kind", "source", "target", "involution"]
    return .conjugate (← str j "source") (← str j "target") (← str j "involution")
  | "adjoint" =>
    fields j ["kind", "source_metric", "target_metric"]
    return .adjoint (← str j "source_metric") (← str j "target_metric")
  | _ => throw "unknown typed map transform"

private def numericalOperation (j : Json) : Except String NumericalOperation := do
  match ← str j "op" with
  | "space" =>
    fields j ["op", "name", "implementation", "dimension"]
    return .space (← str j "name") (← Indexed.Wire.path (← field j "implementation")) (← size j "dimension")
  | "basis" =>
    fields j ["op", "name", "space"]
    return .basis (← str j "name") (← str j "space")
  | "involution" =>
    fields j ["op", "name", "space"]
    return .involution (← str j "name") (← str j "space")
  | "dual_space" =>
    fields j ["op", "name", "parent"]
    return .dualSpace (← str j "name") (← str j "parent")
  | "conjugate_space" =>
    fields j ["op", "name", "parent", "involution"]
    return .conjugateSpace (← str j "name") (← str j "parent") (← str j "involution")
  | "derived_basis" =>
    fields j ["op", "name", "parent", "space"]
    return .derivedBasis (← str j "name") (← str j "parent") (← str j "space")
  | "metric" =>
    fields j ["op", "name", "basis", "involution", "gram"]
    return .metric (← str j "name") (← str j "basis") (← str j "involution") (← gram (← field j "gram"))
  | "transform" =>
    fields j ["op", "name", "parent", "operation"]
    return .transform (← str j "name") (← str j "parent") (← transform (← field j "operation"))
  | "map" =>
    fields j ["op", "name", "loan", "source", "target"]
    return .map (← str j "name") (← str j "loan") (← str j "source") (← str j "target")
  | "owned_map" =>
    fields j ["op", "name", "owner", "layout", "source", "target"]
    return .ownedMap (← str j "name") (← str j "owner") (← Storage.Wire.layout (← field j "layout"))
      (← str j "source") (← str j "target")
  | "owned_view" =>
    fields j ["op", "name", "loan", "owner"]
    return .ownedView (← str j "name") (← str j "loan") (← str j "owner")
  | "borrow_owned" =>
    fields j ["op", "name", "owner", "access"]
    return .borrowOwned (← str j "name") (← str j "owner") (← Storage.Wire.access (← str j "access"))
  | "gemm" =>
    fields j ["op", "left", "right", "output", "mode", "policy", "alpha", "beta"]
    return .gemm (← str j "left") (← str j "right") (← str j "output")
      (← Storage.Wire.gemmMode (← str j "mode")) (← Storage.Wire.numericalPolicy (← str j "policy"))
      (← optionalCoefficient j "alpha") (← optionalCoefficient j "beta")
  | _ => throw "unknown numerical source operation"

private def networkPort (j : Json) : Except String Storage.TensorNetwork.Port := do
  fields j ["occurrence", "role"]
  let role ← match ← str j "role" with
    | "input" => pure Storage.TensorNetwork.Role.input
    | "output" => pure .output
    | _ => throw "network port role must be input (algebraic dual) or output (vector)"
  return ⟨← str j "occurrence", role⟩

private def networkGraph (j : Json) : Except String (Storage.TensorNetwork.Graph String) := do
  fields j ["occurrences", "edges", "inputs", "outputs"]
  let occurrences ← array j "occurrences"
  let edges ← array j "edges"
  let inputs ← array j "inputs"
  let outputs ← array j "outputs"
  unless occurrences.length == 2 && edges.length == 1 && inputs.length == 1 && outputs.length == 1 do
    throw "two-map network requires two occurrences, one edge and explicit input/output boundaries"
  let occurrences ← occurrences.mapM fun node => do
    fields node ["name", "value"]
    return Storage.TensorNetwork.Occurrence.mk (← str node "name") (← str node "value")
  let edges ← edges.mapM fun edge => do
    fields edge ["dual", "primal"]
    return Storage.TensorNetwork.Edge.mk (← networkPort (← field edge "dual")) (← networkPort (← field edge "primal"))
  return ⟨occurrences, edges, ← inputs.mapM networkPort, ← outputs.mapM networkPort⟩

private def statements : Nat → List Json → Except String (List Statement)
  | _, [] => pure []
  | 0, _ :: _ => throw "resource source exceeds decoding depth bound"
  | fuel + 1, first :: rest => do
    let span ← decodeSpan first
    let statement ← match ← str first "kind" with
      | "action" =>
        fields first ["kind", "action", "span"]
        pure (.action (← action (← field first "action")) span)
      | "network" =>
        fields first ["kind", "graph", "output", "policy", "span"]
        pure (.network (← networkGraph (← field first "graph")) (← str first "output")
          (← Storage.Wire.numericalPolicy (← str first "policy")) span)
      | "numerical" =>
        fields first ["kind", "operation", "span"]
        pure (.numerical (← numericalOperation (← field first "operation")) span)
      | "call" =>
        fields first ["kind", "callee", "arguments", "results", "span"]
        pure (.call (← Indexed.Wire.namedPath (← str first "callee") span)
          (← (← array first "arguments").mapM Json.getStr?)
          (← (← array first "results").mapM Json.getStr?) span)
      | "branch" =>
        fields first ["kind", "condition", "yes", "no", "span"]
        pure (.branch (← first.getObjValAs? Bool "condition")
          (← statements fuel (← array first "yes")) (← statements fuel (← array first "no")) span)
      | _ => throw "unknown resource source statement"
    return statement :: (← statements fuel rest)

private def resultType (j : Json) : Except String (Storage.Functions.ResultType String) := do
  match j.getObjVal? "kind" with
  | .error _ => return .owned (← Storage.Functions.Wire.ownedType j)
  | .ok _ =>
    fields j ["kind", "source", "target"]
    if (← str j "kind") != "owned_map" then throw "unknown resource result type"
    return .ownedMap (← str j "source") (← str j "target")

def function (j : Json) : Except String Function := do
  fields j ["name", "parameters", "results", "body", "value_type", "value_body", "span", "public"]
  let results ← (← array j "results").mapM fun result => do
    fields result ["name", "type"]
    return (← str result "name", ← resultType (← field result "type"))
  return {
    name := ← str j "name", parameters := ← (← array j "parameters").mapM parameter, results,
    body := ← statements 4096 (← array j "body"), valueType := ← Indexed.Wire.pureType (← field j "value_type"),
    valueBody := ← Indexed.Wire.block Limits.sourceNesting (← field j "value_body"),
    isPublic := ← j.getObjValAs? Bool "public", span := ← decodeSpan j }

private def without (j : Json) (key : String) : Except String Json := do
  return Json.mkObj ((← j.getObj?).toArray.toList.filter (·.1 != key))

def module (j : Json) : Except String Module := do
  let pureModule ← Indexed.Wire.module (← without j "resource_functions") true
  return ⟨pureModule, ← (← optionalArray j "resource_functions").mapM function⟩

def package (j : Json) : Except String Package := do
  let modules ← (← array j "modules").mapM module
  -- Reuse the exact package metadata decoder, with no resource body projected
  -- into a pure function. Unknown metadata fields remain rejected.
  let stripped ← (← array j "modules").mapM (without · "resource_functions")
  let metadata := (← without j "modules").setObjVal! "modules" (toJson stripped)
  let pkg ← Indexed.Wire.package metadata true
  return ⟨pkg.id, pkg.dependencies, modules, pkg.geometryCompat⟩

def program (j : Json) : Except String Program := do
  fields j ["version", "input", "file", "root", "packages"]
  if (← j.getObjValAs? Nat "version") != 8 then throw "expected protocol 8"
  if (← str j "input") != "package" then throw "protocol 8 requires package input"
  return ⟨← str j "file", ← str j "root", ← (← array j "packages").mapM package⟩

structure CheckedInput (json : Json) (requireMain : Bool) where
  input : Program
  decoded : program json = .ok input
  checked : Checked input requireMain
  accepted : ResourceSource.check input requireMain = .ok checked

def check (json : Json) (requireMain : Bool) : Except Diagnostic (CheckedInput json requireMain) :=
  match decoded : program json with
  | .error message => .error {code := "E_PROTOCOL", message}
  | .ok input => match accepted : ResourceSource.check input requireMain with
    | .error diagnostic => .error diagnostic
    | .ok checked => .ok ⟨input, decoded, checked, accepted⟩

end VastitasKernel.ResourceSource.Wire
