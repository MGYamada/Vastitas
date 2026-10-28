import Lean.Elab.Term

/-! The shared resource policy is reified as ordinary transparent Nat constants.
There is no runtime configuration or unchecked axiom. Lake tracks the JSON input;
Cargo reads the same file for the frontend's limits. -/
namespace VastitasKernel.Limits

open Lean Elab Term in
elab "compiler_limit% " key:str : term => do
  let file := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let source ← IO.FS.readFile (file.parent.getD "." / "../compiler-limits.json")
  let .ok json := Json.parse source | throwError "invalid compiler limits JSON"
  let .ok value := json.getObjValAs? Nat key.getString
    | throwError "missing or invalid compiler limit: {key.getString}"
  if value == 0 then throwError "compiler limits must be positive"
  pure (mkNatLit value)

def typeNesting : Nat := compiler_limit% "typeNesting"
def sourceNesting : Nat := compiler_limit% "sourceNesting"
def namespaceNesting : Nat := compiler_limit% "namespaceNesting"
def captureDiagnostic : Nat := compiler_limit% "captureDiagnostic"
def bodyChecking : Nat := compiler_limit% "bodyChecking"
def generatedLets : Nat := compiler_limit% "generatedLets"
def specializations : Nat := compiler_limit% "specializations"
def dispatchKeys : Nat := compiler_limit% "dispatchKeys"
def dispatchArity : Nat := compiler_limit% "dispatchArity"
def nominalTypes : Nat := compiler_limit% "nominalTypes"
def namespaceResolution : Nat := compiler_limit% "namespaceResolution"
def dependencyGraph : Nat := compiler_limit% "dependencyGraph"

def assemblyEvents : Nat := compiler_limit% "assemblyEvents"
def contributionMethods : Nat := compiler_limit% "contributionMethods"

end VastitasKernel.Limits
