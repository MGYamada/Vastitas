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
def elaborationWork : Nat := compiler_limit% "elaborationWork"
def resourceWork : Nat := compiler_limit% "resourceWork"
def generatedLets : Nat := compiler_limit% "generatedLets"
/-- The maps of one compiled reverse pass that the compilation reads through
`let`s and compositions (#623); beyond it, a map value is one step. -/
def reverseLeaves : Nat := compiler_limit% "reverseLeaves"
def specializations : Nat := compiler_limit% "specializations"
def dispatchKeys : Nat := compiler_limit% "dispatchKeys"
def dispatchArity : Nat := compiler_limit% "dispatchArity"
def dispatchWork : Nat := compiler_limit% "dispatchWork"
def nominalTypes : Nat := compiler_limit% "nominalTypes"
def namespaceResolution : Nat := compiler_limit% "namespaceResolution"
def namespaceImportWork : Nat := compiler_limit% "namespaceImportWork"
def namespaceProgramWork : Nat := compiler_limit% "namespaceProgramWork"
def dependencyGraph : Nat := compiler_limit% "dependencyGraph"

def assemblyEvents : Nat := compiler_limit% "assemblyEvents"
def authorityTraceWork : Nat := compiler_limit% "authorityTraceWork"
def contributionMethods : Nat := compiler_limit% "contributionMethods"

/-! Finite Stage 2 algebra: generators per ring, declared relations, source
degree, polynomial terms, reduced basis size, decimal digits per source
integer, base-chain length and weighted checker work. -/
def algebraGenerators : Nat := compiler_limit% "algebraGenerators"
def algebraRelations : Nat := compiler_limit% "algebraRelations"
def algebraDegree : Nat := compiler_limit% "algebraDegree"
def algebraTerms : Nat := compiler_limit% "algebraTerms"
def algebraBasis : Nat := compiler_limit% "algebraBasis"
def algebraCoefficientDigits : Nat := compiler_limit% "algebraCoefficientDigits"
def algebraChain : Nat := compiler_limit% "algebraChain"
def algebraWork : Nat := compiler_limit% "algebraWork"
/-- Parenthesized nesting of one polynomial expression on the wire. -/
def algebraNesting : Nat := compiler_limit% "algebraNesting"

/-! Finite Stage 3 metrics: the size of one elaborated Gram entry and the size
of the whole Gram matrix. The entry bound does not bound a certificate: the
exact inverse grows with the least common denominators of the rows, not with
the entries alone. The matrix bound does, and it is checked before any inverse
or `L D Lᵀ` factorization is computed (`SmoothDeclarations.matrixBounded`). -/
/-- Bits of the numerator and of the denominator of one Gram entry. -/
def metricEntryBits : Nat := compiler_limit% "metricEntryBits"
/-- Bits of the Hadamard bound of one Gram matrix: the product of the
Euclidean norms of its rows, each cleared of its denominators, and of the
largest row denominator. -/
def metricMatrixBits : Nat := compiler_limit% "metricMatrixBits"

end VastitasKernel.Limits
