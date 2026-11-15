import VastitasKernel.IndexedNatureSource
import VastitasKernel.SpectralDeclarations
import VastitasKernel.IndexedSpectralContracts

set_option autoImplicit false

/-! Source elaboration of the spectral declarations, invariants and
observations (Stage 5, #806; `std::linalg::spectral`).

A free module, an endomorphism, a spectrum and a branch are declared at a
family with the representation `free_module`, `endomorphism`, `spectrum` and
`branch` and one smooth object. `resolveBody` resolves their paths and leaves
their rows, certificates and polynomials empty; a `trace_power(H, k)` or
`char_coefficient(S, i)` morphism stays the placeholder of a declared
morphism, which `elaborateSmooth` passes through; and the observations
`annihilates`, `action_entry`, `on_branch`, `branch_differential` and
`branch_projector` embed placeholders (`SpectrumRef.placeholder`,
`BranchRef.placeholder`). This pass elaborates all of them, after the nature
declarations and before the relative morphisms. Its rejections are
`E_SPECTRAL`.

Not implemented yet: the pass rejects every spectral declaration, every
spectral invariant and every spectral observation with `E_SPECTRAL` at its
place, and leaves a program without them unchanged. -/
namespace VastitasKernel.Indexed.Source

def spectralProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_SPECTRAL" reason

private def spectralSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

/-- What a diagnostic calls a spectral declaration, or `none` for another
declaration. -/
private def spectralDeclarationKind? : Indexed.Declaration → Option String
  | .freeModule .. => some "free module"
  | .endomorphism .. => some "endomorphism"
  | .spectrum .. => some "spectrum"
  | .branch .. => some "branch"
  | _ => none

/-- The source spelling of a spectral binding, or `none` for another binding.
A spectral invariant is still the placeholder of a declared morphism here, so
the source body decides it. -/
private def spectralBindingSpelling? (binding : PrimitiveBinding) (body : Option Body) : Option String :=
  match binding, body with
  | _, some (.morphism _ _ (.tracePower ..)) => some "trace_power"
  | _, some (.morphism _ _ (.charCoefficient ..)) => some "char_coefficient"
  | .spectralInvariant .., _ => some "spectral invariant"
  | .annihilates .., _ => some "annihilates"
  | .actionEntry .., _ => some "action_entry"
  | .onBranch .., _ => some "on_branch"
  | .branchDifferential .., _ => some "branch_differential"
  | .branchProjector .., _ => some "branch_projector"
  | _, _ => none

/-- Elaborate every spectral declaration, invariant and observation. -/
def elaborateSpectral (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  for entry in env.indexed do
    if let some kind := spectralDeclarationKind? entry.declaration then
      spectralProblem (spectralSpan sources entry.id) s!"the {kind} `{qualified entry.id}` is not implemented yet"
  for entry in env.primitives do
    let body := (sources.find? (·.1 == entry.id)).map (·.2.2)
    if let some spelling := spectralBindingSpelling? entry.binding body then
      spectralProblem (spectralSpan sources entry.id)
        s!"the `{spelling}` declaration `{qualified entry.id}` is not implemented yet"
  pure env

end VastitasKernel.Indexed.Source
