import VastitasKernel.IndexedPrimitiveBinding
import VastitasKernel.SpectralRuntime

set_option autoImplicit false

/-! The validity contracts of the spectral bindings (Stage 5, #806), next to
the bindings as `IndexedFrameContracts` holds those of the frame bindings: the
checks that the entries of `IndexedSpectralRegistry` name.

The bindings that read an endomorphism, a spectrum or a branch embed it as an
`EndoRef`, a `SpectrumRef` or a `BranchRef`. The contracts require every
embedded copy to equal its declaration exactly (`endoDeclared`,
`spectrumDeclared`, `branchDeclared`), and the copy that a spectrum or a
branch embeds to be the declaration that it names: a forged row, `symmetric`
claim, characteristic polynomial, adjugate, localization, witness or
exponent, or a stale reference to another declaration, fails the declaration
audit. The declaration audit checks each spectral declaration once
(`SpectralDeclarations.checkEndomorphism`, `checkSpectrum`, `checkBranch`);
the contracts do not repeat its certificate checks.

A spectral invariant is a declared smooth map `X → Line`
(`smoothConstantValid`) whose one image the contract recomputes from the
embedded declaration: `tr(Hᵏ)` by the budgeted products of
`SpectralDeclarations.tracePowerImage`, or the coefficient of `tⁱ` of `χ`
(`charCoefficientImage`). A forged image, power or index fails the binding.

The observations take a point of the object of their spectrum or branch in a
smooth family, and the branch observations a value in a 1-dimensional object
`line` of the same family; `branch_differential` returns a covector of a
cotangent family over that object. An element of `A[t]` is a canonical
polynomial in the object's coordinates and the fiber coordinate, last; a row
and a column are indices below the rank of the module. No contract consults a
metric declaration, a frame, a base chain or a descriptor capability. -/
namespace VastitasKernel.Indexed

/-! ## Embedded declarations -/

/-- The embedded endomorphism is its declaration: `endo.endomorphism` is an
endomorphism declaration on `endo.object` of the free module `endo.module`
with exactly the embedded rows and `symmetric` claim. -/
def endoDeclared (env : Environment) (endo : EndoRef) : Bool :=
  match endomorphismData? env endo.endomorphism with
  | some (_, object, module, rows, symmetric) =>
    object == endo.object && module == endo.module && rows == endo.rows && symmetric == endo.symmetric
  | none => false

/-- The embedded spectrum is its declaration: `spectrum.spectrum` is a
spectrum declaration on the object of its endomorphism, of exactly the
embedded endomorphism, whose certificate has exactly the embedded `χ` and
adjugate, and the embedded endomorphism is its declaration. -/
def spectrumDeclared (env : Environment) (spectrum : SpectrumRef) : Bool :=
  match spectrumData? env spectrum.spectrum with
  | some (_, object, endomorphism, _, certificate) =>
    object == spectrum.endomorphism.object && endomorphism == spectrum.endomorphism.endomorphism &&
      certificate.characteristic == spectrum.characteristic && certificate.adjugate == spectrum.adjugate &&
      endoDeclared env spectrum.endomorphism
  | none => false

/-- The embedded branch is its declaration: `branch.branch` is a branch
declaration on the object of its spectrum, of exactly the embedded spectrum,
with exactly the embedded localization, witness and exponent, and the
embedded spectrum is its declaration. -/
def branchDeclared (env : Environment) (branch : BranchRef) : Bool :=
  match branchData? env branch.branch with
  | some (_, object, spectrum, localize, witness, exponent, _) =>
    object == branch.spectrum.endomorphism.object && spectrum == branch.spectrum.spectrum &&
      localize == branch.localize && witness == branch.witness && exponent == branch.exponent &&
      spectrumDeclared env branch.spectrum
  | none => false

/-- The object of the embedded endomorphism of a spectrum. -/
def SpectrumRef.object (spectrum : SpectrumRef) : DeclId := spectrum.endomorphism.object

/-- The object of the embedded endomorphism of the spectrum of a branch. -/
def BranchRef.object (branch : BranchRef) : DeclId := branch.spectrum.object

/-- The rank of the embedded endomorphism of a spectrum: its number of rows. -/
def SpectrumRef.rank (spectrum : SpectrumRef) : Nat := spectrum.endomorphism.rows.length

/-! ## Spectral invariants -/

/-- The object that a spectral invariant reads: the endomorphism's or the
spectrum's. -/
def SpectralInvariant.object : SpectralInvariant → DeclId
  | .tracePower endomorphism _ => endomorphism.object
  | .charCoefficient spectrum _ => spectrum.object

/-- The embedded declaration of a spectral invariant is its declaration. -/
def SpectralInvariant.declared (env : Environment) : SpectralInvariant → Bool
  | .tracePower endomorphism _ => endoDeclared env endomorphism
  | .charCoefficient spectrum _ => spectrumDeclared env spectrum

/-- The image that a spectral invariant over `arity` coordinates computes:
`tr(Hᵏ)` of the embedded rows, or the coefficient of `tⁱ` in the embedded
`χ`, or `none` when the power, the index, the rank or the algebra budget
rejects it. -/
def SpectralInvariant.image? (arity : Nat) : SpectralInvariant → Option AlgebraRuntime.Poly
  | .tracePower endomorphism power =>
    (SpectralDeclarations.tracePowerImage arity endomorphism.rows power).toOption
  | .charCoefficient spectrum index =>
    (SpectralDeclarations.charCoefficientImage spectrum.rank spectrum.characteristic index).toOption

/-- The source object of a smooth family application `Smooth<X, Y>`. -/
def smoothSource? (application : Application) : Option DeclId :=
  match application.indices with
  | [.object (.global source), _] => some source
  | _ => none

/-- `trace_power(H, k)` or `char_coefficient(S, i)` as the smooth map `map`
of type `application`: a declared smooth map `X → Line` on the object of
the embedded declaration, which is its declaration, whose one image is the
invariant that the contract recomputes. -/
def spectralInvariantValid (env : Environment) (application : Application) (map : AlgebraRuntime.Map)
    (invariant : SpectralInvariant) : Bool :=
  smoothConstantValid env application map && smoothSource? application == some invariant.object &&
    invariant.declared env &&
    match invariant.image? map.arity with
    | some image => map.images == [image]
    | none => false

/-! ## Observations -/

/-- An element of `A[t]` for a spectrum: a canonical polynomial of arity
`m + 1` over the `m` coordinates of the spectrum's object and the fiber
coordinate, last. -/
def spectralElementValid (env : Environment) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) : Bool :=
  match smoothDimension? env spectrum.object with
  | some m => AlgebraRuntime.Poly.canonical (m + 1) element
  | none => false

/-- `annihilates(S, spectrum = Σ, element = f)`: whether `f(H(p)) = 0` for a
point `p` in the smooth family `S` of the object of `Σ`. -/
def annihilatesValid (env : Environment) (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) :
    Bool :=
  isSmoothFamily env smooth && spectrumDeclared env spectrum && spectralElementValid env spectrum element

/-- `action_entry(S, spectrum = Σ, element = f, eᵢ, eⱼ)`: an entry of `f(H(p))`,
in a row and a column below the rank of the module. -/
def actionEntryValid (env : Environment) (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly)
    (row column : Nat) : Bool :=
  annihilatesValid env smooth spectrum element && decide (row < spectrum.rank) && decide (column < spectrum.rank)

/-- `on_branch(S, L, branch = B)`: whether a point `p` and a value `t` in the
smooth family `S`, `t` into the 1-dimensional object `L`, lie on `B`. -/
def onBranchValid (env : Environment) (smooth line : DeclId) (branch : BranchRef) : Bool :=
  isSmoothFamily env smooth && smoothDimension? env line == some 1 && branchDeclared env branch

/-- `branch_differential(S, C, L, branch = B)`: the differential of the
eigenvalue of `B` at a point, a covector of the cotangent family `C` over the
branch's object. -/
def branchDifferentialValid (env : Environment) (smooth cotangent line : DeclId) (branch : BranchRef) : Bool :=
  isSmoothFamily env smooth && fiberVariance? env cotangent == some .cotangent &&
    smoothDimension? env line == some 1 && branchDeclared env branch &&
    validApplication env ⟨cotangent, [.object (.global branch.object)]⟩

/-- `branch_projector(S, L, branch = B, eᵢ, eⱼ)`: an entry of the
eigenprojector of `B`, in a row and a column below the rank of the module. -/
def branchProjectorValid (env : Environment) (smooth line : DeclId) (branch : BranchRef) (row column : Nat) :
    Bool :=
  onBranchValid env smooth line branch && decide (row < branch.spectrum.rank) &&
    decide (column < branch.spectrum.rank)

end VastitasKernel.Indexed
