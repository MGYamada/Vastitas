import VastitasKernel.AlgebraBasis
import VastitasKernel.Identity

/-! Checked data of a presented affine object in the finite Stage 2 profile.

A declared object `N = spec[g₁, …, gₙ] relations(r₁, …) over B by(b ↦ pᵦ, …)`
stands for the presented QQ-algebra `QQ[g₁, …, gₙ]/(r₁, …)`. Its optional base
`B` is another declared object, and the bindings give the images of `B`'s
coordinates in `N`'s ring. Each declaration is one canonical object:
separately declared presentations stay distinct, and become comparable only
through checked isomorphisms.

`AffineData` stores the declared data together with the elaborated reduced
basis, its cofactors and the ordered structure images. `checkAffine` verifies
the stored data against the base's data. It does not trust the elaboration
that produced it. -/
namespace VastitasKernel.AlgebraDeclarations

open AlgebraRuntime AlgebraBasis

/-- The exact coefficient fields of presented objects. -/
inductive ExactField where
  | rational
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- How a presented object is constructed. Fiber products and localizations
extend this inductive in later increments. -/
inductive Construction where
  | presented (relations : List Poly)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure AffineData where
  generators : List String
  construction : Construction
  base : Option Namespace.Owner
  /-- Declared images of the base's coordinates, in this object's coordinates. -/
  bindings : List (String × Poly)
  /-- Elaborated normal forms of the bindings, ordered like the base's coordinates. -/
  structureImages : List Poly
  basis : List Poly
  cofactors : List (List Poly)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace AffineData

def arity (data : AffineData) : Nat := data.generators.length

def relations (data : AffineData) : List Poly :=
  match data.construction with
  | .presented relations => relations

def certificate (data : AffineData) : Certificate :=
  ⟨data.arity, data.relations, data.basis, data.cofactors⟩

def binding? (data : AffineData) (name : String) : Option Poly :=
  (data.bindings.find? (·.1 == name)).map (·.2)

end AffineData

/-- Check that `image` lies in the ideal of `basis` by exact division. -/
def checkMember (basis : List Poly) (image : Poly) (error : Error) : Work Unit := do
  let division ← divide basis image
  let identity ← combine division.quotients basis
  ensure (division.remainder == [] && identity == image) error

/-- The stored image of one base coordinate is the normal form of its binding. -/
def checkImage (data : AffineData) (entry : String × Poly) : Work Unit := do
  match data.binding? entry.1 with
  | none => throw (.base s!"no image for base coordinate {entry.1}")
  | some declared =>
    let reduced ← divide data.basis declared
    ensure (reduced.remainder == entry.2)
      (.base s!"the stored image of base coordinate {entry.1} is not its normal form")

/-- One base basis element pulls back into this object's ideal. -/
def checkPullback (data : AffineData) (g : Poly) : Work Unit := do
  charge (cost g + 1)
  checkMember data.basis (Poly.subst data.arity data.structureImages g)
    (.base "the structure map does not respect the base relations")

/-- The structure map to a base: one binding per base coordinate, normalized
and ordered like the base, and every base basis element pulled back into the
ideal. -/
def checkStructure (data base : AffineData) : Work Unit := do
  ensure ((data.bindings.map (·.1)).length == base.arity && decide (data.bindings.map (·.1)).Nodup &&
      (data.bindings.map (·.1)).all (base.generators.contains ·))
    (.base "the structure map must give each base coordinate exactly one image")
  ensure (data.bindings.all fun (_, image) => Poly.canonical data.arity image)
    (.coordinate "a structure image is not a polynomial in this object's coordinates")
  ensure (data.structureImages.length == base.arity) (.base "structure images have the wrong length")
  (base.generators.zip data.structureImages).forM (checkImage data)
  base.basis.forM (checkPullback data)

/-- Verify one stored object against its base's stored data. -/
def checkAffine (data : AffineData) (base : Option AffineData) : Work Unit := do
  ensure (data.arity ≤ Limits.algebraGenerators) (.limit "generator")
  ensure (decide data.generators.Nodup) (.coordinate "duplicate coordinate name")
  verify data.certificate
  match data.base, base with
  | none, none =>
    ensure (data.bindings == [] && data.structureImages == [])
      (.base "an object without a base cannot have structure images")
  | some _, some base => checkStructure data base
  | some _, none => throw (.base "the declared base is not a presented affine object")
  | none, some _ => throw (.base "unexpected base data")

def validAffineData (data : AffineData) (base : Option AffineData) : Bool :=
  (run (checkAffine data base)).isOk

/-- Elaborate declared data: compute the basis, cofactors and ordered
structure images. The result must still pass `checkAffine`. -/
def elaborate (generators : List String) (relations : List Poly) (baseRef : Option Namespace.Owner)
    (bindings : List (String × Poly)) (base : Option AffineData) : Except Error AffineData := run do
  let arity := generators.length
  ensure (decide generators.Nodup) (.coordinate "duplicate coordinate name")
  let certificate ← certify arity relations
  let structureImages ← match base with
    | none => pure []
    | some base => base.generators.mapM fun name => do
      match (bindings.find? (·.1 == name)).map (·.2) with
      | some image => pure (← divide certificate.basis image).remainder
      | none => throw (.base s!"no image for base coordinate {name}")
  let data : AffineData := {
    generators, construction := .presented relations, base := baseRef, bindings,
    structureImages, basis := certificate.basis, cofactors := certificate.cofactors }
  checkAffine data base
  pure data

end VastitasKernel.AlgebraDeclarations
