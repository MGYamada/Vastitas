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

/-- How a presented object is constructed. -/
inductive Construction where
  | presented (relations : List Poly)
  /-- `left ×_B right` over `B = base left`. Without `via`, both factors have the
  declared base `B`. With `via = (forward, inverse)`, `right` has a separately
  declared base `B'`; `forward` gives `B`'s coordinates in `B'`'s ring and
  `inverse` gives `B'`'s coordinates in `B`'s ring, a checked isomorphism.
  `relations` are the derived relations, re-derived by the audit. -/
  | fiber (left right : Namespace.Owner) (via : Option (List Poly × List Poly)) (relations : List Poly)
  /-- The principal open `D(f) = Spec A[u]/(u·f − 1)` of `object`, over `object`.
  `inverse` names the new coordinate `u`. -/
  | localization (object : Namespace.Owner) (element : Poly) (inverse : String) (relations : List Poly)
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
  | .presented relations | .fiber _ _ _ relations | .localization _ _ _ relations => relations

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
  checkMember data.basis (← substitute data.arity data.structureImages g)
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

/-! ## Fiber products -/

/-- Embed a polynomial of some arity into `total` coordinates at `offset`. Zero
padding preserves the degLex order, so canonical polynomials stay canonical. -/
def embed (offset total : Nat) (p : Poly) : Poly :=
  p.map fun t => ⟨List.replicate offset 0 ++ t.monomial ++
    List.replicate (total - offset - t.monomial.length) 0, t.coefficient⟩

/-- The qualifier of each factor occurrence: the factor's name, or `first` and
`second` when both factors have the same name (a self-product, or same-named
declarations in different modules). Declaration names are single identifiers,
so distinct qualifiers never produce colliding coordinates. -/
def fiberQualifiers (left right : Namespace.Owner) : String × String :=
  if left.name == right.name then ("first", "second") else (left.name, right.name)

def qualify (qualifier : String) (generators : List String) : List String :=
  generators.map (s!"{qualifier}::" ++ ·)

/-- The derived presentation of `left ×_B right`: qualified coordinates, both
bases embedded, the equalizer of both structure maps, and the left structure map. -/
structure FiberPresentation where
  generators : List String
  relations : List Poly
  base : Option Namespace.Owner
  bindings : List (String × Poly)
  deriving Repr, DecidableEq, BEq

def fiberPresentation (left right : Namespace.Owner) (l r b : AffineData) (rightImages : List Poly) :
    FiberPresentation :=
  let total := l.arity + r.arity
  let cross := (l.structureImages.zip rightImages).map fun (a, c) =>
    Poly.sub (embed 0 total a) (embed l.arity total c)
  { generators := qualify (fiberQualifiers left right).1 l.generators ++
      qualify (fiberQualifiers left right).2 r.generators
    relations := l.basis.map (embed 0 total) ++ r.basis.map (embed l.arity total) ++ cross
    base := l.base
    bindings := b.generators.zip (l.structureImages.map (embed 0 total)) }

/-- Morphism images are normal forms in the source ring. -/
def checkNormal (basis : List Poly) (images : List Poly) : Work Unit :=
  images.forM fun image => do
    ensure ((← reduce basis image) == image) (.coordinate "a morphism image is not a normal form")

/-- A pullback map `Y → X` sends every basis element of `Y` into `X`'s ideal. -/
def checkRelations (dx dy : AffineData) (images : List Poly) : Work Unit :=
  dy.basis.forM fun g => do
    checkMember dx.basis (← substitute dx.arity images g)
      (.relation "the map does not respect the target's relations")

/-- A pullback map commutes with the structure maps `sx` and `sy` to the base. -/
def checkTriangle (dx : AffineData) (sx sy images : List Poly) : Work Unit := do
  let pulled ← sy.mapM fun image => do reduce dx.basis (← substitute dx.arity images image)
  ensure (sx == pulled) (.base "the morphism does not commute with the structure maps to the base")

/-- The right factor's structure map to the left factor's base: its own
structure images, or those composed with the chosen base isomorphism. -/
def fiberImages (r : AffineData) (via : Option (List Poly × List Poly)) : Work (List Poly) :=
  match via with
  | none => pure r.structureImages
  | some (forward, _) => forward.mapM (substitute r.arity r.structureImages)

/-- A checked isomorphism between two declared base rings: images that respect
relations both ways and compose to the identity both ways. -/
def checkIso (b b' : AffineData) (forward inverse : List Poly) : Work Unit := do
  ensure (forward.length == b.arity && inverse.length == b'.arity &&
      forward.all (Poly.canonical b'.arity) && inverse.all (Poly.canonical b.arity))
    (.base "a base isomorphism gives each coordinate exactly one image")
  b.basis.forM fun g => do
    checkMember b'.basis (← substitute b'.arity forward g)
      (.relation "the base isomorphism does not respect the relations")
  b'.basis.forM fun g => do
    checkMember b.basis (← substitute b.arity inverse g)
      (.relation "the inverse base isomorphism does not respect the relations")
  let there ← compose ⟨b.arity, b.basis, inverse⟩ ⟨b'.arity, b'.basis, forward⟩
  let back ← compose ⟨b'.arity, b'.basis, forward⟩ ⟨b.arity, b.basis, inverse⟩
  ensure (there.images == (Map.identity b'.arity b'.basis).images &&
      back.images == (Map.identity b.arity b.basis).images)
    (.relation "the base maps are not mutually inverse")

/-- The derived presentation of a principal open `D(f) ⊂ X`: `X`'s coordinates and
the inverse `u`, `X`'s basis and `u·f − 1`, over `X` by the inclusion. -/
def localizationPresentation (owner : Namespace.Owner) (x : AffineData) (element : Poly) (inverse : String) :
    FiberPresentation :=
  let total := x.arity + 1
  { generators := x.generators ++ [inverse]
    relations := x.basis.map (embed 0 total) ++
      [Poly.sub (Poly.mul (Poly.var total x.arity) (embed 0 total element)) (Poly.one total)]
    base := some owner
    bindings := x.generators.zip ((List.range x.arity).map (Poly.var total)) }

/-- Re-derive a constructed object's presentation from the stored data of the
declarations it is built from. -/
def checkConstruction (data : AffineData) (resolve : Namespace.Owner → Option AffineData) : Work Unit := do
  match data.construction with
  | .presented _ => pure ()
  | .fiber left right via relations =>
    let some l := resolve left | throw (.base "a fiber factor is not a presented affine object")
    let some r := resolve right | throw (.base "a fiber factor is not a presented affine object")
    let some baseRef := l.base | throw (.base "the left fiber factor has no declared base")
    let some b := resolve baseRef | throw (.base "the fiber base is not a presented affine object")
    match via with
    | none =>
      ensure (r.base == some baseRef)
        (.base "the fiber factors have different declared bases and no chosen isomorphism")
    | some (forward, inverse) =>
      let some baseRef' := r.base | throw (.base "the right fiber factor has no declared base")
      let some b' := resolve baseRef' | throw (.base "the right fiber base is not a presented affine object")
      checkIso b b' forward inverse
    let expected := fiberPresentation left right l r b (← fiberImages r via)
    ensure (data.generators == expected.generators && relations == expected.relations &&
        data.base == expected.base && data.bindings == expected.bindings)
      (.base "the stored fiber presentation is not derived from its factors")
  | .localization object element inverse relations =>
    let some x := resolve object | throw (.base "a principal open needs a presented affine object")
    ensure (Poly.canonical x.arity element) (.coordinate "the localized element is not a polynomial in the object's coordinates")
    let expected := localizationPresentation object x element inverse
    ensure (data.generators == expected.generators && relations == expected.relations &&
        data.base == expected.base && data.bindings == expected.bindings)
      (.base "the stored principal open is not derived from its object")

def validConstruction (data : AffineData) (resolve : Namespace.Owner → Option AffineData) : Bool :=
  (run (checkConstruction data resolve)).isOk

/-- Elaborate declared data: compute the basis, cofactors and ordered
structure images. The result must still pass `checkAffine`. -/
def elaborate (generators : List String) (relations : List Poly) (baseRef : Option Namespace.Owner)
    (bindings : List (String × Poly)) (base : Option AffineData)
    (construction : Construction := .presented relations) : Except Error AffineData := run do
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
    generators, construction, base := baseRef, bindings,
    structureImages, basis := certificate.basis, cofactors := certificate.cofactors }
  checkAffine data base
  pure data

end VastitasKernel.AlgebraDeclarations
