import VastitasKernel.AlgebraDeclarations

set_option autoImplicit false

/-! Checked gluing data of the finite Stage 7 profile (#878).

Every check here is exact polynomial arithmetic over presented rings, inside
the shared work budget of `AlgebraBasis`. The checks read only the stored
data of the objects they name, so elaboration and the declaration audit run
the same actions.

- A **transition** between two principal opens `U₁ = D(f₁) ⊂ X₁` and
  `U₂ = D(f₂) ⊂ X₂` is a pair of maps given by images: `forward` gives the
  coordinates of `U₂` in the ring of `U₁`, `backward` the coordinates of `U₁`
  in the ring of `U₂`. Both respect the relations, and they compose to the
  identity both ways. Over a base, `forward` also commutes with the structure
  maps of both opens to it.
- A **cover** of `X` by principal opens `D(fᵢ)` is certified by coefficients
  `aᵢ` with `Σ aᵢ fᵢ − 1` in the ideal of `X`.
- A **separation witness** of a gluing is a polynomial `w` in the
  coordinates of `X₁` and then `X₂` whose image under
  `O(X₁) ⊗ O(X₂) → O(U₁)` (the inclusion and the transition) is the inverse
  coordinate `u = 1/f₁` of `U₁`. Then that ring map is onto, which is the
  criterion for a scheme glued from two affine charts to be separated, and in
  the smooth site it makes the graph of the transition closed.
- A **projective chart** identifies a chart with a standard chart `D₊(s)` or
  `D₊(t)` of the projective line over a base with no coordinates. -/
namespace VastitasKernel.GluingDeclarations

open AlgebraRuntime AlgebraBasis AlgebraDeclarations

/-- One chart of a projective claim `proj(P)[s, t] chart(X, c, p) inverse(…)`:
the chart is the standard chart where the homogeneous coordinate number
`dehomogenized` (0 for the first, 1 for the second) is a unit, `image` is the
other homogeneous coordinate divided by it, in the coordinates of the chart,
and `inverse` gives each coordinate of the chart in the one coordinate of the
standard chart. -/
structure ProjectiveChart where
  chart : Namespace.Owner
  dehomogenized : Nat
  image : Poly
  inverse : List Poly
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- The presentation of a smooth object `Affine(n)[c₁, …, cₙ]`: its
coordinates and no relations. -/
def freeData (coordinates : List String) : AffineData :=
  { generators := coordinates, construction := .presented [], base := none, bindings := [],
    structureImages := [], basis := [], cofactors := [] }

/-- The element `f` of a principal open `D(f)`, with its object. -/
def localization? (data : AffineData) : Option (Namespace.Owner × Poly) :=
  match data.construction with
  | .localization object element _ _ => some (object, element)
  | _ => none

/-- Images are canonical polynomials in `arity` coordinates. -/
def canonicalImages (arity : Nat) (images : List Poly) : Bool := images.all (Poly.canonical arity)

/-- `after ∘ before` is the identity of `before`'s source. -/
def checkIdentity (after before : Map) (error : Error) : Work Unit := do
  let composite ← compose after before
  ensure (composite.images == (Map.identity before.arity before.basis).images) error

/-- A transition `forward : U₁ → U₂` with inverse `backward : U₂ → U₁`:
images of the right length in normal form, relations respected both ways,
and both composites the identity. -/
def checkTransition (u₁ u₂ : AffineData) (forward backward : List Poly) : Work Unit := do
  ensure (forward.length == u₂.arity && backward.length == u₁.arity &&
      canonicalImages u₁.arity forward && canonicalImages u₂.arity backward)
    (.coordinate "a transition gives each coordinate of the other open exactly one image")
  checkNormal u₁.basis forward
  checkNormal u₂.basis backward
  checkRelations u₁ u₂ forward
  checkRelations u₂ u₁ backward
  let there : Map := ⟨u₁.arity, u₁.basis, forward⟩
  let back : Map := ⟨u₂.arity, u₂.basis, backward⟩
  checkIdentity back there (.relation "the transition and its inverse are not mutually inverse")
  checkIdentity there back (.relation "the transition and its inverse are not mutually inverse")

/-- The transition commutes with the structure maps of both opens to their
common base: `sx` are the structure images of `U₁`, `sy` those of `U₂`. -/
def checkOverBase (u₁ : AffineData) (sx sy forward : List Poly) : Work Unit :=
  checkTriangle u₁ sx sy forward

/-- `Σ aᵢ fᵢ = 1` in the ring of `x`. -/
def checkCover (x : AffineData) (elements coefficients : List Poly) : Work Unit := do
  ensure (elements.length == coefficients.length && !elements.isEmpty)
    (.coordinate "a cover gives one coefficient for each open")
  ensure (canonicalImages x.arity coefficients)
    (.coordinate "a coefficient of a cover is not a polynomial in the coordinates of its object")
  let sum ← (elements.zip coefficients).foldlM (fun total (element, coefficient) => do
    add total (← mul coefficient element)) []
  checkMember x.basis (← add sum (Poly.neg (Poly.one x.arity)))
    (.relation "the coefficients of the cover do not combine the opens to 1")

/-- The images in the ring of `U₁ = D(f₁) ⊂ X₁` of the coordinates of `X₁`
and then of `X₂`: the inclusion, and the first `arity₂` images of the
transition. -/
def tensorImages (u₁ : AffineData) (arity₁ arity₂ : Nat) (forward : List Poly) : List Poly :=
  (List.range arity₁).map (Poly.var u₁.arity) ++ forward.take arity₂

/-- The separation witness `w` maps to the inverse coordinate of `U₁`, the
last coordinate of its presentation. -/
def checkSeparation (u₁ : AffineData) (arity₁ arity₂ : Nat) (forward : List Poly) (witness : Poly) :
    Work Unit := do
  ensure (u₁.arity == arity₁ + 1 && forward.length == arity₂ + 1)
    (.base "a separation witness needs two principal opens of the charts")
  ensure (Poly.canonical (arity₁ + arity₂) witness)
    (.coordinate "a separation witness is a polynomial in the coordinates of the two charts")
  let image ← reduce u₁.basis (← substitute u₁.arity (tensorImages u₁ arity₁ arity₂ forward) witness)
  let inverse ← reduce u₁.basis (Poly.var u₁.arity arity₁)
  ensure (image == inverse)
    (.relation "the witness does not give the inverse coordinate of the first open on the overlap")

/-- The homogeneous coordinates `(s, t)` of a chart, in its own coordinates. -/
def homogeneous (arity : Nat) (chart : ProjectiveChart) : Poly × Poly :=
  if chart.dehomogenized == 0 then (Poly.one arity, chart.image) else (chart.image, Poly.one arity)

/-- One chart of a projective claim. The chart `x` maps isomorphically onto
its standard chart `Spec B[z]` by `z ↦ image`, with `inverse` the images of
its coordinates in `z`, and its open `D(element)` is the preimage of the
other standard chart: `element` and `image` have one normal form. -/
def checkProjectiveChart (x : AffineData) (element : Poly) (chart : ProjectiveChart) : Work Unit := do
  ensure (chart.dehomogenized < 2) (.coordinate "a chart is the standard chart of one of the two coordinates")
  ensure (Poly.canonical x.arity chart.image && chart.inverse.length == x.arity &&
      canonicalImages 1 chart.inverse)
    (.coordinate "a projective chart gives one image and one inverse image for each coordinate of the chart")
  -- The standard chart `Spec B[z]` over a base without coordinates.
  let standard : AffineData := freeData ["z"]
  let image ← reduce x.basis chart.image
  checkRelations standard x chart.inverse
  let toStandard : Map := ⟨x.arity, x.basis, [image]⟩
  let fromStandard : Map := ⟨1, [], chart.inverse⟩
  checkIdentity fromStandard toStandard
    (.relation "the chart map and its inverse are not mutually inverse on the chart")
  checkIdentity toStandard fromStandard
    (.relation "the chart map and its inverse are not mutually inverse on the standard chart")
  ensure (image == (← reduce x.basis element))
    (.base "the open of the chart is not the preimage of the other standard chart")

/-- The homogeneous coordinates of the two charts agree on `U₁`:
`s₁ · φ#(t₂) − t₁ · φ#(s₂) = 0` in the ring of `U₁`. -/
def checkProjectiveOverlap (u₁ : AffineData) (arity₁ arity₂ : Nat) (forward : List Poly)
    (first second : ProjectiveChart) : Work Unit := do
  ensure (first.dehomogenized != second.dehomogenized)
    (.base "the two charts must be the standard charts of different coordinates")
  let (s₁, t₁) := homogeneous arity₁ first
  let (s₂, t₂) := homogeneous arity₂ second
  let inclusion := (List.range arity₁).map (Poly.var u₁.arity)
  let transition := forward.take arity₂
  let left ← mul (← substitute u₁.arity inclusion s₁) (← substitute u₁.arity transition t₂)
  let right ← mul (← substitute u₁.arity inclusion t₁) (← substitute u₁.arity transition s₂)
  checkMember u₁.basis (← add left (Poly.neg right))
    (.relation "the homogeneous coordinates of the two charts disagree on the overlap")

end VastitasKernel.GluingDeclarations
