import VastitasOracle.AffineDeclarations
import VastitasKernel.IndexedContractAudit

/-! Structural soundness of morphisms over a base (Stage 2).

An accepted declared morphism `X → Y` over `S`, a `relativeConstant`
binding, establishes:

- its map lives in `X`'s ring with `X`'s stored basis;
- it gives normal-form images of exactly `Y`'s coordinates;
- it sends every basis element of `Y` into `X`'s ideal, with exact quotient
  identities;
- it commutes with the stored structure maps of `X` and `Y` to `S`.

Composition substitutes in the written order, so `compose after before` is
`X → Z` with pullback `after ∘ before`. A view to another base requires that
base on the declared chain. These are statements about kernel `Poly`
operations. Their meaning as ring maps and `Spec.map` is proved in the
mathlib bridge. -/
namespace VastitasOracle.AffineMorphisms

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.AlgebraBasis VastitasKernel.AlgebraDeclarations
open VastitasOracle.AlgebraBasis VastitasOracle.AffineDeclarations

/-- The exact facts recorded by an accepted morphism over a base. -/
structure MorphismValid (env : Environment) (application : Application) (map : Map) : Prop where
  family : familyRepresentation env application.family = some .relative
  valid : application.Valid env
  objects : ∃ x y s dx dy sx sy,
    application.indices = [Index.object (.global x), Index.object (.global y), Index.object (.global s)] ∧
    affineData? env x = some dx ∧ affineData? env y = some dy ∧
    structureImages? env x s = some sx ∧ structureImages? env y s = some sy ∧
    map.arity = dx.arity ∧ map.basis = dx.basis ∧ map.images.length = dy.arity ∧
    (∀ image ∈ map.images, Poly.canonical dx.arity image = true ∧ normalForm dx.basis image = image) ∧
    (∀ g ∈ dy.basis, ∃ quotients, combination quotients dx.basis = Poly.subst dx.arity map.images g) ∧
    sx = sy.map (fun image => normalForm dx.basis (Poly.subst dx.arity map.images image))

theorem run_isOk {action : Work Unit} (h : (run action).isOk = true) :
    ∃ s', action.run 0 = .ok ((), s') := by
  unfold run at h
  cases result : action.run 0 with
  | error e => simp [result, Except.map, Except.isOk, Except.toBool] at h
  | ok pair => exact ⟨pair.2, by simp⟩

theorem checkNormal_ok {basis images : List Poly} {s s' : Nat}
    (h : (checkNormal basis images).run s = .ok ((), s')) :
    ∀ image ∈ images, normalForm basis image = image := by
  intro image member
  obtain ⟨_, _, hi⟩ := forM_ok h image member
  obtain ⟨q, _, hq, hi⟩ := bind_ok hi
  have same := ensure_ok hi
  simp only [beq_iff_eq] at same
  rw [← reduce_ok hq]
  exact same

theorem checkRelations_ok {dx dy : AffineData} {images : List Poly} {s s' : Nat}
    (h : (checkRelations dx dy images).run s = .ok ((), s')) :
    ∀ g ∈ dy.basis, ∃ quotients, combination quotients dx.basis = Poly.subst dx.arity images g := by
  intro g member
  obtain ⟨_, _, hg⟩ := forM_ok h g member
  obtain ⟨q, _, hq, hg⟩ := bind_ok hg
  rw [← substitute_ok hq]
  exact checkMember_ok hg

theorem checkTriangle_ok {dx : AffineData} {sx sy images : List Poly} {s s' : Nat}
    (h : (checkTriangle dx sx sy images).run s = .ok ((), s')) :
    sx = sy.map (fun image => normalForm dx.basis (Poly.subst dx.arity images image)) := by
  unfold checkTriangle at h
  obtain ⟨pulled, _, hpulled, h⟩ := bind_ok h
  have same := ensure_ok h
  simp only [beq_iff_eq] at same
  rw [same]
  refine mapM_ok (fun image _ s s' r hr => ?_) hpulled
  obtain ⟨q, _, hq, hr⟩ := bind_ok hr
  rw [reduce_ok hr, substitute_ok hq]

theorem relativeConstant_sound {env : Environment} {application : Application} {map : Map}
    (h : relativeConstantValid env application map = true) : MorphismValid env application map := by
  unfold relativeConstantValid at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨relative, valid⟩, h⟩ := h
  refine ⟨by simpa [isRelativeFamily] using relative, (Audit.validApplication_iff _ _).mp valid, ?_⟩
  split at h
  · rename_i x y s indices
    split at h
    · rename_i dx dy sx sy hx hy hsx hsy
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨⟨arity, basis⟩, length⟩, canonical⟩, checks⟩ := h
      obtain ⟨_, ran⟩ := run_isOk checks
      unfold checkMorphism at ran
      obtain ⟨_, _, hnormal, ran⟩ := bind_ok ran
      obtain ⟨_, _, hrelations, htriangle⟩ := bind_ok ran
      refine ⟨x, y, s, dx, dy, sx, sy, indices, hx, hy, hsx, hsy, arity, basis, length,
        fun image member => ⟨canonical image member, checkNormal_ok hnormal image member⟩,
        checkRelations_ok hrelations, checkTriangle_ok htriangle⟩
    · simp at h
  · simp at h

/-- Pullback composition substitutes `before`'s images into `after`'s: the
written order, never the reverse. -/
theorem compose_images (after before : Map) :
    (Map.compose after before).images =
      after.images.map (fun image => normalForm before.basis (Poly.subst before.arity before.images image)) ∧
    (Map.compose after before).arity = before.arity ∧ (Map.compose after before).basis = before.basis :=
  ⟨rfl, rfl, rfl⟩

/-- A base view is admitted only to a base on the declared chain. -/
theorem view_requires_chain {env : Environment} {family source target : DeclId}
    (valid : (PrimitiveBinding.relativeView family source target).Valid env) :
    onChain env source target = true := valid.2

/-- Morphism equality compares exact normal-form images. -/
theorem same_iff (left right : Map) : Map.same left right = true ↔ left.images = right.images := by
  simp [Map.same]

end VastitasOracle.AffineMorphisms
