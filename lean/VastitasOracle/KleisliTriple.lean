import VastitasOracle.Kleisli

/-! Kleisli triples on an explicit category. Both directions preserve the
object action and the typed operations, including the chosen multiplication. -/
namespace VastitasOracle.Kleisli

universe u v
variable {Obj : Type u} {Hom : Obj → Obj → Type v}

structure Triple (Obj : Type u) (Hom : Obj → Obj → Type v) where
  id : (x : Obj) → Hom x x
  comp : {x y z : Obj} → Hom y z → Hom x y → Hom x z
  T : Obj → Obj
  eta : (x : Obj) → Hom x (T x)
  extend : {x y : Obj} → Hom x (T y) → Hom (T x) (T y)

namespace Triple

structure Laws (k : Triple Obj Hom) : Prop where
  id_comp : ∀ {x y} (f : Hom x y), k.comp (k.id y) f = f
  comp_id : ∀ {x y} (f : Hom x y), k.comp f (k.id x) = f
  assoc : ∀ {w x y z} (h : Hom y z) (g : Hom x y) (f : Hom w x),
    k.comp (k.comp h g) f = k.comp h (k.comp g f)
  extend_eta : ∀ x, k.extend (k.eta x) = k.id (k.T x)
  extend_comp_eta : ∀ {x y} (f : Hom x (k.T y)), k.comp (k.extend f) (k.eta x) = f
  extend_comp : ∀ {x y z} (g : Hom y (k.T z)) (f : Hom x (k.T y)),
    k.extend (k.comp (k.extend g) f) = k.comp (k.extend g) (k.extend f)

def fromMonad (d : Data Obj Hom) : Triple Obj Hom :=
  ⟨d.id,d.comp,d.T,d.eta,Kleisli.extend d⟩

theorem fromMonad_lawful (d : Data Obj Hom) (h : Kleisli.Laws d) : Laws (fromMonad d) :=
  ⟨h.id_comp,h.comp_id,h.assoc,h.mu_map_eta,Kleisli.unit_bind d h,
   fun g f => Kleisli.extend_bind d h f g⟩

variable (k : Triple Obj Hom)

def action {x y} (f : Hom x y) : Hom (k.T x) (k.T y) := k.extend (k.comp (k.eta y) f)

def multiplication (x : Obj) : Hom (k.T (k.T x)) (k.T x) := k.extend (k.id (k.T x))

def toMonad : Data Obj Hom := ⟨k.id,k.comp,k.T,k.action,k.eta,k.multiplication⟩

variable (h : Laws k)
include h

private theorem extend_after_action {x y z} (g : Hom y (k.T z)) (f : Hom x y) :
    k.comp (k.extend g) (k.action f) = k.extend (k.comp g f) := by
  unfold action
  rw [← h.extend_comp, ← h.assoc, h.extend_comp_eta]

theorem recover_extension {x y} (f : Hom x (k.T y)) : Kleisli.extend k.toMonad f = k.extend f := by
  change k.comp (k.extend (k.id (k.T y))) (k.action f) = k.extend f
  rw [extend_after_action k h, h.id_comp]

private theorem extend_after_multiplication {x y} (g : Hom x (k.T y)) :
    k.comp (k.extend g) (k.multiplication x) = k.extend (k.extend g) := by
  unfold multiplication
  rw [← h.extend_comp, h.comp_id]

theorem toMonad_lawful : Kleisli.Laws k.toMonad := by
  constructor <;> dsimp only [toMonad]
  · exact h.id_comp
  · exact h.comp_id
  · exact h.assoc
  · intro x
    simp only [action, h.comp_id, h.extend_eta]
  · intro x y z g f
    change k.extend (k.comp (k.eta z) (k.comp g f)) = k.comp (k.extend (k.comp (k.eta z) g)) (k.action f)
    rw [extend_after_action k h, h.assoc]
  · intro x y f
    exact h.extend_comp_eta _
  · intro x y f
    calc k.comp (k.action f) (k.multiplication x) = k.extend (k.action f) :=
           extend_after_multiplication k h (k.comp (k.eta y) f)
         _ = k.comp (k.multiplication y) (k.action (k.action f)) := (recover_extension k h _).symm
  · intro x
    exact h.extend_comp_eta _
  · intro x
    exact (recover_extension k h (k.eta x)).trans (h.extend_eta x)
  · intro x
    calc k.comp (k.multiplication x) (k.multiplication (k.T x)) = k.extend (k.multiplication x) :=
           extend_after_multiplication k h (k.id (k.T x))
         _ = k.comp (k.multiplication x) (k.action (k.multiplication x)) := (recover_extension k h _).symm

theorem triple_roundtrip : fromMonad k.toMonad = k := by
  have e : @Kleisli.extend Obj Hom k.toMonad = @k.extend := by funext x y f; exact recover_extension k h f
  cases k
  unfold fromMonad
  rw [e]
  rfl

omit h
variable (d : Data Obj Hom) (laws : Kleisli.Laws d)
include laws

theorem recover_action {x y} (f : Hom x y) : (fromMonad d).action f = d.map f := by
  change d.comp (d.mu y) (d.map (d.comp (d.eta y) f)) = d.map f
  rw [laws.map_comp, ← laws.assoc, laws.mu_map_eta, laws.id_comp]

theorem recover_multiplication (x : Obj) : (fromMonad d).multiplication x = d.mu x := by
  change d.comp (d.mu x) (d.map (d.id (d.T x))) = d.mu x
  rw [laws.map_id, laws.comp_id]

/-- Reconstructing the Monad from its triple recovers the original data,
including action on every arrow and multiplication at every object. -/
theorem monad_roundtrip : (fromMonad d).toMonad = d := by
  have a : @(fromMonad d).action = @d.map := by funext x y f; exact recover_action d laws f
  have m : (fromMonad d).multiplication = d.mu := by funext x; exact recover_multiplication d laws x
  cases d
  unfold toMonad
  rw [a,m]
  rfl

end Triple
end VastitasOracle.Kleisli
