import Init

/-! Kleisli composition from the category, endofunctor, unit and multiplication
of a selected monad. All arrows have explicit endpoints. The operations only
use the data; the category and monad equations are separate proof fields. -/
namespace VastitasOracle.Kleisli

universe u v
variable {Obj : Type u} {Hom : Obj → Obj → Type v}

structure Data (Obj : Type u) (Hom : Obj → Obj → Type v) where
  id : (x : Obj) → Hom x x
  comp : {x y z : Obj} → Hom y z → Hom x y → Hom x z
  T : Obj → Obj
  map : {x y : Obj} → Hom x y → Hom (T x) (T y)
  eta : (x : Obj) → Hom x (T x)
  mu : (x : Obj) → Hom (T (T x)) (T x)

structure Laws (d : Data Obj Hom) : Prop where
  id_comp : ∀ {x y} (f : Hom x y), d.comp (d.id y) f = f
  comp_id : ∀ {x y} (f : Hom x y), d.comp f (d.id x) = f
  assoc : ∀ {w x y z} (h : Hom y z) (g : Hom x y) (f : Hom w x),
    d.comp (d.comp h g) f = d.comp h (d.comp g f)
  map_id : ∀ x, d.map (d.id x) = d.id (d.T x)
  map_comp : ∀ {x y z} (g : Hom y z) (f : Hom x y), d.map (d.comp g f) = d.comp (d.map g) (d.map f)
  eta_natural : ∀ {x y} (f : Hom x y), d.comp (d.map f) (d.eta x) = d.comp (d.eta y) f
  mu_natural : ∀ {x y} (f : Hom x y), d.comp (d.map f) (d.mu x) = d.comp (d.mu y) (d.map (d.map f))
  mu_eta : ∀ x, d.comp (d.mu x) (d.eta (d.T x)) = d.id (d.T x)
  mu_map_eta : ∀ x, d.comp (d.mu x) (d.map (d.eta x)) = d.id (d.T x)
  mu_assoc : ∀ x, d.comp (d.mu x) (d.mu (d.T x)) = d.comp (d.mu x) (d.map (d.mu x))

variable (d : Data Obj Hom)

def unit (x : Obj) : Hom x (d.T x) := d.eta x

/-- Kleisli extension sends an arrow from x to T y to an arrow from T x to T y. -/
def extend {x y : Obj} (f : Hom x (d.T y)) : Hom (d.T x) (d.T y) :=
  d.comp (d.mu y) (d.map f)

def bind {s x y : Obj} (p : Hom s (d.T x)) (f : Hom x (d.T y)) : Hom s (d.T y) :=
  d.comp (extend d f) p

/-- Compose the first argument after the second. -/
def compose {x y z : Obj} (g : Hom y (d.T z)) (f : Hom x (d.T y)) : Hom x (d.T z) :=
  bind d f g

def lift {x y : Obj} (f : Hom x y) : Hom x (d.T y) := d.comp (unit d y) f

variable (laws : Laws d)
include laws

theorem bind_unit {s x} (p : Hom s (d.T x)) : bind d p (unit d x) = p := by
  simp only [bind, extend, unit, laws.mu_map_eta, laws.id_comp]

theorem unit_bind {x y} (f : Hom x (d.T y)) : bind d (unit d x) f = f := by
  unfold bind extend unit
  rw [laws.assoc, laws.eta_natural, ← laws.assoc, laws.mu_eta, laws.id_comp]

/-- The extension commutes with multiplication by naturality and the Monad associativity equation. -/
private theorem extend_mu {x y} (f : Hom x (d.T y)) :
    d.comp (extend d f) (d.mu x) = d.comp (d.mu y) (d.map (extend d f)) := by
  unfold extend
  rw [laws.assoc, laws.mu_natural, ← laws.assoc, laws.mu_assoc, laws.assoc, laws.map_comp]

theorem extend_bind {x y z} (f : Hom x (d.T y)) (g : Hom y (d.T z)) :
    extend d (bind d f g) = d.comp (extend d g) (extend d f) := by
  change d.comp (d.mu z) (d.map (d.comp (extend d g) f)) =
    d.comp (extend d g) (d.comp (d.mu y) (d.map f))
  rw [laws.map_comp, ← laws.assoc, ← extend_mu d laws, laws.assoc]

theorem bind_assoc {s x y z} (p : Hom s (d.T x)) (f : Hom x (d.T y)) (g : Hom y (d.T z)) :
    bind d (bind d p f) g = bind d p (bind d f g) := by
  change d.comp (extend d g) (d.comp (extend d f) p) = d.comp (extend d (bind d f g)) p
  rw [extend_bind d laws, laws.assoc]

theorem unit_compose {x y} (f : Hom x (d.T y)) : compose d (unit d y) f = f :=
  bind_unit d laws f

theorem compose_unit {x y} (f : Hom x (d.T y)) : compose d f (unit d x) = f :=
  unit_bind d laws f

theorem compose_assoc {w x y z} (h : Hom y (d.T z)) (g : Hom x (d.T y)) (f : Hom w (d.T x)) :
    compose d (compose d h g) f = compose d h (compose d g f) :=
  (bind_assoc d laws f g h).symm

theorem lift_id (x : Obj) : lift d (d.id x) = unit d x := laws.comp_id _

theorem lift_comp {x y z} (g : Hom y z) (f : Hom x y) :
    compose d (lift d g) (lift d f) = lift d (d.comp g f) := by
  change d.comp (d.comp (d.mu z) (d.map (d.comp (d.eta z) g))) (d.comp (d.eta y) f) =
    d.comp (d.eta z) (d.comp g f)
  rw [laws.map_comp, ← laws.assoc (d.mu z) (d.map (d.eta z)) (d.map g),
    laws.mu_map_eta, laws.id_comp, ← laws.assoc, laws.eta_natural, laws.assoc]

end VastitasOracle.Kleisli
