import VastitasOracle.Coordinates
import Lean

/-!
Exact two-variable polynomial cotangents, the first mathematical slice of #361.

This is a mathematical presentation over `Rat`, not accepted AD Core. No metric,
smoothness oracle, external derivative rule, native reflection or new checker is
used. The general C∞ differential and compiler correspondence remain separate.
-/
namespace VastitasOracle.PolynomialCotangent

abbrev Axis := Fin 2
abbrev Coordinates2 := Coordinates.RationalCoordinates ⟨.ordinary, .qq, 2⟩

def coordinates (x y : Rat) : Coordinates2 := fun i => if i = 0 then x else y

theorem coordinates_ext {a b : Coordinates2} (h₀ : a 0 = b 0) (h₁ : a 1 = b 1) :
    a = b := by
  funext i
  have hi : i = 0 ∨ i = 1 := by
    simp only [Fin.ext_iff]
    have bound : i.val < 2 := i.isLt
    omega
  rcases hi with rfl | rfl <;> assumption

/-- Polynomial expressions with exact coefficients. Negation and natural powers
are expressible using constants, addition and multiplication. -/
inductive Polynomial where
  | constant (value : Rat)
  | var (axis : Axis)
  | add (left right : Polynomial)
  | mul (left right : Polynomial)

namespace Polynomial

def eval : Polynomial → Coordinates2 → Rat
  | .constant c, _ => c
  | .var i, x => x i
  | .add p q, x => eval p x + eval q x
  | .mul p q, x => eval p x * eval q x

/-- Formal partial derivative in the polynomial fragment only. -/
def derivative : Polynomial → Axis → Polynomial
  | .constant _, _ => .constant 0
  | .var j, i => .constant (if i = j then 1 else 0)
  | .add p q, i => .add (derivative p i) (derivative q i)
  | .mul p q, i => .add (.mul (derivative p i) q) (.mul p (derivative q i))

/-- Simultaneous substitution: the components of the inner map replace variables
of the outer polynomial. This is the contravariant coordinate-ring direction. -/
def substitute : Polynomial → (Axis → Polynomial) → Polynomial
  | .constant c, _ => .constant c
  | .var i, f => f i
  | .add p q, f => .add (substitute p f) (substitute q f)
  | .mul p q, f => .mul (substitute p f) (substitute q f)

theorem eval_substitute (p : Polynomial) (f : Axis → Polynomial) (x : Coordinates2) :
    (p.substitute f).eval x = p.eval (fun j => (f j).eval x) := by
  induction p <;> simp_all [substitute, eval]

/-- Chain rule for every expression in this fragment, not just sampled maps. -/
theorem derivative_substitute (p : Polynomial) (f : Axis → Polynomial)
    (x : Coordinates2) (i : Axis) :
    ((p.substitute f).derivative i).eval x =
      (p.derivative 0).eval (fun j => (f j).eval x) * ((f 0).derivative i).eval x +
      (p.derivative 1).eval (fun j => (f j).eval x) * ((f 1).derivative i).eval x := by
  induction p with
  | constant c => simp [substitute, derivative, eval] <;> grind
  | var j =>
    have hi : j = 0 ∨ j = 1 := by
      simp only [Fin.ext_iff]
      have bound : j.val < 2 := j.isLt
      omega
    rcases hi with rfl | rfl <;> simp [substitute, derivative, eval] <;> grind
  | add p q hp hq =>
    simp only [substitute, derivative, eval, hp, hq]
    grind
  | mul p q hp hq =>
    simp only [substitute, derivative, eval, eval_substitute, hp, hq]
    grind

/-- A Q-linear derivation into the evaluation module Q at the specified point.
The module action is multiplication by `p.eval x`; constants have derivative 0.
This is a fiberwise polynomial notion, not a universal C∞ derivation. -/
structure DerivationAt (x : Coordinates2) where
  value : Polynomial → Rat
  constant : ∀ c, value (.constant c) = 0
  add : ∀ p q, value (.add p q) = value p + value q
  mul : ∀ p q, value (.mul p q) = value p * q.eval x + p.eval x * value q

/-- The values on dx and dy uniquely determine every polynomial derivation. -/
theorem DerivationAt.coordinates (D : DerivationAt x) (p : Polynomial) :
    D.value p = (p.derivative 0).eval x * D.value (.var 0) +
      (p.derivative 1).eval x * D.value (.var 1) := by
  induction p with
  | constant c => simp [D.constant, derivative, eval] <;> grind
  | var j =>
    have hi : j = 0 ∨ j = 1 := by
      simp only [Fin.ext_iff]
      have bound : j.val < 2 := j.isLt
      omega
    rcases hi with rfl | rfl <;> simp [derivative, eval] <;> grind
  | add p q hp hq =>
    rw [D.add, hp, hq]
    simp only [derivative, eval]
    grind
  | mul p q hp hq =>
    rw [D.mul, hp, hq]
    simp only [derivative, eval]
    grind

/-- Every choice of the two generator values actually defines a derivation. -/
def directional (x v : Coordinates2) : DerivationAt x where
  value p := (p.derivative 0).eval x * v 0 + (p.derivative 1).eval x * v 1
  constant _ := by simp [derivative, eval] <;> grind
  add _ _ := by simp only [derivative, eval]; grind
  mul _ _ := by simp only [derivative, eval]; grind

theorem directional_generator (x v : Coordinates2) (i : Axis) :
    (directional x v).value (.var i) = v i := by
  have hi : i = 0 ∨ i = 1 := by
    simp only [Fin.ext_iff]
    have bound : i.val < 2 := i.isLt
    omega
  rcases hi with rfl | rfl <;> simp [directional, derivative, eval] <;> grind

theorem DerivationAt.unique (D E : DerivationAt x)
    (h₀ : D.value (.var 0) = E.value (.var 0))
    (h₁ : D.value (.var 1) = E.value (.var 1)) : D.value = E.value := by
  funext p
  rw [D.coordinates p, E.coordinates p, h₀, h₁]

/-- The ordinary commutative Q-algebra presentation relation. This is explicit
algebraic evidence, not equality of floating values or a general equality solver. -/
inductive Equivalent : Polynomial → Polynomial → Prop where
  | refl (p) : Equivalent p p
  | symm : Equivalent p q → Equivalent q p
  | trans : Equivalent p q → Equivalent q r → Equivalent p r
  | add : Equivalent p q → Equivalent r s → Equivalent (.add p r) (.add q s)
  | mul : Equivalent p q → Equivalent r s → Equivalent (.mul p r) (.mul q s)
  | add_assoc (p q r) : Equivalent (.add (.add p q) r) (.add p (.add q r))
  | add_comm (p q) : Equivalent (.add p q) (.add q p)
  | add_zero (p) : Equivalent (.add p (.constant 0)) p
  | add_neg (p) : Equivalent (.add p (.mul (.constant (-1)) p)) (.constant 0)
  | mul_assoc (p q r) : Equivalent (.mul (.mul p q) r) (.mul p (.mul q r))
  | mul_comm (p q) : Equivalent (.mul p q) (.mul q p)
  | mul_one (p) : Equivalent (.mul p (.constant 1)) p
  | mul_zero (p) : Equivalent (.mul p (.constant 0)) (.constant 0)
  | mul_add (p q r) : Equivalent (.mul p (.add q r)) (.add (.mul p q) (.mul p r))
  | constant_add (a b) : Equivalent (.add (.constant a) (.constant b)) (.constant (a + b))
  | constant_mul (a b) : Equivalent (.mul (.constant a) (.constant b)) (.constant (a * b))

/-- Primal and differential respect the polynomial-ring presentation. In
particular, the differential does not depend on choosing expanded/factored syntax. -/
theorem equivalent_jet {p q : Polynomial} (h : Equivalent p q) (x : Coordinates2) :
    p.eval x = q.eval x ∧ ∀ i, (p.derivative i).eval x = (q.derivative i).eval x := by
  induction h <;> constructor
  all_goals first | intro i | skip
  all_goals try simp only [eval, derivative] at *
  all_goals grind

end Polynomial

/-- A named affine plane over the fixed base Q, with a fixed ordered coordinate
basis and its dual. The name does not confer production namespace authority. -/
structure Plane where
  name : String
  deriving DecidableEq

/-- Rational points only; this does not identify a scheme with its Q-points. -/
structure Point (X : Plane) where
  coordinates : Coordinates2

theorem Point.ext {x y : Point X} (h : x.coordinates = y.coordinates) : x = y := by
  cases x; cases y; cases h; rfl

structure PolynomialMap (X Y : Plane) where
  components : Axis → Polynomial

namespace PolynomialMap

def applyPoint (f : PolynomialMap X Y) (x : Point X) : Point Y :=
  ⟨fun i => (f.components i).eval x.coordinates⟩

def identity (X : Plane) : PolynomialMap X X := ⟨Polynomial.var⟩

/-- `comp g f` means g after f, with the middle nominal object shared by type. -/
def comp (g : PolynomialMap Y Z) (f : PolynomialMap X Y) : PolynomialMap X Z :=
  ⟨fun i => (g.components i).substitute f.components⟩

theorem at_identity (x : Point X) : (identity X).applyPoint x = x := rfl

theorem at_comp (g : PolynomialMap Y Z) (f : PolynomialMap X Y) (x : Point X) :
    (comp g f).applyPoint x = g.applyPoint (f.applyPoint x) := by
  apply Point.ext
  funext i
  exact Polynomial.eval_substitute _ _ _

end PolynomialMap

/-- The coordinate covector space Q dx ⊕ Q dy in the fiber at this exact point.
It is a structure, not an abbreviation erasing the nominal object/basepoint. -/
structure Cotangent {X : Plane} (x : Point X) where
  components : Coordinates2

namespace Cotangent

theorem ext {x : Point X} {a b : Cotangent x} (h : a.components = b.components) : a = b := by
  cases a; cases b; cases h; rfl

/-- Reindex only along an actual equality of points of the same named plane. -/
def transport {x y : Point X} (h : x = y) (seed : Cotangent x) : Cotangent y :=
  h ▸ seed

theorem transport_components {x y : Point X} (h : x = y) (seed : Cotangent x) :
    (transport h seed).components = seed.components := by cases h; rfl

def add {x : Point X} (a b : Cotangent x) : Cotangent x :=
  ⟨fun i => a.components i + b.components i⟩

def scale {x : Point X} (c : Rat) (a : Cotangent x) : Cotangent x :=
  ⟨fun i => c * a.components i⟩

end Cotangent

/-- The polynomial differential, in the ordered dual basis at the given point. -/
def differential (p : Polynomial) (x : Point X) : Cotangent x :=
  ⟨fun i => (p.derivative i).eval x.coordinates⟩

/-- `J_f(x)ᵀ seed`: T*_(f(x)) Y → T*_x X, with no metric or conjugation. -/
def pullback (f : PolynomialMap X Y) (x : Point X)
    (seed : Cotangent (f.applyPoint x)) : Cotangent x :=
  ⟨fun i => ((f.components 0).derivative i).eval x.coordinates * seed.components 0 +
    ((f.components 1).derivative i).eval x.coordinates * seed.components 1⟩

/-- Pulling back the canonical differential agrees with differentiating the
substituted polynomial. This ties the map to the differential, not just its laws. -/
theorem differential_substitute (p : Polynomial) (f : PolynomialMap X Y) (x : Point X) :
    differential (p.substitute f.components) x =
      pullback f x (differential p (f.applyPoint x)) := by
  apply Cotangent.ext
  funext i
  simp only [differential, pullback, Polynomial.derivative_substitute, PolynomialMap.applyPoint]
  grind

theorem pullback_add (f : PolynomialMap X Y) (x : Point X)
    (a b : Cotangent (f.applyPoint x)) :
    pullback f x (a.add b) = (pullback f x a).add (pullback f x b) := by
  apply Cotangent.ext
  funext i
  simp only [pullback, Cotangent.add]
  grind

theorem pullback_scale (f : PolynomialMap X Y) (x : Point X) (c : Rat)
    (a : Cotangent (f.applyPoint x)) :
    pullback f x (a.scale c) = (pullback f x a).scale c := by
  apply Cotangent.ext
  funext i
  simp only [pullback, Cotangent.scale]
  grind

theorem pullback_identity (x : Point X) (seed : Cotangent x) :
    pullback (.identity X) x seed = seed := by
  apply Cotangent.ext
  funext i
  have hi : i = 0 ∨ i = 1 := by
    simp only [Fin.ext_iff]
    have bound : i.val < 2 := i.isLt
    omega
  rcases hi with rfl | rfl <;>
    simp [pullback, PolynomialMap.identity, Polynomial.derivative, Polynomial.eval, Rat.add_zero, Rat.zero_add]

/-- Typed reverse composition. The seed is transported from the actual composite
point to the iterated point by the proved substitution/evaluation equality. -/
theorem pullback_comp (g : PolynomialMap Y Z) (f : PolynomialMap X Y) (x : Point X)
    (seed : Cotangent ((g.comp f).applyPoint x)) :
    pullback (g.comp f) x seed =
      pullback f x (pullback g (f.applyPoint x)
        (seed.transport (PolynomialMap.at_comp g f x))) := by
  apply Cotangent.ext
  funext i
  simp only [pullback]
  simp only [Cotangent.transport_components]
  simp only [PolynomialMap.comp, Polynomial.derivative_substitute, PolynomialMap.applyPoint]
  grind

/-- A proposed custom rule is usable only together with a proof that it equals
the canonical polynomial pullback at every point and seed. This is mathematical
evidence, not a new Domain Checker or a production AD registration mechanism. -/
structure VerifiedRule (f : PolynomialMap X Y) where
  run : (x : Point X) → Cotangent (f.applyPoint x) → Cotangent x
  correct : ∀ x seed, run x seed = pullback f x seed

def canonicalRule (f : PolynomialMap X Y) : VerifiedRule f := ⟨pullback f, fun _ _ => rfl⟩

end VastitasOracle.PolynomialCotangent
