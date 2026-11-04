import VastitasOracle.SmoothCanonical
import VastitasOracle.SmoothRuntime

set_option autoImplicit false

/-! The chain rule of the smooth runtime, without mathlib (Stage 3).

`VastitasOracle.SmoothRuntime` proves that the reverse pass unfolds stepwise.
This module proves that it is calculus: the reverse pass of a well-typed
program is the cotangent pullback `cot` along the single map that the program
denotes. The statements are about the kernel definitions that the checker and
generated programs share. They use only Lean core: `Lean.Grind.CommRing`, and
`grind` for ring identities.

- `evalIn` evaluates the kernel's polynomials in any commutative ring that
  receives `ℚ` (`RatHom`). It turns `Poly.add` (including its cancelling
  branch), `Poly.mul` and `Poly.subst` into `+`, `*` and evaluation at the image
  point (`evalIn_add`, `evalIn_mul`, `evalIn_subst`). At the identity of `ℚ` it
  is the runtime's `evalAt` (`evalAt_eq_evalIn`).
- In the dual numbers `ℚ[ε]/(ε²)`, evaluation at `x + εv` computes the value at
  `x` and the directional derivative `Σⱼ vⱼ (∂ⱼ p)(x)`, with the runtime's
  `partialDerivative` (`dual_tangent`). Substitution then gives the chain rule
  for one polynomial (`evalAt_partial_subst`).
- `cot_compose`, `eval_denote`, `backward_eq_cot` and `pullback_composite` are
  the chain rule for maps and programs. They need no hypothesis on the point or
  the seed.
- `Cov` ports the typed cotangent fragment of PR #377 to the kernel's maps,
  with named spaces, typed points and `Cov.pullback_comp`.

The derivative here is the formal partial derivative of polynomials. That it
is the Fréchet derivative of the real polynomial map is proved in the mathlib
bridge (`VastitasBridge.Differential.Frechet`), not here. -/
namespace VastitasOracle.SmoothCalculus

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasOracle.SmoothCanonical

universe u

/-! ## Evaluation in a commutative ring -/

/-- A ring map from `ℚ`. -/
structure RatHom (R : Type u) [Lean.Grind.CommRing R] where
  toFun : Rat → R
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b

section Ring

variable {R : Type u} [Lean.Grind.CommRing R]

/-- The value of a monomial at a point of `Rⁿ`. Like `monomialValue`, a missing
coordinate contributes `1` and extra coordinates are ignored. -/
def monomialValueIn : Monomial → List R → R
  | exponent :: exponents, coordinate :: coordinates =>
    coordinate ^ exponent * monomialValueIn exponents coordinates
  | _, _ => 1

/-- The value of a polynomial at a point of `Rⁿ`, with coefficients mapped by `ι`. -/
def evalIn (ι : RatHom R) : Poly → List R → R
  | [], _ => 0
  | t :: p, point => ι.toFun t.coefficient * monomialValueIn t.monomial point + evalIn ι p point

theorem evalIn_nil (ι : RatHom R) (x : List R) : evalIn ι [] x = 0 := rfl

theorem evalIn_cons (ι : RatHom R) (t : Term) (p : Poly) (x : List R) :
    evalIn ι (t :: p) x = ι.toFun t.coefficient * monomialValueIn t.monomial x + evalIn ι p x := rfl

theorem RatHom.map_add_eq_zero (ι : RatHom R) {a b : Rat} (h : a + b = 0) :
    ι.toFun a + ι.toFun b = 0 := by
  rw [← ι.map_add, h, ι.map_zero]

/-- **Addition.** `Poly.add` is evaluated as a sum, through every branch of the
merge, including the branch that cancels two terms. No canonical form is needed. -/
theorem evalIn_add (ι : RatHom R) (p q : Poly) (x : List R) :
    evalIn ι (Poly.add p q) x = evalIn ι p x + evalIn ι q x := by
  fun_induction Poly.add p q with
  | case1 q => simp only [evalIn_nil]; grind
  | case2 s p => simp only [evalIn_nil]; grind
  | case3 s p t q _ ih => simp only [evalIn_cons, ih]; grind
  | case4 s p t q _ ih => simp only [evalIn_cons, ih]; grind
  | case5 s p t q heq _ hzero ih =>
    have same := (compare_eq_iff _ _).mp heq
    have hz : s.coefficient + t.coefficient = 0 := by simpa using hzero
    have := ι.map_add_eq_zero hz
    simp only [evalIn_cons, ih, same]
    grind
  | case6 s p t q heq _ _ ih =>
    have same := (compare_eq_iff _ _).mp heq
    have := ι.map_add s.coefficient t.coefficient
    simp only [evalIn_cons, ih, same]
    grind

/-! ### Products, powers, scaling and substitution

`Monomial.mul` adds exponents entrywise, so it multiplies values only for
monomials with the same number of exponents: every polynomial of one ring. -/

/-- Every monomial has `n` exponents. Canonical polynomials of arity `n` have
this property (`arity_of_canonical`); it is all that evaluation needs. -/
def Arity (n : Nat) (p : Poly) : Prop := ∀ t ∈ p, t.monomial.length = n

theorem arity_of_canonical {n : Nat} {p : Poly} (h : Poly.canonical n p = true) : Arity n p :=
  fun t ht => (((canonical_iff n p).mp h).1 t ht).1

theorem arity_nil (n : Nat) : Arity n [] := by simp [Arity]

theorem arity_add {n : Nat} {p q : Poly} (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.add p q) := by
  intro u hu
  rcases add_monomial hu with ⟨s, hs, hm⟩ | ⟨s, hs, hm⟩
  · rw [hm]; exact hp s hs
  · rw [hm]; exact hq s hs

theorem arity_mulTerm {n : Nat} {term : Term} {p : Poly} (hterm : term.monomial.length = n) (hp : Arity n p) :
    Arity n (Poly.mulTerm term p) := by
  unfold Poly.mulTerm
  split
  · exact arity_nil n
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
    simp [Monomial.mul, List.length_zipWith, hp t ht, hterm]

theorem arity_mul_foldl {n : Nat} {q : Poly} (hq : Arity n q) : ∀ (ts : Poly) (acc : Poly),
    Arity n ts → Arity n acc →
      Arity n (ts.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc)
  | [], _, _, hacc => hacc
  | t :: ts, acc, hts, hacc =>
    arity_mul_foldl hq ts _ (fun u hu => hts u (List.mem_cons_of_mem _ hu))
      (arity_add hacc (arity_mulTerm (hts t (by simp)) hq))

theorem arity_mul {n : Nat} {p q : Poly} (hp : Arity n p) (hq : Arity n q) : Arity n (Poly.mul p q) :=
  arity_mul_foldl hq p [] hp (arity_nil n)

theorem arity_const (n : Nat) (value : Rat) : Arity n (Poly.const n value) := by
  unfold Poly.const
  split
  · exact arity_nil n
  · simp [Arity, Monomial.one]

theorem arity_pow {n : Nat} {p : Poly} (hp : Arity n p) : ∀ e, Arity n (Poly.pow n p e)
  | 0 => arity_const n 1
  | e + 1 => arity_mul (arity_pow hp e) hp

theorem arity_scale {n : Nat} (value : Rat) {p : Poly} (hp : Arity n p) : Arity n (Poly.scale value p) := by
  unfold Poly.scale
  split
  · exact arity_nil n
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hu
    exact hp t ht

theorem arity_evalMonomial_foldl {n : Nat} {images : List Poly} (himages : ∀ g ∈ images, Arity n g) :
    ∀ (pairs : List (Nat × Poly)) (acc : Poly), (∀ pair ∈ pairs, pair.2 ∈ images) → Arity n acc →
      Arity n (pairs.foldl (fun product (pair : Nat × Poly) =>
        Poly.mul product (Poly.pow n pair.2 pair.1)) acc)
  | [], _, _, hacc => hacc
  | pair :: pairs, acc, hpairs, hacc =>
    arity_evalMonomial_foldl himages pairs _ (fun u hu => hpairs u (List.mem_cons_of_mem _ hu))
      (arity_mul hacc (arity_pow (himages _ (hpairs pair (by simp))) _))

theorem arity_evalMonomial {n : Nat} {images : List Poly} (himages : ∀ g ∈ images, Arity n g)
    (m : Monomial) : Arity n (Poly.evalMonomial n images m) :=
  arity_evalMonomial_foldl himages (m.zip images) (Poly.one n)
    (fun _ hpair => (List.of_mem_zip hpair).2) (arity_const n 1)

theorem arity_subst_foldl {n : Nat} {images : List Poly} (himages : ∀ g ∈ images, Arity n g) :
    ∀ (ts : Poly) (acc : Poly), Arity n acc →
      Arity n (ts.foldl (fun result t =>
        Poly.add result (Poly.scale t.coefficient (Poly.evalMonomial n images t.monomial))) acc)
  | [], _, hacc => hacc
  | _ :: ts, _, hacc =>
    arity_subst_foldl himages ts _ (arity_add hacc (arity_scale _ (arity_evalMonomial himages _)))

theorem arity_subst {n : Nat} {images : List Poly} (himages : ∀ g ∈ images, Arity n g) (p : Poly) :
    Arity n (Poly.subst n images p) :=
  arity_subst_foldl himages p [] (arity_nil n)

@[simp] theorem monomialValueIn_nil_left (x : List R) : monomialValueIn [] x = 1 := by
  cases x <;> rfl

@[simp] theorem monomialValueIn_nil_right (m : Monomial) : monomialValueIn m ([] : List R) = 1 := by
  cases m <;> rfl

@[simp] theorem monomialValueIn_cons (e : Nat) (es : Monomial) (c : R) (cs : List R) :
    monomialValueIn (e :: es) (c :: cs) = c ^ e * monomialValueIn es cs := rfl

theorem monomialValueIn_mul : ∀ (a b : Monomial) (x : List R), a.length = b.length →
    monomialValueIn (Monomial.mul a b) x = monomialValueIn a x * monomialValueIn b x
  | [], [], x, _ => by simp only [Monomial.mul, List.zipWith_nil_left, monomialValueIn_nil_left]; grind
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by
    simp only [Monomial.mul, List.zipWith_cons_cons, monomialValueIn_nil_right]; grind
  | e :: es, f :: fs, c :: cs, h => by
    have ih := monomialValueIn_mul es fs cs (by simpa using h)
    simp only [Monomial.mul, List.zipWith_cons_cons, monomialValueIn_cons] at ih ⊢
    rw [ih, Lean.Grind.Semiring.pow_add]
    grind

theorem evalIn_mulTerm (ι : RatHom R) (term : Term) {p : Poly}
    (hp : Arity term.monomial.length p) (x : List R) :
    evalIn ι (Poly.mulTerm term p) x =
      ι.toFun term.coefficient * monomialValueIn term.monomial x * evalIn ι p x := by
  unfold Poly.mulTerm
  split
  · rename_i hzero
    have : term.coefficient = 0 := by simpa using hzero
    rw [this, ι.map_zero, evalIn_nil]
    grind
  · induction p with
    | nil => simp only [List.map_nil, evalIn_nil]; grind
    | cons t p ih =>
      simp only [List.map_cons, evalIn_cons]
      rw [ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)), ι.map_mul,
        monomialValueIn_mul _ _ _ (hp t (by simp))]
      grind

theorem evalIn_mul_foldl (ι : RatHom R) {n : Nat} {q : Poly} (hq : Arity n q) (x : List R) :
    ∀ (ts : Poly) (acc : Poly), Arity n ts →
      evalIn ι (ts.foldl (fun product t => Poly.add product (Poly.mulTerm t q)) acc) x =
        evalIn ι acc x + evalIn ι ts x * evalIn ι q x
  | [], acc, _ => by simp only [List.foldl_nil, evalIn_nil]; grind
  | t :: ts, acc, hts => by
    have ht : t.monomial.length = n := hts t (by simp)
    rw [List.foldl_cons, evalIn_mul_foldl ι hq x ts _ (fun u hu => hts u (List.mem_cons_of_mem _ hu)),
      evalIn_add, evalIn_mulTerm ι t (ht ▸ hq), evalIn_cons]
    grind

/-- **Multiplication.** -/
theorem evalIn_mul (ι : RatHom R) {n : Nat} {p q : Poly} (hp : Arity n p) (hq : Arity n q)
    (x : List R) : evalIn ι (Poly.mul p q) x = evalIn ι p x * evalIn ι q x := by
  unfold Poly.mul
  rw [evalIn_mul_foldl ι hq x p [] hp, evalIn_nil]
  grind

theorem monomialValueIn_zero : ∀ (n : Nat) (x : List R), monomialValueIn (List.replicate n 0) x = 1
  | 0, x => monomialValueIn_nil_left x
  | _ + 1, [] => monomialValueIn_nil_right _
  | n + 1, c :: cs => by
    rw [List.replicate_succ, monomialValueIn_cons, monomialValueIn_zero n cs,
      Lean.Grind.Semiring.pow_zero]
    grind

theorem evalIn_one (ι : RatHom R) (n : Nat) (x : List R) : evalIn ι (Poly.one n) x = 1 := by
  have : ((1 : Rat) == 0) = false := by decide
  simp only [Poly.one, Poly.const, this, Bool.false_eq_true, ite_false, evalIn_cons, evalIn_nil,
    Monomial.one, monomialValueIn_zero, ι.map_one]
  grind

theorem evalIn_pow (ι : RatHom R) {n : Nat} {p : Poly} (hp : Arity n p) (x : List R) :
    ∀ e, evalIn ι (Poly.pow n p e) x = evalIn ι p x ^ e
  | 0 => by rw [Poly.pow, evalIn_one, Lean.Grind.Semiring.pow_zero]
  | e + 1 => by
    rw [Poly.pow, evalIn_mul ι (arity_pow hp e) hp, evalIn_pow ι hp x e,
      Lean.Grind.Semiring.pow_succ]

theorem evalIn_scale (ι : RatHom R) (value : Rat) (p : Poly) (x : List R) :
    evalIn ι (Poly.scale value p) x = ι.toFun value * evalIn ι p x := by
  unfold Poly.scale
  split
  · rename_i hzero
    have : value = 0 := by simpa using hzero
    rw [this, ι.map_zero, evalIn_nil]
    grind
  · induction p with
    | nil => simp only [List.map_nil, evalIn_nil]; grind
    | cons t p ih =>
      simp only [List.map_cons, evalIn_cons] at ih ⊢
      rw [ih, ι.map_mul]
      grind

theorem evalIn_evalMonomial_foldl (ι : RatHom R) {n : Nat} (x : List R) :
    ∀ (m : Monomial) (images : List Poly) (acc : Poly), (∀ g ∈ images, Arity n g) → Arity n acc →
      evalIn ι ((m.zip images).foldl (fun product (pair : Nat × Poly) =>
          Poly.mul product (Poly.pow n pair.2 pair.1)) acc) x =
        evalIn ι acc x * monomialValueIn m (images.map fun g => evalIn ι g x)
  | [], images, acc, _, _ => by
    simp only [List.zip_nil_left, List.foldl_nil, monomialValueIn_nil_left]; grind
  | _ :: _, [], acc, _, _ => by
    simp only [List.zip_nil_right, List.foldl_nil, List.map_nil, monomialValueIn_nil_right]; grind
  | e :: es, g :: gs, acc, himages, hacc => by
    have hg : Arity n g := himages g (by simp)
    rw [List.zip_cons_cons, List.foldl_cons,
      evalIn_evalMonomial_foldl ι x es gs _ (fun u hu => himages u (List.mem_cons_of_mem _ hu))
        (arity_mul hacc (arity_pow hg e)),
      evalIn_mul ι hacc (arity_pow hg e), evalIn_pow ι hg, List.map_cons, monomialValueIn_cons]
    grind

/-- Substitution into one monomial is the monomial evaluated at the image values. -/
theorem evalIn_evalMonomial (ι : RatHom R) {n : Nat} {images : List Poly}
    (himages : ∀ g ∈ images, Arity n g) (m : Monomial) (x : List R) :
    evalIn ι (Poly.evalMonomial n images m) x = monomialValueIn m (images.map fun g => evalIn ι g x) := by
  have h := evalIn_evalMonomial_foldl ι x m images (Poly.one n) himages (arity_const n 1)
  rw [evalIn_one, Lean.Grind.Semiring.one_mul] at h
  exact h

theorem evalIn_subst_foldl (ι : RatHom R) {n : Nat} {images : List Poly}
    (himages : ∀ g ∈ images, Arity n g) (x : List R) :
    ∀ (ts : Poly) (acc : Poly),
      evalIn ι (ts.foldl (fun result t =>
          Poly.add result (Poly.scale t.coefficient (Poly.evalMonomial n images t.monomial))) acc) x =
        evalIn ι acc x + evalIn ι ts (images.map fun g => evalIn ι g x)
  | [], acc => by simp only [List.foldl_nil, evalIn_nil]; grind
  | t :: ts, acc => by
    rw [List.foldl_cons, evalIn_subst_foldl ι himages x ts _, evalIn_add, evalIn_scale,
      evalIn_evalMonomial ι himages, evalIn_cons]
    grind

/-- **Substitution.** Evaluating `Poly.subst n images p` at `x` is evaluating `p`
at the values of the images at `x`. Only the images need `n` exponents per
monomial; `p` and `x` are arbitrary. -/
theorem evalIn_subst (ι : RatHom R) {n : Nat} {images : List Poly}
    (himages : ∀ g ∈ images, Arity n g) (p : Poly) (x : List R) :
    evalIn ι (Poly.subst n images p) x = evalIn ι p (images.map fun g => evalIn ι g x) := by
  unfold Poly.subst
  rw [evalIn_subst_foldl ι himages x p [], evalIn_nil]
  grind

end Ring

/-! ### Rational evaluation -/

/-- The identity of `ℚ`. -/
def RatHom.id : RatHom Rat where
  toFun value := value
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

theorem npow_eq_pow (value : Rat) : ∀ e, npow value e = value ^ e
  | 0 => (Lean.Grind.Semiring.pow_zero value).symm
  | e + 1 => by rw [npow, npow_eq_pow value e, Lean.Grind.Semiring.pow_succ]

theorem monomialValue_eq_monomialValueIn : ∀ (m : Monomial) (x : List Rat),
    monomialValue m x = monomialValueIn m x
  | [], x => by cases x <;> rfl
  | _ :: _, [] => rfl
  | e :: es, c :: cs => by
    rw [monomialValue, monomialValueIn_cons, npow_eq_pow, monomialValue_eq_monomialValueIn es cs]

/-- **The runtime's evaluation is `evalIn` at the identity of `ℚ`.** -/
theorem evalAt_eq_evalIn (p : Poly) (x : List Rat) : evalAt p x = evalIn RatHom.id p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [evalAt, evalIn_cons, ih, monomialValue_eq_monomialValueIn]
    rfl

/-! ## Dual numbers

`Dual` is `ℚ[ε]/(ε²)`: a value and a tangent. Evaluating a polynomial at
`x + εv` computes its value at `x` and its directional derivative along `v`
(`dual_tangent`). -/

/-- The dual number `re + ε eps`, with `ε² = 0`. -/
structure Dual where
  re : Rat
  eps : Rat
  deriving DecidableEq

namespace Dual

theorem ext_iff' {a b : Dual} : a = b ↔ a.re = b.re ∧ a.eps = b.eps := by
  cases a; cases b; simp

/-- Two dual numbers are equal when their components are. -/
theorem ext' {a b : Dual} (hre : a.re = b.re) (heps : a.eps = b.eps) : a = b :=
  ext_iff'.mpr ⟨hre, heps⟩

instance : Add Dual := ⟨fun a b => ⟨a.re + b.re, a.eps + b.eps⟩⟩
instance : Mul Dual := ⟨fun a b => ⟨a.re * b.re, a.re * b.eps + a.eps * b.re⟩⟩
instance : Neg Dual := ⟨fun a => ⟨-a.re, -a.eps⟩⟩
instance : Sub Dual := ⟨fun a b => ⟨a.re - b.re, a.eps - b.eps⟩⟩
instance : NatCast Dual := ⟨fun k => ⟨k, 0⟩⟩
instance : IntCast Dual := ⟨fun k => ⟨k, 0⟩⟩
instance (k : Nat) : OfNat Dual k := ⟨⟨(k : Rat), 0⟩⟩
instance : SMul Nat Dual := ⟨fun k a => ⟨k * a.re, k * a.eps⟩⟩
instance : SMul Int Dual := ⟨fun k a => ⟨k * a.re, k * a.eps⟩⟩

/-- `a ^ k`, by recursion on the exponent. -/
def pow (a : Dual) : Nat → Dual
  | 0 => ⟨1, 0⟩
  | k + 1 => pow a k * a

instance : HPow Dual Nat Dual := ⟨pow⟩

@[simp, grind =] theorem add_re (a b : Dual) : (a + b).re = a.re + b.re := rfl
@[simp, grind =] theorem add_eps (a b : Dual) : (a + b).eps = a.eps + b.eps := rfl
@[simp, grind =] theorem mul_re (a b : Dual) : (a * b).re = a.re * b.re := rfl
@[simp, grind =] theorem mul_eps (a b : Dual) : (a * b).eps = a.re * b.eps + a.eps * b.re := rfl
@[simp, grind =] theorem neg_re (a : Dual) : (-a).re = -a.re := rfl
@[simp, grind =] theorem neg_eps (a : Dual) : (-a).eps = -a.eps := rfl
@[simp, grind =] theorem sub_re (a b : Dual) : (a - b).re = a.re - b.re := rfl
@[simp, grind =] theorem sub_eps (a b : Dual) : (a - b).eps = a.eps - b.eps := rfl
@[simp, grind =] theorem ofNat_re (k : Nat) : (OfNat.ofNat k : Dual).re = (k : Rat) := rfl
@[simp, grind =] theorem ofNat_eps (k : Nat) : (OfNat.ofNat k : Dual).eps = 0 := rfl
@[simp, grind =] theorem zero_re : (0 : Dual).re = 0 := rfl
@[simp, grind =] theorem zero_eps : (0 : Dual).eps = 0 := rfl
@[simp, grind =] theorem one_re : (1 : Dual).re = 1 := rfl
@[simp, grind =] theorem one_eps : (1 : Dual).eps = 0 := rfl
@[simp, grind =] theorem natCast_re (k : Nat) : (k : Dual).re = (k : Rat) := rfl
@[simp, grind =] theorem natCast_eps (k : Nat) : (k : Dual).eps = 0 := rfl
@[simp, grind =] theorem intCast_re (k : Int) : (k : Dual).re = (k : Rat) := rfl
@[simp, grind =] theorem intCast_eps (k : Int) : (k : Dual).eps = 0 := rfl
@[simp, grind =] theorem nsmul_re (k : Nat) (a : Dual) : (k • a).re = k * a.re := rfl
@[simp, grind =] theorem nsmul_eps (k : Nat) (a : Dual) : (k • a).eps = k * a.eps := rfl
@[simp, grind =] theorem zsmul_re (k : Int) (a : Dual) : (k • a).re = k * a.re := rfl
@[simp, grind =] theorem zsmul_eps (k : Int) (a : Dual) : (k • a).eps = k * a.eps := rfl

/-- `Dual` is a commutative ring. Every law is checked componentwise in `ℚ`. -/
instance commRing : Lean.Grind.CommRing Dual where
  add_zero a := ext' (by grind) (by grind)
  add_comm a b := ext' (by grind) (by grind)
  add_assoc a b c := ext' (by grind) (by grind)
  mul_assoc a b c := ext' (by grind) (by grind)
  mul_one a := ext' (by grind) (by grind)
  one_mul a := ext' (by grind) (by grind)
  left_distrib a b c := ext' (by grind) (by grind)
  right_distrib a b c := ext' (by grind) (by grind)
  zero_mul a := ext' (by grind) (by grind)
  mul_zero a := ext' (by grind) (by grind)
  pow_zero a := rfl
  pow_succ a k := rfl
  ofNat_succ k := ext' (by grind) (by grind)
  ofNat_eq_natCast k := rfl
  nsmul_eq_natCast_mul k a := ext' (by grind) (by grind)
  neg_add_cancel a := ext' (by grind) (by grind)
  sub_eq_add_neg a b := ext' (by grind) (by grind)
  neg_zsmul k a := ext' (by grind) (by grind)
  zsmul_natCast_eq_nsmul k a := rfl
  intCast_ofNat k := rfl
  intCast_neg k := ext' (by grind) (by grind)
  mul_comm a b := ext' (by grind) (by grind)

/-- The constant dual numbers: `ℚ → Dual`, `q ↦ q + ε 0`. -/
def ofRat : RatHom Dual where
  toFun q := ⟨q, 0⟩
  map_zero := ext' (by grind) (by grind)
  map_one := ext' (by grind) (by grind)
  map_add a b := ext' (by grind) (by grind)
  map_mul a b := ext' (by grind) (by grind)

end Dual

/-! ### Dot products -/

theorem dot_nil_left (b : List Rat) : dot [] b = 0 := by cases b <;> rfl

theorem dot_nil_right (a : List Rat) : dot a [] = 0 := by cases a <;> rfl

theorem dot_cons (a : Rat) (as : List Rat) (b : Rat) (bs : List Rat) :
    dot (a :: as) (b :: bs) = a * b + dot as bs := rfl

theorem dot_comm : ∀ a b : List Rat, dot a b = dot b a
  | [], b => by rw [dot_nil_left, dot_nil_right]
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by rw [dot_cons, dot_cons, dot_comm xs ys]; grind

theorem dot_map_add {α : Type} (v : List Rat) (L : List α) (f g : α → Rat) :
    dot v (L.map fun j => f j + g j) = dot v (L.map f) + dot v (L.map g) := by
  induction L generalizing v with
  | nil => simp only [List.map_nil, dot_nil_right]; grind
  | cons a L ih =>
    cases v with
    | nil => simp only [dot_nil_left]; grind
    | cons c v => simp only [List.map_cons, dot_cons, ih]; grind

theorem dot_map_mul {α : Type} (v : List Rat) (L : List α) (c : Rat) (f : α → Rat) :
    dot v (L.map fun j => c * f j) = c * dot v (L.map f) := by
  induction L generalizing v with
  | nil => simp only [List.map_nil, dot_nil_right]; grind
  | cons a L ih =>
    cases v with
    | nil => simp only [dot_nil_left]; grind
    | cons d v => simp only [List.map_cons, dot_cons, ih]; grind

theorem dot_map_zero {α : Type} (v : List Rat) (L : List α) : dot v (L.map fun _ => (0 : Rat)) = 0 := by
  have := dot_map_mul v L 0 (fun _ => 0)
  simpa using this

theorem dot_map_add_left {α : Type} (L : List α) (f g : α → Rat) (w : List Rat) :
    dot (L.map fun j => f j + g j) w = dot (L.map f) w + dot (L.map g) w := by
  rw [dot_comm, dot_map_add, dot_comm w, dot_comm w]

theorem dot_map_mul_left {α : Type} (L : List α) (c : Rat) (f : α → Rat) (w : List Rat) :
    dot (L.map fun j => c * f j) w = c * dot (L.map f) w := by
  rw [dot_comm, dot_map_mul, dot_comm w]

/-- `ηᵀ (M w) = (ηᵀ M) w` for the matrix `M` with entries `f g l`. -/
theorem dot_swap {α : Type} (η : List Rat) (A : List α) (L : List Nat) (w : List Rat)
    (f : α → Nat → Rat) :
    dot η (A.map fun g => dot (L.map (f g)) w) = dot (L.map fun l => dot η (A.map fun g => f g l)) w := by
  induction A generalizing η with
  | nil => simp only [List.map_nil, dot_nil_right]; rw [dot_comm, dot_map_zero]
  | cons g A ih =>
    cases η with
    | nil => simp only [dot_nil_left]; rw [dot_comm, dot_map_zero]
    | cons e η =>
      simp only [List.map_cons, dot_cons]
      rw [ih, dot_map_add_left, dot_map_mul_left]

/-- The coordinate vector `e_j` picks out component `j`. -/
theorem dot_indicator_map : ∀ (n j : Nat) (f : Nat → Rat), j < n →
    dot ((List.range n).map fun i => if i = j then (1 : Rat) else 0) ((List.range n).map f) = f j
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, f, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map, dot_cons]
    cases j with
    | zero =>
      have : ((fun i => if i = 0 then (1 : Rat) else 0) ∘ Nat.succ) = fun _ => 0 := by
        funext i; simp
      rw [this, dot_comm, dot_map_zero]
      simp [Rat.add_zero]
    | succ j =>
      have : ((fun i => if i = j + 1 then (1 : Rat) else 0) ∘ Nat.succ) =
          fun i => if i = j then (1 : Rat) else 0 := by
        funext i; simp
      rw [this, dot_indicator_map n j (f ∘ Nat.succ) (by omega)]
      simp [Rat.zero_add]

/-! ### Directional derivatives -/

/-- The point `x + εv` of `Dualⁿ`. -/
def dualPoint (x v : List Rat) : List Dual := List.zipWith Dual.mk x v

/-- The directional derivative of a monomial at `x` along `v`, by the product rule. -/
def monomialTangent : Monomial → List Rat → List Rat → Rat
  | e :: es, c :: cs, w :: ws =>
    (e : Rat) * npow c (e - 1) * w * monomialValue es cs + npow c e * monomialTangent es cs ws
  | _, _, _ => 0

theorem monomialValue_nil_left (x : List Rat) : monomialValue [] x = 1 := by cases x <;> rfl

theorem monomialValue_nil_right (m : Monomial) : monomialValue m [] = 1 := by cases m <;> rfl

theorem monomialTangent_nil_left (x v : List Rat) : monomialTangent [] x v = 0 := by
  cases x <;> cases v <;> rfl

theorem monomialTangent_nil_mid (m : Monomial) (v : List Rat) : monomialTangent m [] v = 0 := by
  cases m <;> cases v <;> rfl

theorem Dual.pow_mk (c w : Rat) : ∀ e : Nat,
    (⟨c, w⟩ : Dual) ^ e = ⟨npow c e, (e : Rat) * npow c (e - 1) * w⟩
  | 0 => by rw [Lean.Grind.Semiring.pow_zero, Dual.ext_iff']; simp [npow]
  | e + 1 => by
    rw [Lean.Grind.Semiring.pow_succ, Dual.pow_mk c w e, Dual.ext_iff']
    cases e with
    | zero => simp [npow, Rat.add_zero]
    | succ e => simp only [Dual.mul_re, Dual.mul_eps, npow, Nat.add_sub_cancel]; push_cast; grind

/-- At `x + εv` a monomial takes its value at `x` plus `ε` times its directional
derivative along `v`. -/
theorem monomialValueIn_dual : ∀ (m : Monomial) (x v : List Rat), x.length = v.length →
    monomialValueIn m (dualPoint x v) = ⟨monomialValue m x, monomialTangent m x v⟩
  | [], x, v, _ => by
    rw [monomialValueIn_nil_left, monomialValue_nil_left, monomialTangent_nil_left]; rfl
  | _ :: _, [], v, _ => by
    rw [dualPoint, List.zipWith_nil_left, monomialValueIn_nil_right, monomialValue_nil_right,
      monomialTangent_nil_mid]; rfl
  | _ :: _, _ :: _, [], h => by simp at h
  | e :: es, c :: cs, w :: ws, h => by
    have ih := monomialValueIn_dual es cs ws (by simpa using h)
    rw [dualPoint, List.zipWith_cons_cons, monomialValueIn_cons, ← dualPoint, ih, Dual.pow_mk,
      Dual.ext_iff']
    simp only [Dual.mul_re, Dual.mul_eps, monomialValue, monomialTangent]
    grind

/-- The directional derivative of a monomial is the dot product of the direction
with its partial derivatives. -/
theorem monomialTangent_eq_dot : ∀ (n : Nat) (m : Monomial) (x v : List Rat),
    m.length = n → x.length = n → v.length = n →
    monomialTangent m x v = dot v ((List.range n).map fun j =>
      ((m.getD j 0 : Nat) : Rat) * monomialValue (m.set j (m.getD j 0 - 1)) x)
  | 0, m, _, v, hm, _, _ => by
    rw [List.length_eq_zero_iff.mp hm, monomialTangent_nil_left, List.range_zero, List.map_nil,
      dot_nil_right]
  | n + 1, e :: es, c :: cs, w :: ws, hm, hx, hv => by
    have ih := monomialTangent_eq_dot n es cs ws (by simpa using hm) (by simpa using hx)
      (by simpa using hv)
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, dot_cons, monomialTangent, ih]
    have : ((fun j => ((((e :: es).getD j 0 : Nat) : Rat)) *
          monomialValue ((e :: es).set j ((e :: es).getD j 0 - 1)) (c :: cs)) ∘ Nat.succ) =
        fun j => npow c e * ((es.getD j 0 : Nat) : Rat) * monomialValue (es.set j (es.getD j 0 - 1)) cs := by
      funext j
      simp only [Function.comp_apply, List.getD_cons_succ, List.set_cons_succ, monomialValue]
      grind
    rw [this]
    have : (fun j => npow c e * ((es.getD j 0 : Nat) : Rat) *
          monomialValue (es.set j (es.getD j 0 - 1)) cs) =
        fun j => npow c e * (((es.getD j 0 : Nat) : Rat) * monomialValue (es.set j (es.getD j 0 - 1)) cs) := by
      funext j; grind
    rw [this, dot_map_mul]
    simp only [List.getD_cons_zero, List.set_cons_zero, monomialValue]
    grind
  | _ + 1, [], _, _, hm, _, _ => by simp at hm
  | _ + 1, _ :: _, [], _, _, hx, _ => by simp at hx
  | _ + 1, _ :: _, _ :: _, [], _, _, hv => by simp at hv

theorem evalAt_partial_cons (j : Nat) (t : Term) (p : Poly) (x : List Rat) :
    evalAt (partialDerivative j (t :: p)) x =
      t.coefficient * (((t.monomial.getD j 0 : Nat) : Rat) *
        monomialValue (t.monomial.set j (t.monomial.getD j 0 - 1)) x) +
      evalAt (partialDerivative j p) x := by
  by_cases h : t.monomial.getD j 0 = 0
  · simp only [partialDerivative, h, ↓reduceIte]
    grind
  · simp only [partialDerivative, h, ↓reduceIte, evalAt]
    grind

theorem evalAt_partial_nil (j : Nat) (x : List Rat) : evalAt (partialDerivative j []) x = 0 := rfl

/-- **Dual numbers compute derivatives.** For a polynomial whose monomials have
`n` exponents, at a point `x` and a direction `v` with `n` coordinates,
evaluating at `x + εv` gives the value at `x` plus `ε` times the directional
derivative `Σⱼ vⱼ (∂ⱼ p)(x)`, with the runtime's `partialDerivative`. -/
theorem dual_tangent {n : Nat} {p : Poly} (hp : Arity n p) {x v : List Rat}
    (hx : x.length = n) (hv : v.length = n) :
    evalIn Dual.ofRat p (dualPoint x v) =
      ⟨evalAt p x, dot v ((List.range n).map fun j => evalAt (partialDerivative j p) x)⟩ := by
  induction p with
  | nil =>
    simp only [evalIn_nil, evalAt_partial_nil, dot_map_zero]
    rfl
  | cons t p ih =>
    rw [evalIn_cons, ih (fun u hu => hp u (List.mem_cons_of_mem _ hu)),
      monomialValueIn_dual _ _ _ (hx.trans hv.symm)]
    simp only [evalAt_partial_cons]
    rw [dot_map_add, dot_map_mul, ← monomialTangent_eq_dot n t.monomial x v (hp t (by simp)) hx hv,
      Dual.ext_iff']
    simp only [Dual.add_re, Dual.add_eps, Dual.mul_re, Dual.mul_eps, Dual.ofRat, evalAt]
    grind

/-! ## The chain rule -/

/-- **Chain rule for one polynomial.** The partial derivative of `g ∘ images` at
`x` is the dot product of the partial derivatives of `g` at the image point
with the partial derivatives of the images at `x`. -/
theorem evalAt_partial_subst {n k : Nat} {images : List Poly} (himages : ∀ b ∈ images, Arity n b)
    (hk : images.length = k) {g : Poly} (hg : Arity k g) {x : List Rat} (hx : x.length = n)
    {j : Nat} (hj : j < n) :
    evalAt (partialDerivative j (Poly.subst n images g)) x =
      dot ((List.range k).map fun l => evalAt (partialDerivative l g) (images.map fun b => evalAt b x))
        (images.map fun b => evalAt (partialDerivative j b) x) := by
  have he : ((List.range n).map fun i => if i = j then (1 : Rat) else 0).length = n := by simp
  have h1 := dual_tangent (arity_subst himages g) hx he
  rw [evalIn_subst Dual.ofRat himages] at h1
  have h2 : (images.map fun b =>
        evalIn Dual.ofRat b (dualPoint x ((List.range n).map fun i => if i = j then (1 : Rat) else 0))) =
      dualPoint (images.map fun b => evalAt b x) (images.map fun b => evalAt (partialDerivative j b) x) := by
    have : ∀ b ∈ images,
        evalIn Dual.ofRat b (dualPoint x ((List.range n).map fun i => if i = j then (1 : Rat) else 0)) =
          ⟨evalAt b x, evalAt (partialDerivative j b) x⟩ := by
      intro b hb
      rw [dual_tangent (himages b hb) hx he, dot_indicator_map n j _ hj]
    rw [List.map_congr_left this]
    simp only [dualPoint, List.zipWith_map, List.zipWith_self]
  rw [h2, dual_tangent hg (by simp [hk]) (by simp [hk])] at h1
  have := congrArg Dual.eps h1
  simp only at this
  rw [dot_indicator_map n j _ hj] at this
  rw [← this, dot_comm]

/-- **Chain rule for one composite map, at a point with `n` coordinates.** -/
theorem cot_compose_of_length {n k m : Nat} {after before : Map}
    (ha : wellFormed k m after = true) (hb : wellFormed n k before = true) {x : List Rat}
    (hx : x.length = n) (η : List Rat) :
    cot (VastitasKernel.SmoothRuntime.compose after before) x η =
      cot before x (cot after (apply before x) η) := by
  obtain ⟨haArity, _, _, haImages⟩ := (wellFormed_iff k m after).mp ha
  obtain ⟨hbArity, _, hbLength, hbImages⟩ := (wellFormed_iff n k before).mp hb
  have himages : ∀ b ∈ before.images, Arity n b := fun b hb => arity_of_canonical (hbImages b hb)
  apply List.ext_getElem
  · simp [cot, VastitasKernel.SmoothRuntime.compose]
  · intro j hj _
    have hjn : j < n := by simpa [cot, VastitasKernel.SmoothRuntime.compose, hbArity] using hj
    simp only [cot, VastitasKernel.SmoothRuntime.compose, List.getElem_map, List.getElem_range,
      List.map_map, hbArity, haArity]
    have : ∀ g ∈ after.images,
        ((fun image => evalAt (partialDerivative j image) x) ∘ Poly.subst n before.images) g =
          dot ((List.range k).map fun l => evalAt (partialDerivative l g) (apply before x))
            (before.images.map fun b => evalAt (partialDerivative j b) x) := fun g hg =>
      evalAt_partial_subst himages hbLength (arity_of_canonical (haImages g hg)) hx hjn
    rw [List.map_congr_left this]
    exact dot_swap η after.images (List.range k) _ (fun g l => evalAt (partialDerivative l g) (apply before x))

/-! ### Points with any number of coordinates

The runtime reads a missing coordinate as `1` and ignores extra coordinates.
`fit n x` makes that explicit, so the chain rule needs no length hypothesis. -/

/-- The point of `ℚⁿ` at which the runtime evaluates `x`: coordinate `i` of `x`,
and `1` past its end. -/
def fit (n : Nat) (x : List Rat) : List Rat := (List.range n).map fun i => x.getD i 1

theorem fit_length (n : Nat) (x : List Rat) : (fit n x).length = n := by simp [fit]

theorem fit_succ_nil (n : Nat) : fit (n + 1) [] = 1 :: fit n [] := by
  simp [fit, List.range_succ_eq_map]

theorem fit_succ_cons (n : Nat) (c : Rat) (cs : List Rat) : fit (n + 1) (c :: cs) = c :: fit n cs := by
  simp [fit, List.range_succ_eq_map]

theorem npow_one : ∀ e, npow 1 e = 1
  | 0 => rfl
  | e + 1 => by rw [npow, npow_one e, Rat.mul_one]

theorem monomialValue_fit : ∀ (n : Nat) (m : Monomial) (x : List Rat), m.length = n →
    monomialValue m (fit n x) = monomialValue m x
  | 0, m, x, hm => by rw [List.length_eq_zero_iff.mp hm, monomialValue_nil_left, monomialValue_nil_left]
  | _ + 1, [], _, hm => by simp at hm
  | n + 1, e :: es, [], hm => by
    rw [fit_succ_nil, monomialValue, npow_one, monomialValue_fit n es [] (by simpa using hm),
      monomialValue_nil_right, monomialValue_nil_right, Rat.one_mul]
  | n + 1, e :: es, c :: cs, hm => by
    rw [fit_succ_cons, monomialValue, monomialValue, monomialValue_fit n es cs (by simpa using hm)]

theorem evalAt_fit {n : Nat} {p : Poly} (hp : Arity n p) (x : List Rat) :
    evalAt p (fit n x) = evalAt p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [evalAt, evalAt, monomialValue_fit n _ _ (hp t (by simp)),
      ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))]

theorem arity_partial {n : Nat} {p : Poly} (hp : Arity n p) (j : Nat) :
    Arity n (partialDerivative j p) := by
  induction p with
  | nil => exact arity_nil n
  | cons t p ih =>
    have ih := ih (fun u hu => hp u (List.mem_cons_of_mem _ hu))
    simp only [partialDerivative]
    split
    · exact ih
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · simp [hp t (by simp)]
      · exact ih u hu

theorem apply_fit {n m : Nat} {map : Map} (h : wellFormed n m map = true) (x : List Rat) :
    apply map (fit n x) = apply map x := by
  obtain ⟨_, _, _, himages⟩ := (wellFormed_iff n m map).mp h
  exact List.map_congr_left fun g hg => evalAt_fit (arity_of_canonical (himages g hg)) x

theorem cot_fit {n m : Nat} {map : Map} (h : wellFormed n m map = true) (x η : List Rat) :
    cot map (fit n x) η = cot map x η := by
  obtain ⟨_, _, _, himages⟩ := (wellFormed_iff n m map).mp h
  refine List.map_congr_left fun j _ => ?_
  congr 1
  exact List.map_congr_left fun g hg =>
    evalAt_fit (arity_partial (arity_of_canonical (himages g hg)) j) x

/-- **Chain rule for one composite map.** Pulling a covector back along
`compose after before` at `x` is pulling it back along `after` at the image of
`x`, then along `before` at `x`. No length hypothesis on the point or the seed
is needed. -/
theorem cot_compose {n k m : Nat} {after before : Map}
    (ha : wellFormed k m after = true) (hb : wellFormed n k before = true) (x η : List Rat) :
    cot (VastitasKernel.SmoothRuntime.compose after before) x η =
      cot before x (cot after (apply before x) η) := by
  have hc := compose_wellFormed ha hb
  rw [← cot_fit hc x η, ← cot_fit hb x, ← apply_fit hb x]
  exact cot_compose_of_length ha hb (fit_length n x) η

/-- The composite map sends a point where the two factors send it in turn. Only
the inner map needs to be well formed. -/
theorem apply_compose {n k : Nat} {after before : Map} (hb : wellFormed n k before = true)
    (x : List Rat) :
    apply (VastitasKernel.SmoothRuntime.compose after before) x = apply after (apply before x) := by
  obtain ⟨hbArity, _, _, hbImages⟩ := (wellFormed_iff n k before).mp hb
  have himages : ∀ b ∈ before.images, Arity n b := fun b hb => arity_of_canonical (hbImages b hb)
  simp only [apply, VastitasKernel.SmoothRuntime.compose, List.map_map, hbArity]
  refine List.map_congr_left fun g _ => ?_
  simp only [Function.comp_apply]
  rw [evalAt_eq_evalIn, evalIn_subst RatHom.id himages, evalAt_eq_evalIn]
  congr 1
  exact List.map_congr_left fun b _ => (evalAt_eq_evalIn b x).symm

/-! ## Programs -/

/-- A well-typed program evaluates as the single map it denotes, at every point. -/
theorem eval_denote {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) (x : List Rat) :
    apply F.denote x = F.eval x := by
  induction F generalizing n m x with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    simp only [Program.denote, Program.eval]
    rw [apply_compose (denote_wellFormed hF.1), ihBefore hF.1, ihAfter hF.2]

/-- **The reverse pass is the cotangent pullback along the denoted map.** The
recomputing reverse pass of a well-typed program, which pulls back node by node
at the recomputed intermediate points, equals `cot` of the composite polynomial
map, for every point and seed. -/
theorem backward_eq_cot {F : Program} {n m : Nat} (hF : F.wellTyped n m = true) (x η : List Rat) :
    F.reverse x η = cot F.denote x η := by
  induction F generalizing n m x η with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    rw [Program.reverse, ihAfter hF.2, ihBefore hF.1, ← eval_denote hF.1, Program.denote,
      cot_compose (denote_wellFormed hF.2) (denote_wellFormed hF.1)]

/-- The same for the reverse pass over the saved tape. -/
theorem backward_eq_cot_saved {F : Program} {n m : Nat} (hF : F.wellTyped n m = true)
    (x η : List Rat) : backwardSteps (F.forward x).steps η = cot F.denote x η := by
  rw [VastitasOracle.SmoothRuntime.backward_forward, backward_eq_cot hF]

/-- **Pullback along the composite.** For a well-typed program, the checked
pullback in either mode equals the checked pullback along its composite map as
one primitive node, for every point and every seed, including seeds over other
points and the failure value. -/
theorem pullback_composite (mode : PullbackMode) {F : Program} {n m : Nat}
    (hF : F.wellTyped n m = true) (point : Program) (seed : FiberValue) :
    pullback mode F point seed = pullback mode (.primitive F.denote) point seed := by
  cases seed with
  | none => rw [VastitasOracle.SmoothRuntime.pullback_none, VastitasOracle.SmoothRuntime.pullback_none]
  | some seed =>
    have hout : (Program.primitive F.denote).outputArity = F.outputArity := by
      rw [VastitasOracle.SmoothRuntime.wellTyped_outputArity hF]
      exact ((wellFormed_iff n m F.denote).mp (denote_wellFormed hF)).2.2.1
    rw [VastitasOracle.SmoothRuntime.pullback_spec, VastitasOracle.SmoothRuntime.pullback_spec, hout]
    simp only [Program.eval, Program.reverse, eval_denote hF, backward_eq_cot hF]

/-- The same with `composite F`, the primitive node of the denoted map. -/
theorem pullback_eq_composite (mode : PullbackMode) {F : Program} {n m : Nat}
    (hF : F.wellTyped n m = true) (point : Program) (seed : FiberValue) :
    pullback mode F point seed = pullback mode (composite F) point seed :=
  pullback_composite mode hF point seed

/-! ## Covectors typed by object and basepoint

The port of the typed cotangent fragment of PR #377 to the kernel's own maps.
A point belongs to a named space, and a covector to a point of that space: the
object and the basepoint are part of the type. A seed is accepted only at its
own index, and moving it to another index needs `Cov.transport`, which takes a
proof that the points are equal. `Cov.pullback_comp` is the typed chain rule;
its transport is the proved `SmoothMap.at_comp`. -/

/-- A named smooth affine space `ℝⁿ`. The name is a nominal identity: two spaces
of one dimension have different points. It grants no authority. -/
structure Space where
  name : String
  dimension : Nat
  deriving DecidableEq

/-- A rational point of `X`. -/
structure Point (X : Space) where
  coordinates : List Rat
  length : coordinates.length = X.dimension

theorem Point.ext {X : Space} {x y : Point X} (h : x.coordinates = y.coordinates) : x = y := by
  cases x; cases y; cases h; rfl

/-- A smooth map between named spaces: a well-formed kernel map between their
dimensions. -/
structure SmoothMap (X Y : Space) where
  map : Map
  wf : wellFormed X.dimension Y.dimension map = true

namespace SmoothMap

variable {X Y Z : Space}

theorem length_apply (f : SmoothMap X Y) (x : List Rat) : (apply f.map x).length = Y.dimension := by
  simp [apply, ((wellFormed_iff _ _ _).mp f.wf).2.2.1]

/-- The image of a point. -/
def applyPoint (f : SmoothMap X Y) (x : Point X) : Point Y :=
  ⟨apply f.map x.coordinates, f.length_apply _⟩

/-- `comp g f` is `g` after `f`. The middle object is shared by type. -/
def comp (g : SmoothMap Y Z) (f : SmoothMap X Y) : SmoothMap X Z :=
  ⟨VastitasKernel.SmoothRuntime.compose g.map f.map, compose_wellFormed g.wf f.wf⟩

theorem identity_wellFormed (n : Nat) : wellFormed n n (identity n) = true := by
  rw [wellFormed_iff]
  refine ⟨rfl, rfl, by simp [identity], ?_⟩
  intro image h
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
  simp [Poly.canonical, Poly.var, Monomial.var]

/-- The identity of `X`. -/
def id (X : Space) : SmoothMap X X := ⟨identity X.dimension, identity_wellFormed X.dimension⟩

theorem at_comp (g : SmoothMap Y Z) (f : SmoothMap X Y) (x : Point X) :
    (g.comp f).applyPoint x = g.applyPoint (f.applyPoint x) :=
  Point.ext (apply_compose f.wf x.coordinates)

theorem at_id (x : Point X) : (SmoothMap.id X).applyPoint x = x := by
  apply Point.ext
  show apply (identity X.dimension) x.coordinates = x.coordinates
  rw [← x.length]
  exact VastitasOracle.SmoothRuntime.apply_identity x.coordinates

end SmoothMap

/-- A covector at the point `x` of `X`: its components in the coordinate coframe
at `x`, one per coordinate of `X`. -/
structure Cov {X : Space} (x : Point X) where
  components : List Rat
  length : components.length = X.dimension

namespace Cov

variable {X Y Z : Space}

theorem ext {x : Point X} {a b : Cov x} (h : a.components = b.components) : a = b := by
  cases a; cases b; cases h; rfl

/-- Reindex a covector along an equality of points of one space. -/
def transport {x y : Point X} (h : x = y) (seed : Cov x) : Cov y := h ▸ seed

@[simp] theorem transport_components {x y : Point X} (h : x = y) (seed : Cov x) :
    (seed.transport h).components = seed.components := by
  cases h
  rfl

/-- The pullback `T*_{f(x)} Y → T*ₓ X` along `f` at `x`. Its seed must lie over
the image of `x`. It runs the kernel's `cot`. -/
def pullback (f : SmoothMap X Y) (x : Point X) (seed : Cov (f.applyPoint x)) : Cov x :=
  ⟨cot f.map x.coordinates seed.components, by
    rw [VastitasOracle.SmoothRuntime.cot_length, ((wellFormed_iff _ _ _).mp f.wf).1]⟩

/-- **Typed chain rule.** The pullback along the composite is the pullback along
`g` at the image point, then along `f`. The seed is transported from the
composite's image point to the iterated one by the proved `SmoothMap.at_comp`. -/
theorem pullback_comp (g : SmoothMap Y Z) (f : SmoothMap X Y) (x : Point X)
    (seed : Cov ((g.comp f).applyPoint x)) :
    pullback (g.comp f) x seed =
      pullback f x (pullback g (f.applyPoint x) (seed.transport (SmoothMap.at_comp g f x))) := by
  apply Cov.ext
  simp only [pullback, transport_components]
  exact cot_compose g.wf f.wf x.coordinates seed.components

/-- The identity pulls every covector back to itself. -/
theorem pullback_id (x : Point X) (seed : Cov x) :
    pullback (SmoothMap.id X) x (seed.transport (SmoothMap.at_id x).symm) = seed := by
  apply Cov.ext
  simp only [pullback, transport_components]
  exact VastitasOracle.SmoothRuntime.cot_identity _ _ _ seed.length

/-- The typed pullback is the runtime's checked pullback, in either mode, at a
point program whose coordinates are `x`. -/
theorem pullback_runtime (mode : PullbackMode) (f : SmoothMap X Y) (x : Point X) (point : Program)
    (hpoint : coordinates point = x.coordinates) (seed : Cov (f.applyPoint x)) :
    VastitasKernel.SmoothRuntime.pullback mode (.primitive f.map) point
        (some ⟨(f.applyPoint x).coordinates, seed.components⟩) =
      some ⟨x.coordinates, (pullback f x seed).components⟩ := by
  have hlength : seed.components.length = (Program.primitive f.map).outputArity := by
    rw [seed.length]
    exact (((wellFormed_iff _ _ _).mp f.wf).2.2.1).symm
  rw [VastitasOracle.SmoothRuntime.pullback_spec, ite_eq_left ⟨by simp [SmoothMap.applyPoint, Program.eval, hpoint],
    hlength⟩]
  simp [pullback, Program.reverse, hpoint]

end Cov

/-- A proposed reverse rule for `f`, usable only with a proof that it is the
pullback at every point and seed. A function of the right shape is not enough. -/
structure VerifiedRule {X Y : Space} (f : SmoothMap X Y) where
  run : (x : Point X) → Cov (f.applyPoint x) → Cov x
  correct : ∀ x seed, run x seed = Cov.pullback f x seed

def canonicalRule {X Y : Space} (f : SmoothMap X Y) : VerifiedRule f := ⟨Cov.pullback f, fun _ _ => rfl⟩

/-! ### Regressions

The values are computed by the kernel's `cot` and `apply`; `decide +kernel`
reduces them in the kernel. The failed elaborations test the types of this
model, not the checker's rejection of source programs. If an index were erased,
`fail_if_success` would itself fail. -/

namespace Regression

def A : Space := ⟨"A", 2⟩
def B : Space := ⟨"B", 2⟩
def C : Space := ⟨"C", 2⟩

def origin : Point A := ⟨[0, 0], rfl⟩
def unitSeed : Cov origin := ⟨[1, 0], rfl⟩

-- The shears `f(x, y) = (x + y, y)` and `g(x, y) = (x, x + y)` of #361 both fix the origin.
def shearF : SmoothMap A A := ⟨⟨2, [], [[⟨[1, 0], 1⟩, ⟨[0, 1], 1⟩], [⟨[0, 1], 1⟩]]⟩, by decide⟩
def shearG : SmoothMap A A := ⟨⟨2, [], [[⟨[1, 0], 1⟩], [⟨[1, 0], 1⟩, ⟨[0, 1], 1⟩]]⟩, by decide⟩

theorem shearF_origin : shearF.applyPoint origin = origin := Point.ext (by decide +kernel)
theorem shearG_origin : shearG.applyPoint origin = origin := Point.ext (by decide +kernel)

def fPull (seed : Cov origin) : Cov origin := Cov.pullback shearF origin (seed.transport shearF_origin.symm)
def gPull (seed : Cov origin) : Cov origin := Cov.pullback shearG origin (seed.transport shearG_origin.symm)

theorem shear_correct_order : fPull (gPull unitSeed) = ⟨[1, 1], rfl⟩ :=
  Cov.ext (by decide +kernel)

theorem shear_reversed_order : gPull (fPull unitSeed) = ⟨[2, 1], rfl⟩ :=
  Cov.ext (by decide +kernel)

-- Both orders have the same type, so only the values tell them apart.
theorem shear_orders_differ : fPull (gPull unitSeed) ≠ gPull (fPull unitSeed) := by
  rw [shear_correct_order, shear_reversed_order]
  intro h
  exact absurd (congrArg Cov.components h) (by decide)

theorem shear_composite :
    Cov.pullback (shearG.comp shearF) origin ⟨[1, 0], rfl⟩ = fPull (gPull unitSeed) := by
  rw [Cov.pullback_comp]
  exact Cov.ext (by decide +kernel)

-- Nonlinear maps evaluate derivatives at the intermediate point `(7, 6)`, not at
-- the source point `(2, 3)`: `f(x, y) = (x² + y, xy)`, `g(u, v) = (u + v², uv)`.
def nonlinearF : SmoothMap A B :=
  ⟨⟨2, [], [[⟨[2, 0], 1⟩, ⟨[0, 1], 1⟩], [⟨[1, 1], 1⟩]]⟩, by decide⟩
def nonlinearG : SmoothMap B C :=
  ⟨⟨2, [], [[⟨[0, 2], 1⟩, ⟨[1, 0], 1⟩], [⟨[1, 1], 1⟩]]⟩, by decide⟩
def p : Point A := ⟨[2, 3], rfl⟩
def nonlinearSeed : Cov ((nonlinearG.comp nonlinearF).applyPoint p) := ⟨[3, 5], rfl⟩

theorem nonlinearF_p : nonlinearF.applyPoint p = ⟨[7, 6], rfl⟩ := Point.ext (by decide +kernel)

example : ((nonlinearG.comp nonlinearF).applyPoint p).coordinates = [43, 42] := by
  rw [SmoothMap.at_comp, nonlinearF_p]
  decide +kernel

/-- The (345, 175) case of PR #377, on the kernel's maps. -/
theorem nonlinear_value :
    Cov.pullback (nonlinearG.comp nonlinearF) p nonlinearSeed = ⟨[345, 175], rfl⟩ := by
  rw [Cov.pullback_comp]
  exact Cov.ext (by decide +kernel)

-- The kernel also computes the composite map itself: substitution, products and
-- the merge of `Poly.add`. Its pullback agrees with the stepwise one.
example : (Cov.pullback (nonlinearG.comp nonlinearF) p nonlinearSeed).components = [345, 175] := by
  decide +kernel

-- A seed written over `(7, 6)` is moved to the fiber over `f(p)` only along the
-- proved equation. Elaboration does not run rational arithmetic, so without the
-- transport even this seed is rejected.
example : Cov p := Cov.pullback nonlinearF p ((⟨[3, 5], rfl⟩ : Cov (⟨[7, 6], rfl⟩ : Point B)).transport
  nonlinearF_p.symm)

example : True := by
  fail_if_success
    have : Cov p := Cov.pullback nonlinearF p (⟨[3, 5], rfl⟩ : Cov (⟨[7, 6], rfl⟩ : Point B))
  exact True.intro

-- Coefficients, points and seeds are rational: `f(x, y) = (x²/2, y)`.
def rationalMap : SmoothMap A B := ⟨⟨2, [], [[⟨[2, 0], 1 / 2⟩], [⟨[0, 1], 1⟩]]⟩, by decide +kernel⟩
def rationalPoint : Point A := ⟨[2 / 3, 3 / 4], rfl⟩

example : Cov.pullback rationalMap rationalPoint ⟨[3 / 2, -1 / 3], rfl⟩ = ⟨[1, -1 / 3], rfl⟩ :=
  Cov.ext (by decide +kernel)

-- A wrong middle object, a point of another space, a seed over another object
-- with the right coordinates, a seed over the source point instead of the image,
-- and a covector at another point of the same space all fail to elaborate.
example : True := by
  fail_if_success
    have : SmoothMap A B := nonlinearF.comp nonlinearF
  fail_if_success
    have : Point B := p
  fail_if_success
    have : Cov p := Cov.pullback nonlinearF p (⟨[3, 5], rfl⟩ : Cov (⟨[7, 6], rfl⟩ : Point C))
  fail_if_success
    have : Cov p := Cov.pullback nonlinearF p (⟨[3, 5], rfl⟩ : Cov (⟨[2, 3], rfl⟩ : Point B))
  fail_if_success
    have : Cov origin := (⟨[1, 0], rfl⟩ : Cov p)
  exact True.intro

-- The same holds for arbitrary maps and points.
example (_f : SmoothMap A B) (_x : Point A) (y : Point B) (_seed : Cov y) : True := by
  fail_if_success
    have : Cov _x := Cov.pullback _f _x _seed
  exact True.intro

-- A bare function is not a verified rule, and the zero rule for the identity has no proof.
def zeroRule (x : Point A) (_ : Cov ((SmoothMap.id A).applyPoint x)) : Cov x := ⟨[0, 0], rfl⟩

example : True := by
  fail_if_success
    have : VerifiedRule (SmoothMap.id A) := zeroRule
  exact True.intro

theorem zero_rule_cannot_be_verified :
    ¬ ∃ rule : VerifiedRule (SmoothMap.id A), rule.run = zeroRule := by
  rintro ⟨rule, same⟩
  have h := rule.correct origin (unitSeed.transport (SmoothMap.at_id origin).symm)
  rw [same, Cov.pullback_id] at h
  exact absurd (congrArg Cov.components h) (by decide)

example : (canonicalRule (SmoothMap.id A)).run origin (unitSeed.transport (SmoothMap.at_id origin).symm) =
    unitSeed :=
  Cov.pullback_id origin unitSeed

end Regression

end VastitasOracle.SmoothCalculus
