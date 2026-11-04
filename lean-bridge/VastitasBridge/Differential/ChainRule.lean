import VastitasBridge.Differential.Derivative
import VastitasOracle.SmoothRuntime

/-!
# The chain rule for the smooth runtime

The runtime reverse pass never forms a composite map: on `compose after before` it pulls the
seed back along `after` at the intermediate point, then along `before`. This file proves that
this is the cotangent pullback along the composite polynomial map that the program denotes.

* `cot_compose`: the pullback along `SmoothRuntime.compose after before` is the pullback along
  `after` at the image point, then along `before`. Its proof is the formal chain rule
  `pderiv_aeval` for substitution.
* `eval_denote`: a well-typed program evaluates as the single map it denotes, and that map is
  well formed (`denote_wellFormed`).
* **`backward_eq_cot`**: the recomputing reverse pass of a well-typed program is the cotangent
  pullback along its denoted map. `backward_eq_cot_saved` covers the saved tape, through the
  Oracle's `backward_forward`.
* **`pullback_composite`**: the checked pullback along a well-typed program, in either mode, is
  the checked pullback along its composite as one primitive.
* `smoothEqual_iff`: the runtime's `same` is equality of the denoted polynomial maps.
* `Cov x`: covectors whose basepoint is part of their type, a basepoint-only fragment after the
  polynomial cotangent proof of PR #377. It has no nominal objects or endpoints; the oracle port
  of PR #377 (Stage 3 step S6) carries those. `pullback_comp` is the typed chain rule; a typed
  seed is accepted only at its own index.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.Differential

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
open VastitasOracle.SmoothRuntime
open VastitasBridge.AlgebraicGeometry.Kernel
open MvPolynomial

variable {n k m : ℕ}

/-! ## One composite map -/

lemma eval_aeval_eq (x : Fin n → ℚ) (g : Fin k → MvPolynomial (Fin n) ℚ)
    (q : MvPolynomial (Fin k) ℚ) : eval x (aeval g q) = eval (fun l => eval x (g l)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Evaluating a substituted polynomial is evaluating at the image point. -/
theorem evalAt_subst {before : Map} (hb : WellFormed n k before) {p : Poly} (hp : Arity k p)
    (x : List ℚ) : evalAt (Poly.subst n before.images p) x = evalAt p (apply before x) := by
  rw [evalAt_eq_eval_evalPoint (canonical_subst hb.canonical p).arity,
    toMv_subst hb.canonical hb.length hp, eval_aeval_eq, evalAt_eq_eval_evalPoint hp,
    evalPoint_apply hb]

/-- The composite map sends a point where the two factors send it in turn. -/
theorem apply_compose {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (x : List ℚ) :
    apply (SmoothRuntime.compose after before) x = apply after (apply before x) := by
  simp only [apply, SmoothRuntime.compose, List.map_map, hb.arity]
  refine List.map_congr_left fun p hp => ?_
  exact evalAt_subst hb (ha.canonical p hp).arity x

/-- **Chain rule for one composite map.** Pulling a covector back along
`compose after before` at `x` is pulling it back along `after` at the image of `x`, then along
`before` at `x`. No length hypothesis on the point or the seed is needed. -/
theorem cot_compose {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (x η : List ℚ) :
    cot (SmoothRuntime.compose after before) x η = cot before x (cot after (apply before x) η) := by
  have hc := ha.compose hb
  refine ext_getD (n := n) (by rw [length_cot, hc.arity]) (by rw [length_cot, hb.arity])
    fun j => ?_
  rw [cot_getD hc, cot_getD hb, imageFamily_compose ha hb]
  simp only [cot_getD ha, pderiv_aeval, map_sum, map_mul, eval_aeval_eq, ← evalPoint_apply hb,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

/-! ## Programs -/

/-- The single map a well-typed program denotes is well formed. -/
theorem denote_wellFormed {F : Program} (hF : F.wellTyped n m = true) :
    WellFormed n m F.denote := by
  induction F generalizing n m with
  | primitive map => exact wellFormed_iff.1 hF
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    exact (ihAfter hF.2).compose (ihBefore hF.1)

/-- A well-typed program evaluates as the single map it denotes, at every point. -/
theorem eval_denote {F : Program} (hF : F.wellTyped n m = true) (x : List ℚ) :
    apply F.denote x = F.eval x := by
  induction F generalizing n m x with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    simp only [Program.denote, Program.eval]
    rw [apply_compose (denote_wellFormed hF.2) (denote_wellFormed hF.1), ihBefore hF.1,
      ihAfter hF.2]

/-- **The reverse pass is the cotangent pullback along the denoted map.** The recomputing
reverse pass of a well-typed program, which pulls back node by node at the recomputed
intermediate points, equals `cot` of the composite polynomial map, for every point and seed. -/
theorem backward_eq_cot {F : Program} (hF : F.wellTyped n m = true) (x η : List ℚ) :
    F.reverse x η = cot F.denote x η := by
  induction F generalizing n m x η with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at hF
    rw [Program.reverse, ihAfter hF.2, ihBefore hF.1, ← eval_denote hF.1, Program.denote,
      cot_compose (denote_wellFormed hF.2) (denote_wellFormed hF.1)]

/-- The same for the reverse pass over the saved tape. -/
theorem backward_eq_cot_saved {F : Program} (hF : F.wellTyped n m = true) (x η : List ℚ) :
    backwardSteps (F.forward x).steps η = cot F.denote x η := by
  rw [backward_forward, backward_eq_cot hF]

/-- **Pullback along the composite.** For a well-typed program, the checked pullback in either
mode equals the checked pullback along its composite map as one primitive node, for every
point and every seed, including seeds over other points and the failure value. -/
theorem pullback_composite (mode : PullbackMode) {F : Program} (hF : F.wellTyped n m = true)
    (point : Program) (seed : FiberValue) :
    pullback mode F point seed = pullback mode (.primitive F.denote) point seed := by
  cases seed with
  | none => rfl
  | some seed =>
    have hout : (Program.primitive F.denote).outputArity = F.outputArity := by
      rw [wellTyped_outputArity hF]
      exact (denote_wellFormed hF).length
    rw [pullback_spec, pullback_spec, hout]
    simp only [Program.eval, Program.reverse, eval_denote hF, backward_eq_cot hF]

/-- The same with `composite F`, the primitive node of the denoted map. -/
theorem pullback_eq_composite (mode : PullbackMode) {F : Program} (hF : F.wellTyped n m = true)
    (point : Program) (seed : FiberValue) :
    pullback mode F point seed = pullback mode (composite F) point seed :=
  pullback_composite mode hF point seed

/-! ## Equality of smooth maps -/

/-- **`same` is equality of polynomial maps.** Two well-typed programs with the same source
and target are `same` exactly when their denoted maps have equal images in
`MvPolynomial (Fin n) ℚ`. -/
theorem smoothEqual_iff {F G : Program} (hF : F.wellTyped n m = true)
    (hG : G.wellTyped n m = true) :
    same F G = true ↔ imageFamily n m F.denote.images = imageFamily n m G.denote.images := by
  have hF' := denote_wellFormed hF
  have hG' := denote_wellFormed hG
  rw [same, beq_iff_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    apply List.ext_getElem (hF'.length.trans hG'.length.symm)
    intro i hi hi'
    have hi'' : i < m := hF'.length ▸ hi
    have := toMv_injective (hF'.canonical_getD i) (hG'.canonical_getD i)
      (congrFun h ⟨i, hi''⟩)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi'] using this

/-! ## Covectors typed by their basepoint

After the polynomial cotangent fragment of PR #377, without its nominal objects and endpoints:
the basepoint of a covector is part of its type, so a typed seed is accepted only at its own
index. Moving the components of a covector to another index needs `transport`, which takes a
proof that the points are equal. The constructor itself can re-anchor components at any index;
the runtime's failure value, not this type, is what rejects a seed over another point. -/

/-- A covector at the point `x`: its components in the coordinate coframe at `x`. -/
structure Cov (x : List ℚ) where
  components : List ℚ

namespace Cov

theorem ext {x : List ℚ} {a b : Cov x} (h : a.components = b.components) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Reindex a covector along an equality of points. -/
def transport {x y : List ℚ} (h : x = y) (seed : Cov x) : Cov y := h ▸ seed

@[simp] theorem transport_components {x y : List ℚ} (h : x = y) (seed : Cov x) :
    (seed.transport h).components = seed.components := by
  cases h
  rfl

/-- The pullback along one map at `x`. Its seed must lie over the image of `x`. -/
def pullback (map : Map) (x : List ℚ) (seed : Cov (apply map x)) : Cov x :=
  ⟨cot map x seed.components⟩

/-- The reverse pass of a program at `x`. Its seed must lie over the program's value at `x`. -/
def reverse (F : Program) (x : List ℚ) (seed : Cov (F.eval x)) : Cov x :=
  ⟨F.reverse x seed.components⟩

end Cov

/-- **Typed chain rule.** The pullback along the composite map is the pullback along `after`
at the image point, then along `before`. The seed is transported from the composite's image
point to the iterated one by the proved `apply_compose`. -/
theorem pullback_comp {after before : Map} (ha : WellFormed k m after)
    (hb : WellFormed n k before) (x : List ℚ)
    (seed : Cov (apply (SmoothRuntime.compose after before) x)) :
    Cov.pullback (SmoothRuntime.compose after before) x seed =
      Cov.pullback before x (Cov.pullback after (apply before x)
        (seed.transport (apply_compose ha hb x))) := by
  apply Cov.ext
  simp [Cov.pullback, cot_compose ha hb]

/-- The typed reverse pass of a composite node runs the outer factor first. Its seed type
needs no transport: the intermediate point is the one the program computes. -/
theorem Cov.reverse_compose (after before : Program) (x : List ℚ)
    (seed : Cov ((Program.compose after before).eval x)) :
    Cov.reverse (.compose after before) x seed =
      Cov.reverse before x (Cov.reverse after (before.eval x) seed) := rfl

/-- The typed reverse pass of a well-typed program is the typed pullback along its denoted
map, with the seed transported by `eval_denote`. -/
theorem Cov.reverse_eq_pullback {F : Program} (hF : F.wellTyped n m = true) (x : List ℚ)
    (seed : Cov (F.eval x)) :
    Cov.reverse F x seed = Cov.pullback F.denote x (seed.transport (eval_denote hF x).symm) := by
  apply Cov.ext
  simp [Cov.reverse, Cov.pullback, backward_eq_cot hF]

/-! ### A seed over another point does not typecheck -/

section Examples

/-- The square map `t ↦ t²` of `ℝ`. -/
private def square : Map := ⟨1, [], [[⟨[2], 1⟩]]⟩

private theorem square_three : apply square [3] = [9] := by
  simp [apply, square, evalAt, monomialValue, npow]
  norm_num

-- The seed's type is the fiber over the computed image point; an anonymous seed takes it.
example : (Cov.pullback square [3] ⟨[1]⟩).components = [6] := by
  simp [Cov.pullback, cot, square, partialDerivative, evalAt, monomialValue, npow, dot]
  norm_num

-- A seed written over `9` is moved to that fiber only along the proved `3² = 9`. Elaboration
-- does not run rational arithmetic, so without the transport even this seed is rejected.
example : Cov [3] := Cov.pullback square [3] ((⟨[1]⟩ : Cov [9]).transport square_three.symm)

example : True := by
  fail_if_success
    have : Cov [3] := Cov.pullback square [3] (⟨[1]⟩ : Cov [9])
  exact True.intro

-- No proof can move a seed over `5` there.
example : apply square [3] ≠ [5] := by
  rw [square_three]
  norm_num

-- A seed over another point is rejected by elaboration. If the basepoint index were erased,
-- `fail_if_success` would itself fail.
example : True := by
  fail_if_success
    have : Cov [3] := Cov.pullback square [3] (⟨[1]⟩ : Cov [5])
  fail_if_success
    have : Cov [3] := (⟨[1]⟩ : Cov [2])
  exact True.intro

-- The same holds for arbitrary maps, programs and points.
example (_map : Map) (_x y : List ℚ) (_seed : Cov y) : True := by
  fail_if_success
    have : Cov _x := Cov.pullback _map _x _seed
  exact True.intro

example (_F : Program) (_x y : List ℚ) (_seed : Cov y) : True := by
  fail_if_success
    have : Cov _x := Cov.reverse _F _x _seed
  exact True.intro

end Examples

end VastitasBridge.Differential
