import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Structural soundness of the smooth runtime (Stage 3).

These theorems are about the kernel definitions that generated programs run.
They need no calculus:

- the saved-tape reverse pass and the recomputing reverse pass agree;
- every saved forward value is the value the forward pass computed;
- a pullback is defined only on the fiber over the image point, and its result
  lies over the input point;
- pulling back along a composite program is pulling back along each factor in
  reverse order, at the intermediate point;
- the identity pulls every covector back to itself;
- the failure value is absorbing and observably distinct from every fiber.

That the reverse pass is the transpose of the derivative of the composite map
(the chain rule) is a statement about calculus. It is not proved here:
`VastitasOracle.SmoothCalculus` proves it without mathlib (`cot_compose`,
`backward_eq_cot`, `pullback_composite`), and the mathlib bridge proves it
independently in `VastitasBridge.Differential.ChainRule`. The theorems below
unfold the implementation; they do not compare it with a derivative. -/
namespace VastitasOracle.SmoothRuntime

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

/-! ## Lengths -/

theorem cot_length (map : Map) (point seed : List Rat) : (cot map point seed).length = map.arity := by
  simp [cot]

theorem reverse_length (program : Program) (point seed : List Rat) :
    (program.reverse point seed).length = program.inputArity := by
  induction program generalizing point seed with
  | primitive map => simp [Program.reverse, Program.inputArity, cot_length]
  | compose after before _ ihBefore =>
    simp [Program.reverse, Program.inputArity, ihBefore]

theorem eval_length (program : Program) (point : List Rat) :
    (program.eval point).length = program.outputArity := by
  induction program generalizing point with
  | primitive map => simp [Program.eval, Program.outputArity, apply]
  | compose after _ ihAfter _ => simp [Program.eval, Program.outputArity, ihAfter]

theorem wellTyped_inputArity {program : Program} {source target : Nat}
    (h : program.wellTyped source target = true) : program.inputArity = source := by
  induction program generalizing source target with
  | primitive map =>
    simp [Program.wellTyped, wellFormed] at h
    simp [Program.inputArity, h.1.1.1]
  | compose after before _ ihBefore =>
    simp only [Program.wellTyped, Bool.and_eq_true] at h
    simpa [Program.inputArity] using ihBefore h.1

theorem wellTyped_outputArity {program : Program} {source target : Nat}
    (h : program.wellTyped source target = true) : program.outputArity = target := by
  induction program generalizing source target with
  | primitive map =>
    simp [Program.wellTyped, wellFormed] at h
    simp [Program.outputArity, h.1.2]
  | compose after before ihAfter _ =>
    simp only [Program.wellTyped, Bool.and_eq_true] at h
    simpa [Program.outputArity] using ihAfter h.2

/-! ## Saved and recomputed forward values -/

theorem record_output (program : Program) (point : List Rat) :
    (program.record point).2 = program.eval point := by
  induction program generalizing point with
  | primitive map => rfl
  | compose after before ihAfter ihBefore =>
    simp only [Program.record, Program.eval]
    rw [← ihBefore point, ← ihAfter]

theorem record_compose (after before : Program) (point : List Rat) :
    ((Program.compose after before).record point).1 =
      (before.record point).1 ++ (after.record (before.eval point)).1 := by
  simp only [Program.record]
  rw [← record_output before point]

theorem forward_input (program : Program) (point : List Rat) :
    (program.forward point).input = point := rfl

theorem forward_output (program : Program) (point : List Rat) :
    (program.forward point).output = program.eval point :=
  record_output program point

/-- The tape of a composite saves the intermediate point: the inner factor's
steps come first, then the outer factor's steps, recorded at the inner output. -/
theorem forward_residual (after before : Program) (point : List Rat) :
    ((Program.compose after before).forward point).steps =
      (before.forward point).steps ++ (after.forward (before.eval point)).steps :=
  record_compose after before point

theorem backwardSteps_append (first second : List Step) (seed : List Rat) :
    backwardSteps (first ++ second) seed = backwardSteps first (backwardSteps second seed) := by
  simp [backwardSteps, List.foldr_append]

theorem backward_record (program : Program) (point seed : List Rat) :
    backwardSteps (program.record point).1 seed = program.reverse point seed := by
  induction program generalizing point seed with
  | primitive map => simp [Program.record, backwardSteps, Program.reverse]
  | compose after before ihAfter ihBefore =>
    rw [record_compose, backwardSteps_append, ihAfter, ihBefore]
    rfl

/-- **Saved = recomputed.** The reverse pass over the saved tape is the reverse
pass that recomputes every forward value. -/
theorem backward_forward (program : Program) (point seed : List Rat) :
    backwardSteps (program.forward point).steps seed = program.reverse point seed :=
  backward_record program point seed

/-- The reverse pass over a composite node runs the outer factor at the inner
factor's output, then the inner factor: the reverse pass is stepwise at the
intermediate point. That the implementation never forms the composite map is a
property of the definition; it is tested, not stated here. -/
theorem reverse_compose (after before : Program) (point seed : List Rat) :
    (Program.compose after before).reverse point seed =
      before.reverse point (after.reverse (before.eval point) seed) := rfl

/-! ## Pullbacks -/

theorem linearize_output (map point : Program) :
    (linearize map point).output = map.eval (coordinates point) := forward_output _ _

theorem linearize_input (map point : Program) :
    (linearize map point).input = coordinates point := rfl

/-- Both modes compute the recomputing reverse pass, on the fiber over the image. -/
theorem pullback_spec (mode : PullbackMode) (map point : Program) (seed : Fiber) :
    pullback mode map point (some seed) =
      if seed.point = map.eval (coordinates point) ∧ seed.components.length = map.outputArity then
        some ⟨coordinates point, map.reverse (coordinates point) seed.components⟩
      else none := by
  cases mode
  · simp only [pullback, backward, linearize_output, linearize_input, eval_length, beq_iff_eq,
      Bool.and_eq_true]
    split
    · simp only [linearize, backward_forward]
    · rfl
  · simp [pullback]

theorem pullback_saved_eq_recomputed (map point : Program) (seed : FiberValue) :
    pullback .saved map point seed = pullback .recomputed map point seed := by
  cases seed with
  | none => rfl
  | some seed => rw [pullback_spec, pullback_spec]

theorem pullback_none (mode : PullbackMode) (map point : Program) :
    pullback mode map point none = none := by
  cases mode <;> rfl

/-- **A seed over another point fails.** -/
theorem pullback_wrong_point (mode : PullbackMode) (map point : Program) (seed : Fiber)
    (h : seed.point ≠ map.eval (coordinates point)) :
    pullback mode map point (some seed) = none := by
  rw [pullback_spec]
  simp [h]

theorem pullback_wrong_length (mode : PullbackMode) (map point : Program) (seed : Fiber)
    (h : seed.components.length ≠ map.outputArity) :
    pullback mode map point (some seed) = none := by
  rw [pullback_spec]
  simp [h]

/-- **Membership.** A pullback at `point` lies over `point` and has one
component per source coordinate of the map. With dimension checks
(`pullback_mem_of_wellTyped`) it is a covector in the cotangent space at
`point`. -/
theorem pullback_mem {mode : PullbackMode} {map point : Program} {seed : FiberValue} {result : Fiber}
    (h : pullback mode map point seed = some result) :
    result.point = coordinates point ∧ result.components.length = map.inputArity := by
  cases seed with
  | none => simp [pullback_none] at h
  | some seed =>
    rw [pullback_spec] at h
    split at h
    · cases h
      exact ⟨rfl, reverse_length _ _ _⟩
    · cases h

theorem coordinates_compose (map point : Program) :
    coordinates (.compose map point) = map.eval (coordinates point) := rfl

/-- **Stepwise pullback.** Pulling back along `g ∘ f` at `x` is pulling back
along `g` at `f(x)` and then along `f` at `x`, for every seed, including the
failure value and seeds over other points. -/
theorem pullback_stepwise (mode : PullbackMode) (outer inner point : Program) (seed : FiberValue)
    (h : outer.inputArity = inner.outputArity) :
    pullback mode (.compose outer inner) point seed =
      pullback mode inner point (pullback mode outer (.compose inner point) seed) := by
  cases seed with
  | none => simp only [pullback_none]
  | some seed =>
    rw [pullback_spec, pullback_spec]
    by_cases hs : seed.point = outer.eval (inner.eval (coordinates point)) ∧
        seed.components.length = outer.outputArity
    · have hl : seed.point = (Program.compose outer inner).eval (coordinates point) ∧
          seed.components.length = (Program.compose outer inner).outputArity := hs
      have hr : seed.point = outer.eval (coordinates (.compose inner point)) ∧
          seed.components.length = outer.outputArity := hs
      rw [ite_eq_left hl, ite_eq_left hr, pullback_spec,
        ite_eq_left ⟨rfl, by rw [reverse_length, h]⟩]
      rfl
    · have hl : ¬(seed.point = (Program.compose outer inner).eval (coordinates point) ∧
          seed.components.length = (Program.compose outer inner).outputArity) := hs
      have hr : ¬(seed.point = outer.eval (coordinates (.compose inner point)) ∧
          seed.components.length = outer.outputArity) := hs
      rw [ite_eq_right hl, ite_eq_right hr, pullback_none]

theorem pullback_stepwise_of_wellTyped (mode : PullbackMode) (outer inner point : Program)
    (seed : FiberValue) {source target : Nat}
    (h : (Program.compose outer inner).wellTyped source target = true) :
    pullback mode (.compose outer inner) point seed =
      pullback mode inner point (pullback mode outer (.compose inner point) seed) := by
  simp only [Program.wellTyped, Bool.and_eq_true] at h
  exact pullback_stepwise mode outer inner point seed (wellTyped_inputArity h.2)

/-! ## Saved tapes -/


/-- The first-class tape gives the same result as the pullback. -/
theorem backward_linearize (map point : Program) (seed : FiberValue) :
    backward (linearize map point) seed = pullback .saved map point seed := rfl

/-- The differential is the pullback of the coordinate covector at the image. -/
theorem differential_eq_pullback (function point : Program) :
    differential function point =
      pullback .saved function point (some ⟨function.eval (coordinates point), [1]⟩) := by
  simp only [differential, pullback, linearize_output]

/-- A tape rejects a seed that does not lie over its own output. -/
theorem backward_foreign_seed (tape : Tape) (seed : Fiber) (h : seed.point ≠ tape.output) :
    backward tape (some seed) = none := by
  simp [backward, h]

theorem backward_none (tape : Tape) : backward tape none = none := rfl

/-- **Membership with dimensions.** For a map checked as `ℝⁿ → ℝᵐ` and a point
checked as `ℝ⁰ → ℝⁿ`, a pullback lies over a point with `n` coordinates and
has `n` components: it is a covector in the cotangent space at that point. -/
theorem pullback_mem_of_wellTyped {mode : PullbackMode} {map point : Program} {seed : FiberValue}
    {result : Fiber} {n m : Nat} (hmap : map.wellTyped n m = true)
    (hpoint : point.wellTyped 0 n = true) (h : pullback mode map point seed = some result) :
    result.point = coordinates point ∧ result.point.length = n ∧ result.components.length = n := by
  obtain ⟨hp, hc⟩ := pullback_mem h
  refine ⟨hp, ?_, ?_⟩
  · rw [hp, coordinates, eval_length, wellTyped_outputArity hpoint]
  · rw [hc, wellTyped_inputArity hmap]

/-! ## The failure value -/

theorem fiberAt_none (point : Program) : fiberAt none point = false := rfl

theorem fiberEqual_none_left (value : FiberValue) : fiberEqual none value = false := by
  cases value <;> rfl

theorem fiberEqual_none_right (value : FiberValue) : fiberEqual value none = false := by
  cases value <;> rfl

theorem fiberEqual_iff (left right : Fiber) : fiberEqual (some left) (some right) = true ↔ left = right := by
  simp [fiberEqual]

theorem component_none (index : Nat) : component none index = (0, 0) := rfl

/-- A component of a fiber has a positive denominator, so it is never the
failure reading `(0, 0)`. -/
theorem component_some_den_pos (fiber : Fiber) (index : Nat) :
    0 < (component (some fiber) index).2 := by
  simp [component, ratPair, Rat.den_pos]

theorem component_ne_failure (fiber : Fiber) (index : Nat) :
    component (some fiber) index ≠ (0, 0) := by
  intro h
  have := component_some_den_pos fiber index
  rw [h] at this
  exact Int.lt_irrefl 0 this

theorem pairing_none_left (value : FiberValue) : pairing none value = (0, 0) := by
  cases value <;> rfl

theorem pairing_none_right (value : FiberValue) : pairing value none = (0, 0) := by
  cases value <;> rfl

/-- Pairing a covector with a vector at another point reads the failure value. -/
theorem pairing_wrong_point (alpha v : Fiber) (h : alpha.point ≠ v.point) :
    pairing (some alpha) (some v) = (0, 0) := by
  simp [pairing, h]

/-- Pairing fibers with different component counts reads the failure value. -/
theorem pairing_wrong_length (alpha v : Fiber) (h : alpha.components.length ≠ v.components.length) :
    pairing (some alpha) (some v) = (0, 0) := by
  simp [pairing, h]

/-- A pairing that does not read the failure value comes from fibers at one
point with equal component counts. -/
theorem pairing_some (alpha v : Fiber) (h : pairing (some alpha) (some v) ≠ (0, 0)) :
    alpha.point = v.point ∧ alpha.components.length = v.components.length := by
  by_cases hp : alpha.point = v.point
  · by_cases hl : alpha.components.length = v.components.length
    · exact ⟨hp, hl⟩
    · exact absurd (pairing_wrong_length alpha v hl) h
  · exact absurd (pairing_wrong_point alpha v hp) h

/-- `flat` and `sharp` keep the basepoint and map the failure value to itself. -/
theorem transform_point (matrix : Matrix) (fiber : Fiber) :
    transform matrix (some fiber) = some ⟨fiber.point, matVec matrix fiber.components⟩ := rfl

theorem transform_none (matrix : Matrix) : transform matrix none = none := rfl

/-! ## Identity -/

theorem npow_zero (value : Rat) : npow value 0 = 1 := rfl

theorem monomialValue_zero : ∀ (monomial : Monomial) (point : List Rat),
    (∀ exponent ∈ monomial, exponent = 0) → monomialValue monomial point = 1
  | [], _, _ => by simp [monomialValue]
  | _ :: _, [], _ => by simp [monomialValue]
  | exponent :: exponents, coordinate :: coordinates, h => by
    have he : exponent = 0 := h exponent (List.mem_cons_self ..)
    simp only [monomialValue, he, npow_zero, Rat.one_mul]
    exact monomialValue_zero exponents coordinates fun e he => h e (List.mem_cons_of_mem _ he)

theorem var_getD (arity index j : Nat) (hj : j < arity) :
    (Monomial.var arity index).getD j 0 = if j = index then 1 else 0 := by
  simp [Monomial.var, List.getD_eq_getElem?_getD, hj]

theorem var_set_zero (arity index : Nat) :
    ∀ exponent ∈ (Monomial.var arity index).set index 0, exponent = 0 := by
  intro exponent he
  rw [List.mem_iff_getElem] at he
  obtain ⟨k, hk, rfl⟩ := he
  rw [List.getElem_set]
  split
  · rfl
  · simp only [Monomial.var, List.getElem_map, List.getElem_range]
    split
    · rename_i hne heq
      exact absurd (by simpa using heq) (Ne.symm hne)
    · rfl

/-- The partial derivatives of a coordinate are the Kronecker delta. -/
theorem evalAt_partial_var (arity index j : Nat) (hj : j < arity) (point : List Rat) :
    evalAt (partialDerivative j (Poly.var arity index)) point = if index = j then 1 else 0 := by
  simp only [Poly.var, partialDerivative, var_getD arity index j hj]
  by_cases h : j = index
  · subst h
    simp [evalAt, monomialValue_zero _ _ (var_set_zero arity j), Rat.add_zero]
  · simp [h, evalAt, Ne.symm h]

theorem dot_zero : ∀ (seed : List Rat) (n : Nat), dot seed (List.replicate n 0) = 0
  | [], _ => by simp [dot]
  | _ :: _, 0 => by simp [dot]
  | _ :: seed, n + 1 => by simp [List.replicate_succ, dot, dot_zero seed n, Rat.mul_zero, Rat.add_zero]

theorem dot_indicator : ∀ (seed : List Rat) (j : Nat), j < seed.length →
    dot seed ((List.range seed.length).map fun i => if i = j then (1 : Rat) else 0) = seed[j]!
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: seed, j, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    cases j with
    | zero =>
      have : ((fun i => if i = 0 then (1 : Rat) else 0) ∘ Nat.succ) = fun _ => 0 := by
        funext i; simp
      simp only [this, List.map_const', dot, dot_zero, List.length_range]
      simp [Rat.mul_one, Rat.add_zero]
    | succ j =>
      have : ((fun i => if i = j + 1 then (1 : Rat) else 0) ∘ Nat.succ) =
          fun i => if i = j then (1 : Rat) else 0 := by
        funext i; simp
      simp only [this, dot, ite_eq_right (Nat.succ_ne_zero j).symm,
        Rat.mul_zero, Rat.zero_add]
      rw [dot_indicator seed j (by simpa using h)]
      simp

/-- **Identity.** Pulling back along the identity of `ℝⁿ` leaves every covector
with `n` components unchanged. -/
theorem cot_identity (arity : Nat) (point seed : List Rat) (h : seed.length = arity) :
    cot (identity arity) point seed = seed := by
  apply List.ext_getElem
  · simp [cot, identity, h]
  · intro j hj _
    have hj' : j < arity := by simpa [cot, identity] using hj
    simp only [cot, identity, List.getElem_map, List.getElem_range, List.map_map]
    have : ((fun image => evalAt (partialDerivative j image) point) ∘ Poly.var arity) =
        fun index => if index = j then (1 : Rat) else 0 := by
      funext index
      exact evalAt_partial_var arity index j hj' point
    rw [this, ← h, dot_indicator seed j (h ▸ hj')]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (h ▸ hj')]

theorem monomialValue_indicator : ∀ (point : List Rat) (j : Nat), j < point.length →
    monomialValue ((List.range point.length).map fun i => if i = j then 1 else 0) point = point[j]!
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: point, j, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    cases j with
    | zero =>
      have : ((fun i => if i = 0 then 1 else 0) ∘ Nat.succ) = fun _ => 0 := by
        funext i; simp
      simp only [this, monomialValue]
      rw [monomialValue_zero _ _ (by intro e he; simp at he; exact he.2.symm)]
      simp [npow]
    | succ j =>
      have : ((fun i => if i = j + 1 then 1 else 0) ∘ Nat.succ) = fun i => if i = j then 1 else 0 := by
        funext i; simp
      simp only [this, monomialValue, ite_eq_right (Nat.succ_ne_zero j).symm, npow_zero, Rat.one_mul]
      rw [monomialValue_indicator point j (by simpa using h)]
      simp

theorem var_eq_indicator (arity index : Nat) :
    Monomial.var arity index = (List.range arity).map fun i => if i = index then 1 else 0 := by
  simp [Monomial.var]

theorem apply_identity (point : List Rat) :
    apply (identity point.length) point = point := by
  apply List.ext_getElem
  · simp [apply, identity]
  · intro j hj _
    have hj' : j < point.length := by simpa [apply, identity] using hj
    simp only [apply, identity, List.getElem_map, List.getElem_range, Poly.var, evalAt,
      var_eq_indicator, monomialValue_indicator point j hj', Rat.one_mul, Rat.add_zero]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj']

theorem pullback_identity (mode : PullbackMode) (point : Program) (seed : Fiber)
    (hpoint : seed.point = coordinates point) (hlength : seed.components.length = (coordinates point).length) :
    pullback mode (.primitive (identity (coordinates point).length)) point (some seed) = some seed := by
  have happly := apply_identity (coordinates point)
  rw [pullback_spec, ite_eq_left ⟨by simpa [Program.eval, happly] using hpoint,
    by simpa [Program.outputArity, identity] using hlength⟩]
  simp only [Program.reverse]
  rw [cot_identity _ _ _ hlength]
  cases seed
  simp_all

end VastitasOracle.SmoothRuntime
