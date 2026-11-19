import VastitasOracle.ExactComplexRing
set_option autoImplicit false

/-! Selected exact real and complex meadow models. Nonzero inverses of Cauchy
classes exist by rational separation on a tail. The numerical adapters use
the separate computable rational-coordinate operations. -/

namespace VastitasOracle.ExactComplex

namespace Sequence

/-- A nonzero quotient class has representatives uniformly separated from zero
on a tail. The Cauchy hypothesis turns arbitrarily late large terms into a
bound for every later term. -/
theorem separated {a : Sequence} (nz : Quotient.mk sequenceSetoid a ≠ ofRat 0) :
    ∃ δ : Rat, 0 < δ ∧ ∃ n, ∀ j ≥ n, δ ≤ (a.term j).abs := by
  classical
  have neg : ¬ Equivalent a (constant 0) := fun equiv => nz (Quotient.sound equiv)
  simp only [Equivalent, Classical.not_forall, not_exists] at neg
  obtain ⟨ε,hε,late⟩ := neg
  have half : (0 : Rat) < ε / 2 := by grind
  obtain ⟨n,hn⟩ := a.cauchy.commonTail half
  obtain ⟨k,hk,far⟩ := late n
  refine ⟨ε/2,half,n,fun j hj => ?_⟩
  have close := hn k hk j hj
  change ¬ Near (a.term k) 0 ε at far
  unfold Near at *
  unfold Rat.abs
  split <;> grind

private theorem near_inv {u v δ ε : Rat} (pos : 0 < δ)
    (hu : δ ≤ u.abs) (hv : δ ≤ v.abs) (h : Near u v (ε*(δ*δ))) :
    Near u⁻¹ v⁻¹ ε := by
  have uz : u ≠ 0 := Rat.abs_pos_iff.mp (by grind)
  have vz : v ≠ 0 := Rat.abs_pos_iff.mp (by grind)
  have iu := Rat.inv_mul_cancel u uz
  have iv := Rat.inv_mul_cancel v vz
  have identity : (u⁻¹-v⁻¹)*(u*v) = v-u := by grind
  have mag := congrArg Rat.abs identity
  rw [abs_mul, abs_mul, Rat.abs_sub_comm (x := v)] at mag
  have step := Rat.mul_le_mul_of_nonneg_right hu (Rat.le_of_lt pos)
  have step' := Rat.mul_le_mul_of_nonneg_left hv (Rat.abs_nonneg (x := u))
  have low : δ*δ ≤ u.abs*v.abs := by grind
  have eps := near_iff_abs.mp h
  apply near_iff_abs.mpr
  apply Rat.lt_of_mul_lt_mul_right (c := δ*δ) _ (Rat.le_of_lt (Rat.mul_pos pos pos))
  have bound := Rat.mul_le_mul_of_nonneg_left low (Rat.abs_nonneg (x := u⁻¹-v⁻¹))
  grind

theorem exists_inverse {a : Sequence} (nz : Quotient.mk sequenceSetoid a ≠ ofRat 0) :
    ∃ y : RR, RR.mul (Quotient.mk sequenceSetoid a) y = (1 : RR) := by
  obtain ⟨δ,pos,k,hk⟩ := separated nz
  let b : Sequence := {
    term := fun i => (a.term i)⁻¹
    cauchy := by
      intro ε hε
      obtain ⟨n,hn⟩ := a.cauchy.commonTail (Rat.mul_pos hε (Rat.mul_pos pos pos))
      exact ⟨max n k, fun j hj =>
        near_inv pos (hk j (by omega)) (hk (max n k) (by omega))
          (hn j (by omega) (max n k) (by omega))⟩ }
  refine ⟨Quotient.mk _ b, Quotient.sound ?_⟩
  intro ε hε
  refine ⟨k,fun j hj => ?_⟩
  have hu : a.term j ≠ 0 := Rat.abs_pos_iff.mp (by have := hk j hj; grind)
  change Near (a.term j*(a.term j)⁻¹) 1 ε
  rw [Rat.mul_inv_cancel _ hu]
  unfold Near
  grind

end Sequence

namespace RR

theorem exists_inverse (a : RR) (nonzero : a ≠ 0) : ∃ y, a*y = 1 := by
  induction a using Quotient.inductionOn with
  | _ a => exact Sequence.exists_inverse nonzero

/-- The mathematical inverse chooses the unique inverse in the nonzero case. -/
noncomputable def inv (a : RR) : RR := by
  classical
  exact if h : a = 0 then 0 else Classical.choose (exists_inverse a h)

theorem inv_zero : inv 0 = 0 := by simp [inv]

theorem mul_inv {a : RR} (h : a ≠ 0) : a * inv a = 1 := by
  classical
  simpa [inv,h] using Classical.choose_spec (exists_inverse a h)

theorem zero_ne_one : (0 : RR) ≠ 1 := fun h => (by decide : (0 : Rat) ≠ 1) (ofRat_injective h)

end RR

private theorem rat_sq_nonneg (r : Rat) : 0 ≤ r*r := by
  by_cases h : 0 ≤ r
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -r := by grind
    have := Rat.mul_nonneg h' h'
    grind

private theorem rat_sq_pos {r δ : Rat} (pos : 0 < δ) (hr : δ ≤ r.abs) : δ*δ ≤ r*r := by
  have h := Rat.mul_le_mul_of_nonneg_right hr (Rat.le_of_lt pos)
  have h' := Rat.mul_le_mul_of_nonneg_left hr (Rat.abs_nonneg (x := r))
  have absSq := abs_mul r r
  rw [Rat.abs_of_nonneg (rat_sq_nonneg r)] at absSq
  grind

private theorem squareSum_left (x y : Sequence)
    (hx : Quotient.mk sequenceSetoid x ≠ ofRat 0) :
    Quotient.mk sequenceSetoid (Sequence.add (x.mul x) (y.mul y)) ≠ ofRat 0 := by
  obtain ⟨δ,pos,k,hk⟩ := x.separated hx
  intro zero
  have hz : Equivalent (Sequence.add (x.mul x) (y.mul y)) (constant 0) := Quotient.exact zero
  obtain ⟨n,hn⟩ := hz (δ*δ) (Rat.mul_pos pos pos)
  let j := max n k
  have near := hn j (Nat.le_max_left ..)
  have xbound := rat_sq_pos pos (hk j (Nat.le_max_right ..))
  have ybound := rat_sq_nonneg (y.term j)
  change Near (x.term j*x.term j + y.term j*y.term j) 0 (δ*δ) at near
  unfold Near at near
  grind

namespace CC

def normSq (x : CC) : RR := x.re*x.re + x.im*x.im

theorem normSq_nonzero (x : CC) (nz : x ≠ 0) : normSq x ≠ 0 := by
  obtain ⟨r,i⟩ := x
  change r*r + i*i ≠ 0
  by_cases h : r = 0
  · have hi : i ≠ 0 := fun eq => nz (eq_of_components h eq)
    rw [Lean.Grind.AddCommMonoid.add_comm (r*r) (i*i)]
    induction i, r using Quotient.inductionOn₂ with
    | _ i r => exact squareSum_left i r hi
  · induction r, i using Quotient.inductionOn₂ with
    | _ r i => exact squareSum_left r i h

noncomputable def inv (x : CC) : CC :=
  ⟨x.re * RR.inv x.normSq, -(x.im * RR.inv x.normSq)⟩

theorem inv_zero : inv 0 = 0 := by
  apply eq_of_components <;> change _ = (0 : RR) <;> simp [inv, normSq] <;> grind

theorem mul_inv {x : CC} (nz : x ≠ 0) : x * inv x = 1 := by
  have cancel := RR.mul_inv (normSq_nonzero x nz)
  unfold normSq at cancel
  apply eq_of_components
  · change x.re*(x.re*_) - x.im*(-(x.im*_)) = (1 : RR)
    unfold normSq
    grind
  · change x.re*(-(x.im*_)) + x.im*(x.re*_) = (0 : RR)
    grind

theorem zero_ne_one : (0 : CC) ≠ 1 := fun h => RR.zero_ne_one (congrArg CC.re h)

end CC
/-- The equational inverse operations accompany the chosen ring reduct. Field
evidence is a proposition about this same model. -/
structure Meadow (α : Type) where
  reduct : Lean.Grind.CommRing α
  inv : α → α
  inv_zero : inv (letI := reduct; (0 : α)) = (letI := reduct; (0 : α))
  inv_inv : ∀ x, inv (inv x) = x
  restricted : ∀ x, reduct.mul x (reduct.mul x (inv x)) = x

def Meadow.IsField {α : Type} (m : Meadow α) : Prop :=
  letI := m.reduct
  (0 : α) ≠ 1 ∧ ∀ x : α, x ≠ 0 → x * m.inv x = 1

private def meadowOfInverse {α : Type} [r : Lean.Grind.CommRing α] (inv : α → α)
    (atZero : inv 0 = 0) (distinct : (0 : α) ≠ 1)
    (cancel : ∀ x : α, x ≠ 0 → x * inv x = 1) : Meadow α where
  reduct := r
  inv := inv
  inv_zero := atZero
  inv_inv x := by
    by_cases h : x = 0
    · simp [h,atZero]
    · have h₁ := cancel x h
      have hn : inv x ≠ 0 := by
        intro zero
        rw [zero] at h₁
        grind
      have h₂ := cancel (inv x) hn
      calc
        inv (inv x) = (x*inv x)*inv (inv x) := by rw [h₁]; grind
        _ = x*(inv x*inv (inv x)) := by grind
        _ = x := by rw [h₂]; grind
  restricted x := by
    change x * (x * inv x) = x
    by_cases h : x = 0
    · simp [h,atZero]; grind
    · rw [cancel x h]; grind

noncomputable def realModel : Meadow RR :=
  meadowOfInverse RR.inv RR.inv_zero RR.zero_ne_one (fun _ => RR.mul_inv)

noncomputable def complexModel : Meadow CC :=
  meadowOfInverse CC.inv CC.inv_zero CC.zero_ne_one (fun _ => CC.mul_inv)

theorem real_isField : realModel.IsField := ⟨RR.zero_ne_one, fun _ => RR.mul_inv⟩
theorem complex_isField : complexModel.IsField := ⟨CC.zero_ne_one, fun _ => CC.mul_inv⟩

theorem ofRat_inv (q : Rat) : ofRat q⁻¹ = RR.inv (ofRat q) := by
  by_cases h : q = 0
  · subst q
    rw [Rat.inv_zero, show ofRat 0 = (0 : RR) from rfl, RR.inv_zero]
  · have nz : ofRat q ≠ (0 : RR) := fun e => h (ofRat_injective e)
    have rational := congrArg ofRat (Rat.mul_inv_cancel q h)
    rw [ofRat_mul] at rational
    change ofRat q * ofRat q⁻¹ = 1 at rational
    have selected := RR.mul_inv nz
    calc
      ofRat q⁻¹ = ofRat q⁻¹ * (ofRat q * RR.inv (ofRat q)) := by rw [selected]; grind
      _ = (ofRat q * ofRat q⁻¹) * RR.inv (ofRat q) := by grind
      _ = RR.inv (ofRat q) := by rw [rational]; grind

theorem QQi.embed_inv (a : QQi) : embed (inv a) = CC.inv (embed a) := by
  have norm : ofRat a.normSq = CC.normSq a.embed := rfl
  apply CC.eq_of_components
  · change ofRat (a.re / a.normSq) = ofRat a.re * RR.inv (CC.normSq a.embed)
    rw [Rat.div_def, ofRat_mul, ofRat_inv, norm]
  · change ofRat (-a.im / a.normSq) = -(ofRat a.im * RR.inv (CC.normSq a.embed))
    rw [Rat.div_def, ofRat_mul, ofRat_inv, ofRat_neg, norm]
    grind

end VastitasOracle.ExactComplex
