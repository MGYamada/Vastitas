import VastitasOracle.ExactComplexAdditive
set_option autoImplicit false

/-! Multiplication of rational Cauchy sequences descends to their quotient.
The selected real ring and its complex pair ring both use this multiplication. -/
namespace VastitasOracle.ExactComplex

theorem near_iff_abs {x y ε : Rat} : Near x y ε ↔ (x-y).abs < ε := by
  unfold Near Rat.abs
  split <;> grind

theorem abs_mul (x y : Rat) : (x*y).abs = x.abs*y.abs := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [Rat.abs_of_nonneg hx, Rat.abs_of_nonneg hy, Rat.abs_of_nonneg (Rat.mul_nonneg hx hy)]
  · have hy' : y ≤ 0 := by grind
    have hxy : x*y ≤ 0 := by have := Rat.mul_le_mul_of_nonneg_left hy' hx; grind
    rw [Rat.abs_of_nonneg hx, Rat.abs_of_nonpos hy', Rat.abs_of_nonpos hxy]
    grind
  · have hx' : x ≤ 0 := by grind
    have hxy : x*y ≤ 0 := by have := Rat.mul_le_mul_of_nonneg_right hx' hy; grind
    rw [Rat.abs_of_nonpos hx', Rat.abs_of_nonneg hy, Rat.abs_of_nonpos hxy]
    grind
  · have hx' : 0 ≤ -x := by grind
    have hy' : 0 ≤ -y := by grind
    have hxy := Rat.mul_nonneg hx' hy'
    rw [Rat.abs_of_nonpos (by grind : x ≤ 0), Rat.abs_of_nonpos (by grind : y ≤ 0),
      Rat.abs_of_nonneg (by grind : 0 ≤ x*y)]
    grind

private theorem abs_add_le (x y : Rat) : (x+y).abs ≤ x.abs + y.abs := by
  simp only [Rat.abs]
  split <;> split <;> split <;> grind

private theorem boundedTail (a : Sequence) :
    ∃ bound : Rat, 0 < bound ∧ ∃ n, ∀ j ≥ n, (a.term j).abs ≤ bound := by
  obtain ⟨n,hn⟩ := a.cauchy 1 (by decide)
  refine ⟨(a.term n).abs + 1, by have := Rat.abs_nonneg (x := a.term n); grind, n, ?_⟩
  intro j hj
  have h := near_iff_abs.mp (hn j hj)
  have t := abs_add_le (a.term j-a.term n) (a.term n)
  have e : a.term j-a.term n+a.term n = a.term j := by grind
  rw [e] at t
  grind

private theorem near_mul {a b c d ε A B : Rat}
    (apos : 0 < A) (bpos : 0 < B) (left : a.abs ≤ A) (right : d.abs ≤ B)
    (first : Near a b ((ε/2)/B)) (second : Near c d ((ε/2)/A)) :
    Near (a*c) (b*d) ε := by
  rw [near_iff_abs] at *
  have bound {u v K : Rat} (pos : 0 < K) (hu : u.abs ≤ K) (hv : v.abs < (ε/2)/K) :
      (u*v).abs < ε/2 := by
    rw [abs_mul]
    have h₁ := Rat.mul_le_mul_of_nonneg_right hu (Rat.abs_nonneg (x := v))
    have h₂ := Rat.mul_lt_mul_of_pos_right hv pos
    have h₃ : (ε/2)/K*K = ε/2 := Rat.div_mul_cancel (by grind)
    rw [h₃] at h₂
    grind
  have h₁ := bound apos left second
  have h₂ := bound bpos right first
  have h₃ := abs_add_le (a*(c-d)) (d*(a-b))
  have decomp : a*(c-d) + d*(a-b) = a*c-b*d := by grind
  rw [decomp] at h₃
  grind

private theorem halfOver_pos {ε b : Rat} (hε : 0 < ε) (hb : 0 < b) :
    0 < (ε / 2) / b :=
  (Rat.lt_div_iff hb).mpr (by grind)

namespace Sequence

def mul (x y : Sequence) : Sequence where
  term i := x.term i * y.term i
  cauchy := by
    intro ε pos
    obtain ⟨A, hA, a, ha⟩ := boundedTail x
    obtain ⟨B, hB, b, hb⟩ := boundedTail y
    obtain ⟨m, hm⟩ := x.cauchy.commonTail (halfOver_pos pos hB)
    obtain ⟨n, hn⟩ := y.cauchy.commonTail (halfOver_pos pos hA)
    let k := max (max a b) (max m n)
    have ak : a ≤ k := by dsimp [k]; omega
    have bk : b ≤ k := by dsimp [k]; omega
    have mk : m ≤ k := by dsimp [k]; omega
    have nk : n ≤ k := by dsimp [k]; omega
    exact ⟨k, fun j hj => near_mul hA hB (ha j (by omega)) (hb k bk)
      (hm j (by omega) k mk) (hn j (by omega) k nk)⟩

theorem mul_equivalent {x x' y y' : Sequence} (hx : Equivalent x x') (hy : Equivalent y y') :
    Equivalent (mul x y) (mul x' y') := by
  intro ε pos
  obtain ⟨A, hA, a, ha⟩ := boundedTail x
  obtain ⟨B, hB, b, hb⟩ := boundedTail y'
  obtain ⟨m, hm⟩ := hx _ (halfOver_pos pos hB)
  obtain ⟨n, hn⟩ := hy _ (halfOver_pos pos hA)
  exact ⟨max (max a b) (max m n), fun j hj =>
    near_mul hA hB (ha j (by omega)) (hb j (by omega)) (hm j (by omega)) (hn j (by omega))⟩

end Sequence

namespace RR

def mul (a b : RR) : RR :=
  Quotient.liftOn₂ a b (fun x y => Quotient.mk _ (x.mul y))
    (fun _ _ _ _ hx hy => Quotient.sound (Sequence.mul_equivalent hx hy))

instance : Mul RR := ⟨mul⟩
instance : NatCast RR := ⟨fun n => ofRat n⟩
instance : IntCast RR := ⟨fun n => ofRat n⟩
instance (n : Nat) : OfNat RR n := ⟨ofRat n⟩
instance : SMul Nat RR := ⟨fun n a => ofRat n * a⟩
instance : SMul Int RR := ⟨fun n a => ofRat n * a⟩

private def power (a : RR) : Nat → RR
  | 0 => 1
  | n+1 => power a n * a

instance : HPow RR Nat RR := ⟨power⟩

instance instCommRing : Lean.Grind.CommRing RR where
  add_zero := add_zero
  add_assoc := add_assoc
  add_comm := add_comm
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  mul_comm a b := by
    induction a, b using Quotient.inductionOn₂ with
    | _ x y => exact Sequence.pointwise (fun i => Rat.mul_comm (x.term i) (y.term i))
  mul_assoc a b c := by
    induction a, b, c using Quotient.inductionOn₃ with
    | _ x y z => exact Sequence.pointwise (fun i => Rat.mul_assoc (x.term i) (y.term i) (z.term i))
  mul_one a := by
    induction a using Quotient.inductionOn with
    | _ x => exact Sequence.pointwise (fun i => Rat.mul_one (x.term i))
  zero_mul a := by
    induction a using Quotient.inductionOn with
    | _ x => exact Sequence.pointwise (fun i => Rat.zero_mul (x.term i))
  one_mul a := by
    induction a using Quotient.inductionOn with
    | _ x => exact Sequence.pointwise (fun i => Rat.one_mul (x.term i))
  mul_zero a := by
    induction a using Quotient.inductionOn with
    | _ x => exact Sequence.pointwise (fun i => Rat.mul_zero (x.term i))
  right_distrib a b c := by
    induction a, b, c using Quotient.inductionOn₃ with
    | _ x y z => exact Sequence.pointwise (fun i => Rat.add_mul (x.term i) (y.term i) (z.term i))
  left_distrib a b c := by
    induction a, b, c using Quotient.inductionOn₃ with
    | _ x y z => exact Sequence.pointwise (fun i => Rat.mul_add (x.term i) (y.term i) (z.term i))
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    apply Sequence.pointwise
    intro i
    change ((n+1 : Nat) : Rat) = (n : Rat) + 1
    grind
  neg_zsmul n a := by
    induction a using Quotient.inductionOn with
    | _ x => exact Sequence.pointwise (fun i => by change ((-n : Int) : Rat) * x.term i = -((n : Rat) * x.term i); grind)
  intCast_neg n := by
    apply Sequence.pointwise
    intro i
    change ((-n : Int) : Rat) = -(n : Rat)
    grind

end RR

theorem ofRat_mul (a b : Rat) : ofRat (a*b) = ofRat a * ofRat b := rfl

namespace CC

def mul (x y : CC) : CC :=
  ⟨x.re*y.re - x.im*y.im, x.re*y.im + x.im*y.re⟩
def conjugate (x : CC) : CC := ⟨x.re,-x.im⟩

instance : Mul CC := ⟨mul⟩
instance : NatCast CC := ⟨fun n => ⟨(n : RR),0⟩⟩
instance : IntCast CC := ⟨fun n => ⟨(n : RR),0⟩⟩
instance (n : Nat) : OfNat CC n := ⟨⟨OfNat.ofNat n,0⟩⟩
instance : SMul Nat CC := ⟨fun n a => (Nat.cast n : CC) * a⟩
instance : SMul Int CC := ⟨fun n a => (Int.cast n : CC) * a⟩

private def power (a : CC) : Nat → CC
  | 0 => 1
  | n+1 => power a n * a

instance : HPow CC Nat CC := ⟨power⟩

@[grind =] private theorem mul_re (x y : CC) : (x*y).re = x.re*y.re - x.im*y.im := rfl
@[grind =] private theorem mul_im (x y : CC) : (x*y).im = x.re*y.im + x.im*y.re := rfl
@[grind =] private theorem add_re (x y : CC) : (x+y).re = x.re+y.re := rfl
@[grind =] private theorem add_im (x y : CC) : (x+y).im = x.im+y.im := rfl
@[grind =] private theorem neg_re (x : CC) : (-x).re = -x.re := rfl
@[grind =] private theorem neg_im (x : CC) : (-x).im = -x.im := rfl
@[grind =] private theorem nat_re (n : Nat) : (OfNat.ofNat n : CC).re = (OfNat.ofNat n : RR) := rfl
@[grind =] private theorem nat_im (n : Nat) : (OfNat.ofNat n : CC).im = 0 := rfl
@[grind =] private theorem int_re (n : Int) : (Int.cast n : CC).re = (n : RR) := rfl
@[grind =] private theorem int_im (n : Int) : (Int.cast n : CC).im = 0 := rfl

instance instCommRing : Lean.Grind.CommRing CC where
  add_zero := instAddCommGroup.add_zero
  add_assoc := instAddCommGroup.add_assoc
  add_comm := instAddCommGroup.add_comm
  neg_add_cancel := instAddCommGroup.neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  mul_comm _ _ := eq_of_components (by grind) (by grind)
  mul_assoc _ _ _ := eq_of_components (by grind) (by grind)
  mul_one _ := eq_of_components (by grind) (by grind)
  zero_mul _ := eq_of_components (by grind) (by grind)
  one_mul _ := eq_of_components (by grind) (by grind)
  mul_zero _ := eq_of_components (by grind) (by grind)
  right_distrib _ _ _ := eq_of_components (by grind) (by grind)
  left_distrib _ _ _ := eq_of_components (by grind) (by grind)
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ k := eq_of_components (RR.instCommRing.ofNat_succ k) (by grind)
  neg_zsmul n a := by
    change Int.cast (-n) * a = -(Int.cast n * a)
    exact eq_of_components (by grind) (by grind)
  intCast_neg k := eq_of_components (by grind) (by grind)

end CC

theorem QQi.embed_mul (a b : QQi) : embed (mul a b) = embed a * embed b := by
  apply CC.eq_of_components
  · change ofRat (a.re*b.re - a.im*b.im) = ofRat (a.re*b.re) + -(ofRat (a.im*b.im))
    rw [Rat.sub_eq_add_neg, ofRat_add, ofRat_neg]
  · rfl
theorem QQi.embed_conjugate (a : QQi) : embed (conjugate a) = CC.conjugate (embed a) := rfl

end VastitasOracle.ExactComplex
