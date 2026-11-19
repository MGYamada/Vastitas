import VastitasOracle.ExactComplex

set_option autoImplicit false

namespace VastitasOracle.ExactComplex

/-- Beyond a common threshold any two terms are within ε, even when neither
term is the anchor supplied by the definition of Cauchy. -/
theorem Cauchy.commonTail {a : Nat → Rat} (h : Cauchy a) {ε : Rat} (pos : 0 < ε) :
    ∃ n, ∀ j ≥ n, ∀ k ≥ n, Near (a j) (a k) ε := by
  obtain ⟨n,hn⟩ := h (ε / 2) (by grind)
  refine ⟨n, fun j hj k hk => ?_⟩
  have left := hn j hj
  have right := hn k hk
  unfold Near at *
  grind

private theorem near_pair_add {a b c d ε : Rat}
    (first : Near a b (ε / 2)) (second : Near c d (ε / 2)) :
    Near (a+c) (b+d) ε := by
  unfold Near at *
  grind

private theorem near_pair_neg {a b ε : Rat} (h : Near a b ε) : Near (-a) (-b) ε := by
  unfold Near at *
  grind

namespace Sequence

def add (a b : Sequence) : Sequence where
  term i := a.term i + b.term i
  cauchy := by
    intro ε pos
    have half : 0 < ε/2 := by grind
    obtain ⟨n,hn⟩ := a.cauchy.commonTail half
    obtain ⟨m,hm⟩ := b.cauchy.commonTail half
    exact ⟨max n m, fun j hj =>
      near_pair_add (hn j (by omega) (max n m) (by omega))
        (hm j (by omega) (max n m) (by omega))⟩

def neg (a : Sequence) : Sequence where
  term i := -a.term i
  cauchy := by
    intro ε pos
    obtain ⟨n,hn⟩ := a.cauchy ε pos
    exact ⟨n, fun j hj => near_pair_neg (hn j hj)⟩

theorem add_equivalent {a a' b b' : Sequence} (ha : Equivalent a a') (hb : Equivalent b b') :
    Equivalent (add a b) (add a' b') := by
  intro ε pos
  have half : 0 < ε/2 := by grind
  obtain ⟨n,hn⟩ := ha (ε/2) half
  obtain ⟨m,hm⟩ := hb (ε/2) half
  exact ⟨max n m, fun j hj => near_pair_add (hn j (by omega)) (hm j (by omega))⟩

theorem neg_equivalent {a b : Sequence} (h : Equivalent a b) : Equivalent (neg a) (neg b) := by
  intro ε pos
  obtain ⟨n,hn⟩ := h ε pos
  exact ⟨n, fun j hj => near_pair_neg (hn j hj)⟩

theorem pointwise {a b : Sequence} (equal : ∀ i, a.term i = b.term i) :
    Quotient.mk sequenceSetoid a = Quotient.mk sequenceSetoid b := by
  apply Quotient.sound
  intro ε pos
  refine ⟨0, fun j _ => ?_⟩
  unfold Near
  rw [equal j]
  grind

end Sequence

namespace RR

def add (a b : RR) : RR :=
  Quotient.liftOn₂ a b (fun x y => Quotient.mk _ (x.add y))
    (fun _ _ _ _ hx hy => Quotient.sound (Sequence.add_equivalent hx hy))

def neg (a : RR) : RR :=
  Quotient.liftOn a (fun x => Quotient.mk _ x.neg)
    (fun _ _ hx => Quotient.sound (Sequence.neg_equivalent hx))

theorem add_zero (a : RR) : add a (ofRat 0) = a := by
  induction a using Quotient.inductionOn with
  | _ a => exact Sequence.pointwise (fun i => Rat.add_zero (a.term i))

theorem add_comm (a b : RR) : add a b = add b a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact Sequence.pointwise (fun i => Rat.add_comm (a.term i) (b.term i))

theorem add_assoc (a b c : RR) : add (add a b) c = add a (add b c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c => exact Sequence.pointwise (fun i => Rat.add_assoc (a.term i) (b.term i) (c.term i))

theorem neg_add_cancel (a : RR) : add (neg a) a = ofRat 0 := by
  induction a using Quotient.inductionOn with
  | _ a => exact Sequence.pointwise (fun i => by change -a.term i + a.term i = 0; grind)

instance instAddCommGroup : Lean.Grind.AddCommGroup RR where
  zero := ofRat 0
  add := add
  neg := neg
  sub a b := add a (neg b)
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl

end RR

theorem ofRat_add (a b : Rat) : ofRat (a + b) = ofRat a + ofRat b := rfl

theorem ofRat_neg (a : Rat) : ofRat (-a) = -ofRat a := rfl

namespace CC

def zero : CC := ⟨ofRat 0, ofRat 0⟩
def add (x y : CC) : CC := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : CC) : CC := ⟨-x.re, -x.im⟩

theorem eq_of_components {x y : CC} (real : x.re = y.re) (imag : x.im = y.im) : x = y := by
  cases x
  cases y
  cases real
  cases imag
  rfl

instance instAddCommGroup : Lean.Grind.AddCommGroup CC where
  zero := zero
  add := add
  neg := neg
  sub a b := add a (neg b)
  add_zero x := eq_of_components (RR.add_zero x.re) (RR.add_zero x.im)
  add_comm x y := eq_of_components (RR.add_comm x.re y.re) (RR.add_comm x.im y.im)
  add_assoc x y z := eq_of_components (RR.add_assoc x.re y.re z.re) (RR.add_assoc x.im y.im z.im)
  neg_add_cancel x := eq_of_components (RR.neg_add_cancel x.re) (RR.neg_add_cancel x.im)
  sub_eq_add_neg _ _ := rfl

end CC

namespace QQi

theorem embed_zero : embed ⟨0,0⟩ = 0 := rfl

theorem embed_add (a b : QQi) : embed (add a b) = embed a + embed b := rfl

theorem embed_neg (a : QQi) : embed (neg a) = -embed a := rfl

end QQi
end VastitasOracle.ExactComplex
