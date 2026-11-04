import VastitasBridge.AlgebraicGeometry.Kernel.Substitution
import VastitasOracle.AffineFibers
import VastitasBridge.AlgebraicGeometry.Prerequisites

/-!
# Presented algebras of verified certificates

* `Presented c` is the presented ℚ-algebra `ℚ[x₀, …, xₙ₋₁] ⧸ (relations)` of a certificate, and
  `mk c p` is the class of a kernel polynomial.
* For a certificate that `verify` accepted (`Verified`):
  - the stored basis generates the relation ideal (`Verified.span_basis`);
  - equal classes are exactly equal kernel normal forms (`Verified.normalForm_eq_iff`);
  - every class is the class of a canonical polynomial (`mk_surjective`).
* `verified_of_validAffine` and `verified_of_checkAffine`: every accepted presented declaration
  has a verified certificate.

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

noncomputable section

namespace VastitasBridge.AlgebraicGeometry.Kernel

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.AlgebraBasis
open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {n : ℕ}

/-! ## Presented algebras -/

/-- The presented ℚ-algebra `ℚ[x₀, …, xₙ₋₁] ⧸ (relations)` of a certificate. -/
abbrev Presented (c : Certificate) := MvPolynomial (Fin c.arity) ℚ ⧸ relationIdeal c

/-- The class of a kernel polynomial in the presented algebra. -/
def mk (c : Certificate) (p : Poly) : Presented c := Ideal.Quotient.mk _ (toMv c.arity p)

/-- A certificate that the kernel's `verify` accepted. -/
def Verified (c : Certificate) : Prop := ∃ s s', (verify c).run s = .ok ((), s')

section Verified

variable {c : Certificate}

open VastitasOracle.AlgebraBasis (bind_ok)

lemma Verified.basis_canonical (hc : Verified c) : ∀ g ∈ c.basis, Canonical c.arity g := by
  obtain ⟨_, _, h⟩ := hc
  exact (certificateValid_canonical (VastitasOracle.AlgebraBasis.verify_sound h)).1

lemma Verified.basis_ne_nil (hc : Verified c) : ∀ g ∈ c.basis, g ≠ [] := by
  obtain ⟨_, _, h⟩ := hc
  have hshape := (VastitasOracle.AlgebraBasis.verify_sound h).shape
  simp only [shapeValid, Bool.and_eq_true, List.all_eq_true] at hshape
  intro g hg h0
  have := hshape.1.1.2 g hg
  simp [h0, monic, Poly.leading?] at this

lemma Verified.isGroebnerBasis (hc : Verified c) :
    Buchberger.IsGroebnerBasis degLex (family c.arity c.basis) (relationIdeal c) := by
  obtain ⟨_, _, h⟩ := hc
  exact verify_isGroebnerBasis h

/-- The stored basis generates the relation ideal. -/
theorem Verified.span_basis (hc : Verified c) :
    Ideal.span (Set.range (family c.arity c.basis)) = relationIdeal c := by
  refine hc.isGroebnerBasis.span_eq fun i h0 => ?_
  have hcan := hc.basis_canonical _ (List.get_mem _ i)
  exact hc.basis_ne_nil _ (List.get_mem _ i) ((toMv_eq_zero_iff hcan).1 h0)

/-- Equal classes are exactly equal kernel normal forms. -/
theorem Verified.normalForm_eq_iff (hc : Verified c) {p q : Poly} (hp : Canonical c.arity p)
    (hq : Canonical c.arity q) :
    normalForm c.basis p = normalForm c.basis q ↔ mk c p = mk c q := by
  obtain ⟨_, _, h⟩ := hc
  rw [verify_normalForm_eq_iff h hp hq, mk, mk, Ideal.Quotient.eq]

theorem Verified.mk_normalForm (hc : Verified c) {p : Poly} (hp : Canonical c.arity p) :
    mk c (normalForm c.basis p) = mk c p := by
  obtain ⟨_, _, h⟩ := hc
  obtain ⟨-, hnf⟩ := verify_normalForm h hp
  rw [mk, mk, Ideal.Quotient.eq]
  exact neg_mem_iff.1 (by simpa using hnf.1)

theorem Verified.mk_eq_zero_iff (hc : Verified c) {p : Poly} (hp : Canonical c.arity p) :
    mk c p = 0 ↔ normalForm c.basis p = [] := by
  obtain ⟨_, _, h⟩ := hc
  rw [mk, Ideal.Quotient.eq_zero_iff_mem, verify_mem_iff h hp]

/-- Every element of the presented algebra is the class of a canonical kernel polynomial. -/
theorem mk_surjective (c : Certificate) (x : Presented c) :
    ∃ p, Canonical c.arity p ∧ mk c p = x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨ofMv f, canonical_ofMv f, by rw [mk, toMv_ofMv]⟩

end Verified

/-! ## Accepted declarations -/

section Declarations

open VastitasKernel.AlgebraDeclarations
open VastitasOracle.AlgebraBasis (bind_ok)

/-- A successful `checkAffine` ran `verify` on the object's certificate. -/
theorem verified_of_checkAffine {data : AffineData} {base : Option AffineData} {s s' : ℕ}
    (h : (checkAffine data base).run s = .ok ((), s')) : Verified data.certificate := by
  unfold checkAffine at h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, _, _, h⟩ := bind_ok h
  obtain ⟨_, s₁, hverify, _⟩ := bind_ok h
  exact ⟨_, s₁, hverify⟩

theorem verified_of_validAffineData {data : AffineData} {base : Option AffineData}
    (h : validAffineData data base = true) : Verified data.certificate := by
  obtain ⟨_, hrun⟩ := VastitasOracle.AffineMorphisms.run_isOk h
  exact verified_of_checkAffine hrun

/-- Every accepted presented declaration has a verified certificate. -/
theorem verified_of_validAffine {env : Indexed.Environment} {id implementation : Indexed.DeclId}
    {data : AffineData} (h : Indexed.validAffine env id implementation data = true) :
    Verified data.certificate := by
  unfold Indexed.validAffine at h
  simp only [Bool.and_eq_true] at h
  exact verified_of_validAffineData h.1.2

/-- In a valid environment, every presented entry is an accepted declaration. -/
theorem validAffine_of_affineData {env : Indexed.Environment} (henv : env.Valid)
    {x : Indexed.DeclId} {d : AffineData} (h : Indexed.affineData? env x = some d) :
    ∃ implementation, Indexed.validAffine env x implementation d = true := by
  unfold Indexed.affineData? at h
  split at h
  · rename_i implementation data hl
    simp only [Option.some.injEq] at h
    subst h
    unfold Indexed.lookup at hl
    obtain ⟨entry, hfind, hdecl⟩ := Option.map_eq_some_iff.1 hl
    have hid : entry.id = x := by simpa using List.find?_some hfind
    have hvalid := henv.declarations entry (List.mem_of_find?_eq_some hfind)
    simp only [Indexed.Entry.Valid, hdecl] at hvalid
    exact ⟨implementation, hid ▸ hvalid⟩
  · cases h

/-- In a valid environment, every presented entry has a verified certificate. -/
theorem verified_of_affineData {env : Indexed.Environment} (henv : env.Valid)
    {x : Indexed.DeclId} {d : AffineData} (h : Indexed.affineData? env x = some d) :
    Verified d.certificate := by
  obtain ⟨_, hv⟩ := validAffine_of_affineData henv h
  exact verified_of_validAffine hv

end Declarations

end VastitasBridge.AlgebraicGeometry.Kernel
