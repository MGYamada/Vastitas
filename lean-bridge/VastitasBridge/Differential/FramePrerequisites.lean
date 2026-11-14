module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false

/-!
# Mathlib prerequisites of the frame comparison

Pure Mathlib statements about ordered frames of `Rⁿ`. A frame is given, as the kernel gives it,
by an `n × n` matrix `P` whose column `j` is vector `j` of the frame in the standard basis, and
a two-sided inverse `Q`. The kernel-facing comparison reads the kernel's list matrices as
Mathlib matrices and applies these lemmas; it cannot be a module itself because it reads the
non-module kernel and Oracle sources.

The ring `R` is any commutative ring: no statement divides. So the statements hold over `ℚ`
and `ℝ`, and also over a polynomial ring, where a frame with a polynomial inverse is a basis of
the free module. Positive definiteness is stated over `ℝ`.

* **A frame is a basis.** `frameBasis P Q hPQ hQP` is a `Basis (Fin n) R (Fin n → R)` whose
  vector `j` is column `j` of `P` (`frameBasis_apply`). Its coordinate map is `v ↦ Q v`
  (`frameBasis_repr`, `frameBasis_equivFun`), and in Mathlib's `Basis.toMatrix` the standard
  basis sees it as `P` (`basisFun_toMatrix_frameBasis`); it sees the standard basis as `Q`
  (`frameBasis_toMatrix_basisFun`).
* **Coordinates of a covector.** In the dual basis, the functional `w ↦ α ⬝ᵥ w`
  (`dotProductEquiv R (Fin n) α`) has coordinates `Pᵀ α`, that is `α ᵥ* P`
  (`frameBasis_dualBasis_repr`,
  `frameBasis_dualBasis_equivFun`), and dual vector `i` is the functional of row `i` of `Q`
  (`frameBasis_dualBasis_apply`).
* **Matrix of a linear map in two frames.** For `f : Rⁿ → Rᵐ` with standard matrix
  `J = LinearMap.toMatrix' f`, `LinearMap.toMatrix` in the source frame `(P, Q)` and the target
  frame `(P', Q')` is `Q' * J * P` (`toMatrix_frameBasis`). The proof is Mathlib's
  `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`.
* **Change of frames.** The transition from frame `b = (P, Q)` to frame `b' = (P', Q')` is
  `T_{b→b'} = Q' * P`. In Mathlib's orientation it is `b'.toMatrix b`, whose column `j` is the
  `b'`-coordinates of vector `j` of `b` (`frameBasis_toMatrix_frameBasis`), and it sends
  `b`-coordinates to `b'`-coordinates (`transition_mulVec`). `transition_self`,
  `transition_trans` and `transition_mul_transition` are `T_{b→b} = 1`,
  `T_{b'→b''} * T_{b→b'} = T_{b→b''}` and `T_{b'→b} * T_{b→b'} = 1`. With `M_{bc} = Q_c * J * P_b`,
  `frameMatrix_change` is `M_{b'c'} = T_{c→c'} * M_{bc} * T_{b'→b}`.
* **Pairing invariance.** `(Pᵀ α) ⬝ᵥ (Q v) = α ⬝ᵥ v` when `P * Q = 1` (`pairing_frame`).
* **Gram matrix in a frame.** `LinearMap.BilinForm.toMatrix` in the frame is `Pᵀ * G * P` for
  the standard matrix `G` (`bilinToMatrix_frameBasis`, `toMatrix_toBilin'_frameBasis`). The
  transport law `G_{b'} = Tᵀ * G_b * T`, with `T = T_{b'→b} = Q * P'`, is
  `bilinToMatrix_frameBasis_transport` for the form and `gram_transport` for the matrices. An
  invertible change keeps a real Gram matrix positive definite (`posDef_frameGram`); a frame
  matrix is invertible (`isUnit_frame`).
* **Polynomial frames.** A ring homomorphism keeps a two-sided inverse
  (`matrix_map_mul_eq_one`). So
  polynomial matrices `P`, `Q` over `MvPolynomial σ ℚ` with `P * Q = Q * P = 1` evaluate to
  mutually inverse matrices at every rational point (`polyFrame_eval`, with the evaluation
  `MvPolynomial.eval x` of `Derivative.lean`) and at every real point (`polyFrame_realEval`).
  `realEval x` evaluates a rational polynomial at a real point as `Frechet.lean` evaluates
  `realPoly`: `eval x (map (algebraMap ℚ ℝ) q)` (`realEval_apply`); it is `aeval x`
  (`realEval_eq_aeval`), and at a rational point it is the cast of the rational value
  (`realEval_ratCast`, `map_realEval_ratCast`).

Checked with Lean 4.35.0 and Mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679.
-/

@[expose] public section

noncomputable section

namespace VastitasBridge.Differential

open Matrix Module

variable {R : Type*} [CommRing R] {n m : ℕ}

/-! ## A frame is a basis -/

/-- **The frame of a matrix.** For `P` with two-sided inverse `Q`, the basis of `Rⁿ` whose
vector `j` is column `j` of `P`. It is the standard basis moved by the automorphism `v ↦ P v`. -/
def frameBasis (P Q : Matrix (Fin n) (Fin n) R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Basis (Fin n) R (Fin n → R) :=
  (Pi.basisFun R (Fin n)).map <| LinearEquiv.ofLinearMap (Matrix.toLin' P) (Matrix.toLin' Q)
    (by rw [← Matrix.toLin'_mul, hPQ, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hQP, Matrix.toLin'_one])

section Frame

variable (P Q : Matrix (Fin n) (Fin n) R) (hPQ : P * Q = 1) (hQP : Q * P = 1)

/-- Vector `j` of the frame is column `j` of `P`. -/
@[simp] theorem frameBasis_apply (j : Fin n) : frameBasis P Q hPQ hQP j = P.col j := by
  simp only [frameBasis, Basis.map_apply, Pi.basisFun_apply, LinearEquiv.coe_ofLinearMap,
    Matrix.toLin'_apply, Matrix.mulVec_single_one]

/-- **The coordinates in the frame are `Q v`.** -/
@[simp] theorem frameBasis_repr (v : Fin n → R) (i : Fin n) :
    (frameBasis P Q hPQ hQP).repr v i = (Q *ᵥ v) i := by
  simp only [frameBasis, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_ofLinearMap,
    LinearEquiv.coe_ofLinearMap, Pi.basisFun_repr, Matrix.toLin'_apply]

theorem frameBasis_equivFun (v : Fin n → R) : (frameBasis P Q hPQ hQP).equivFun v = Q *ᵥ v := by
  funext i
  rw [Basis.equivFun_apply, frameBasis_repr]

/-- The standard basis sees the frame as `P`: `(Pi.basisFun R (Fin n)).toMatrix` has column `j`
equal to vector `j` of the frame. -/
theorem basisFun_toMatrix_frameBasis :
    (Pi.basisFun R (Fin n)).toMatrix (frameBasis P Q hPQ hQP) = P := by
  ext i j
  rw [Basis.toMatrix_apply, Pi.basisFun_repr, frameBasis_apply, Matrix.col_apply]

/-- The frame sees the standard basis as `Q`. -/
theorem frameBasis_toMatrix_basisFun :
    (frameBasis P Q hPQ hQP).toMatrix (Pi.basisFun R (Fin n)) = Q := by
  ext i j
  rw [Basis.toMatrix_apply, frameBasis_repr, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply]

/-! ## Coordinates of a covector -/

/-- Dual vector `i` of the frame is the functional `w ↦ Qᵢ ⬝ᵥ w` of row `i` of `Q`. -/
theorem frameBasis_dualBasis_apply (i : Fin n) :
    (frameBasis P Q hPQ hQP).dualBasis i = dotProductEquiv R (Fin n) (Q i) := by
  refine LinearMap.ext fun w => ?_
  rw [Basis.dualBasis_apply, frameBasis_repr]
  rfl

/-- **The coordinates of a covector are `Pᵀ α`.** In the dual basis of the frame, the functional
`w ↦ α ⬝ᵥ w` has coordinate `i` equal to `(Pᵀ α)ᵢ`, which is `(α ᵥ* P)ᵢ` (`mulVec_transpose`). -/
@[simp] theorem frameBasis_dualBasis_repr (α : Fin n → R) (i : Fin n) :
    (frameBasis P Q hPQ hQP).dualBasis.repr (dotProductEquiv R (Fin n) α) i = (Pᵀ *ᵥ α) i := by
  rw [Basis.dualBasis_repr, frameBasis_apply, Matrix.mulVec_transpose]
  rfl

theorem frameBasis_dualBasis_equivFun (α : Fin n → R) :
    (frameBasis P Q hPQ hQP).dualBasis.equivFun (dotProductEquiv R (Fin n) α) = Pᵀ *ᵥ α := by
  funext i
  rw [Basis.equivFun_apply, frameBasis_dualBasis_repr]

/-! ## The matrix of a linear map in two frames -/

/-- **The matrix of a linear map in two frames is `Q' * J * P`.** For the source frame `(P, Q)`,
the target frame `(P', Q')` and the standard matrix `J = LinearMap.toMatrix' f`. This is
Mathlib's `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` through the standard
bases, with `basisFun_toMatrix_frameBasis` and `frameBasis_toMatrix_basisFun`. -/
theorem toMatrix_frameBasis {P' Q' : Matrix (Fin m) (Fin m) R} (hPQ' : P' * Q' = 1)
    (hQP' : Q' * P' = 1) (f : (Fin n → R) →ₗ[R] (Fin m → R)) :
    LinearMap.toMatrix (frameBasis P Q hPQ hQP) (frameBasis P' Q' hPQ' hQP') f =
      Q' * LinearMap.toMatrix' f * P := by
  rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (frameBasis P Q hPQ hQP)
    (Pi.basisFun R (Fin n)) (frameBasis P' Q' hPQ' hQP') (Pi.basisFun R (Fin m)) f,
    frameBasis_toMatrix_basisFun, basisFun_toMatrix_frameBasis]
  -- `LinearMap.toMatrix` in the standard bases is `LinearMap.toMatrix'` by definition
  -- (`LinearMap.toMatrix_eq_toMatrix'` states it for one index type only).
  rfl

/-! ## Change of frames -/

/-- **The transition is a `Basis.toMatrix`.** The transition `T_{b→b'} = Q' * P` from the frame
`b = (P, Q)` to the frame `b' = (P', Q')` is Mathlib's `b'.toMatrix b`: column `j` is the
`b'`-coordinates of vector `j` of `b`. -/
theorem frameBasis_toMatrix_frameBasis {P' Q' : Matrix (Fin n) (Fin n) R} (hPQ' : P' * Q' = 1)
    (hQP' : Q' * P' = 1) :
    (frameBasis P' Q' hPQ' hQP').toMatrix (frameBasis P Q hPQ hQP) = Q' * P := by
  rw [← Basis.toMatrix_mul_toMatrix (frameBasis P' Q' hPQ' hQP') (Pi.basisFun R (Fin n)),
    frameBasis_toMatrix_basisFun, basisFun_toMatrix_frameBasis]

/-! ## The Gram matrix in a frame -/

/-- **The Gram matrix in a frame is `Pᵀ * G * P`**, for the standard matrix
`G = LinearMap.BilinForm.toMatrix' B`. This is Mathlib's
`LinearMap.BilinForm.toMatrix_mul_basis_toMatrix` from the standard basis. -/
theorem bilinToMatrix_frameBasis (B : LinearMap.BilinForm R (Fin n → R)) :
    LinearMap.BilinForm.toMatrix (frameBasis P Q hPQ hQP) B =
      Pᵀ * LinearMap.BilinForm.toMatrix' B * P := by
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun R (Fin n))
    (frameBasis P Q hPQ hQP) B, LinearMap.BilinForm.toMatrix_basisFun,
    basisFun_toMatrix_frameBasis]

/-- The form `g(v, w) = vᵀ G w` (`Matrix.toBilin'_apply'`) has the Gram matrix `Pᵀ * G * P` in
the frame. -/
theorem toMatrix_toBilin'_frameBasis (G : Matrix (Fin n) (Fin n) R) :
    LinearMap.BilinForm.toMatrix (frameBasis P Q hPQ hQP) (Matrix.toBilin' G) = Pᵀ * G * P := by
  rw [bilinToMatrix_frameBasis, LinearMap.BilinForm.toMatrix'_toBilin']

/-- **The transport law of Gram matrices** for a form: `G_{b'} = Tᵀ * G_b * T` with
`T = T_{b'→b} = Q * P'`, the transition from `b' = (P', Q')` to `b = (P, Q)`. -/
theorem bilinToMatrix_frameBasis_transport {P' Q' : Matrix (Fin n) (Fin n) R}
    (hPQ' : P' * Q' = 1) (hQP' : Q' * P' = 1) (B : LinearMap.BilinForm R (Fin n → R)) :
    LinearMap.BilinForm.toMatrix (frameBasis P' Q' hPQ' hQP') B =
      (Q * P')ᵀ * LinearMap.BilinForm.toMatrix (frameBasis P Q hPQ hQP) B * (Q * P') := by
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (frameBasis P Q hPQ hQP)
    (frameBasis P' Q' hPQ' hQP') B, frameBasis_toMatrix_frameBasis]

end Frame

/-! ## Transition laws as matrix identities

Here `b = (P₀, Q₀)`, `b' = (P₁, Q₁)` and `b'' = (P₂, Q₂)` are frames of one space, and the
transition from `b` to `b'` is `T_{b→b'} = Q₁ * P₀`. Each law names only the hypotheses it uses. -/

/-- **`T_{b→b} = 1`**: the transition from a frame to itself is `Q * P`, which is `1` by the
frame's own hypothesis. Stated so that each of the four transition laws has a name. -/
theorem transition_self {P Q : Matrix (Fin n) (Fin n) R} (hQP : Q * P = 1) : Q * P = 1 :=
  hQP

/-- **`T_{b'→b''} * T_{b→b'} = T_{b→b''}`.** -/
theorem transition_trans {P₀ P₁ Q₁ Q₂ : Matrix (Fin n) (Fin n) R} (h₁ : P₁ * Q₁ = 1) :
    (Q₂ * P₁) * (Q₁ * P₀) = Q₂ * P₀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₁, h₁, Matrix.one_mul]

/-- **`T_{b'→b} * T_{b→b'} = 1`.** -/
theorem transition_mul_transition {P₀ Q₀ P₁ Q₁ : Matrix (Fin n) (Fin n) R} (h₀ : Q₀ * P₀ = 1)
    (h₁ : P₁ * Q₁ = 1) : (Q₀ * P₁) * (Q₁ * P₀) = 1 := by
  rw [transition_trans h₁, h₀]

/-- **The transition sends coordinates to coordinates.** `T_{b→b'} = Q' * P` sends the
`b`-coordinates `Q v` of `v` to its `b'`-coordinates `Q' v`. -/
theorem transition_mulVec {P Q : Matrix (Fin n) (Fin n) R} (hPQ : P * Q = 1)
    (Q' : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : (Q' * P) *ᵥ (Q *ᵥ v) = Q' *ᵥ v := by
  rw [mulVec_mulVec, Matrix.mul_assoc, hPQ, Matrix.mul_one]

/-- **Change of frames of a matrix**: `M_{b'c'} = T_{c→c'} * M_{bc} * T_{b'→b}`, where
`M_{bc} = Q_c * J * P_b` (`toMatrix_frameBasis`) for frames `b = (P_b, Q_b)`, `b'` of the source
and `c = (P_c, Q_c)`, `c'` of the target. -/
theorem frameMatrix_change {Pb Qb Pb' : Matrix (Fin n) (Fin n) R}
    {Pc Qc Qc' : Matrix (Fin m) (Fin m) R} (J : Matrix (Fin m) (Fin n) R) (hb : Pb * Qb = 1)
    (hc : Pc * Qc = 1) : Qc' * J * Pb' = (Qc' * Pc) * (Qc * J * Pb) * (Qb * Pb') := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Pb Qb, hb, Matrix.one_mul, ← Matrix.mul_assoc Pc Qc, hc, Matrix.one_mul]

/-! ## Pairing and Gram transport as matrix identities -/

/-- **The pairing does not depend on the frame.** The covector coordinates `Pᵀ α` paired with
the vector coordinates `Q v` give `α ⬝ᵥ v`. Only `P * Q = 1` is needed. -/
theorem pairing_frame {P Q : Matrix (Fin n) (Fin n) R} (hPQ : P * Q = 1) (α v : Fin n → R) :
    (Pᵀ *ᵥ α) ⬝ᵥ (Q *ᵥ v) = α ⬝ᵥ v := by
  rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, hPQ, one_mulVec]

/-- **The transport law of Gram matrices**: with `G_b = Pᵀ * G * P` and
`T = T_{b'→b} = Q * P'`, `Tᵀ * G_b * T = G_{b'} = P'ᵀ * G * P'`. Only `P * Q = 1` is needed. -/
theorem gram_transport {P Q : Matrix (Fin n) (Fin n) R} (hPQ : P * Q = 1)
    (P' G : Matrix (Fin n) (Fin n) R) : (Q * P')ᵀ * (Pᵀ * G * P) * (Q * P') = P'ᵀ * G * P' := by
  have hT : Qᵀ * Pᵀ = 1 := by rw [← transpose_mul, hPQ, transpose_one]
  simp only [transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul, ← Matrix.mul_assoc Qᵀ Pᵀ, hT, Matrix.one_mul]

/-- **An invertible change keeps a real Gram matrix positive definite.** -/
theorem posDef_frameGram {G P : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (hP : IsUnit P) :
    (Pᵀ * G * P).PosDef := by
  have h := hG.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hP)
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- A frame matrix is invertible, as `posDef_frameGram` needs. -/
theorem isUnit_frame {P Q : Matrix (Fin n) (Fin n) R} (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    IsUnit P :=
  ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩

/-! ## Polynomial frames -/

/-- A ring homomorphism keeps a one-sided inverse of matrices. -/
theorem matrix_map_mul_eq_one {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {P Q : Matrix (Fin n) (Fin n) A} (h : P * Q = 1) : P.map f * Q.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one f (map_zero f) (map_one f)]

variable {σ : Type*}

/-- **A polynomial frame is a frame at every rational point.** If polynomial matrices satisfy
`P * Q = Q * P = 1`, their values `MvPolynomial.eval x` at every rational point are mutually
inverse. -/
theorem polyFrame_eval {P Q : Matrix (Fin n) (Fin n) (MvPolynomial σ ℚ)} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (x : σ → ℚ) :
    P.map (MvPolynomial.eval x) * Q.map (MvPolynomial.eval x) = 1 ∧
      Q.map (MvPolynomial.eval x) * P.map (MvPolynomial.eval x) = 1 :=
  ⟨matrix_map_mul_eq_one _ hPQ, matrix_map_mul_eq_one _ hQP⟩

/-- A rational polynomial evaluated at a real point: its coefficients are mapped to `ℝ`, then it
is evaluated, as `Frechet.lean` evaluates `realPoly`. -/
def realEval (x : σ → ℝ) : MvPolynomial σ ℚ →+* ℝ :=
  (MvPolynomial.eval x).comp (MvPolynomial.map (algebraMap ℚ ℝ))

@[simp] theorem realEval_apply (x : σ → ℝ) (q : MvPolynomial σ ℚ) :
    realEval x q = MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℝ) q) :=
  rfl

theorem realEval_eq_aeval (x : σ → ℝ) (q : MvPolynomial σ ℚ) :
    realEval x q = MvPolynomial.aeval x q := by
  rw [realEval_apply, MvPolynomial.eval_map, MvPolynomial.aeval_def]

/-- At a rational point, the real value is the cast of the rational value. -/
theorem realEval_ratCast (x : σ → ℚ) (q : MvPolynomial σ ℚ) :
    realEval (fun i => (x i : ℝ)) q = ((MvPolynomial.eval x q : ℚ) : ℝ) := by
  rw [realEval_apply]
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem map_realEval_ratCast (x : σ → ℚ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℚ)) :
    P.map (realEval fun i => (x i : ℝ)) = (P.map (MvPolynomial.eval x)).map (algebraMap ℚ ℝ) := by
  ext i j
  simp only [Matrix.map_apply, realEval_ratCast, eq_ratCast]

/-- **A polynomial frame is a frame at every real point.** If polynomial matrices satisfy
`P * Q = Q * P = 1`, their values `realEval x` at every real point are mutually inverse. -/
theorem polyFrame_realEval {P Q : Matrix (Fin n) (Fin n) (MvPolynomial σ ℚ)} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (x : σ → ℝ) :
    P.map (realEval x) * Q.map (realEval x) = 1 ∧ Q.map (realEval x) * P.map (realEval x) = 1 :=
  ⟨matrix_map_mul_eq_one _ hPQ, matrix_map_mul_eq_one _ hQP⟩

end VastitasBridge.Differential
