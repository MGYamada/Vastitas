import VastitasKernel.SmoothDeclarations

set_option autoImplicit false

/-! Executable regressions for the smooth runtime and the metric certificates
(Stage 3). They exercise the acceptance numbers of the Stage 3 example on the
runtime definitions themselves. These are tests, not proofs. -/
namespace VastitasKernel.SmoothRuntimeRegression

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime VastitasKernel.SmoothDeclarations

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"smooth runtime regression failed: {label}")

private def v (arity index : Nat) : Poly := Poly.var arity index

/-- `f(t) = (t, t²)` from the line to the plane. -/
private def f : Program := .primitive ⟨1, [], [v 1 0, Poly.pow 1 (v 1 0) 2]⟩
/-- `g(x, y) = x² + y` from the plane to the line. -/
private def g : Program := .primitive ⟨2, [], [Poly.add (Poly.pow 2 (v 2 0) 2) (v 2 1)]⟩
/-- The composite `2t²`, declared by hand. -/
private def gf : Program := .primitive ⟨1, [], [Poly.scale 2 (Poly.pow 1 (v 1 0) 2)]⟩
private def sq : Program := .primitive ⟨1, [], [Poly.pow 1 (v 1 0) 2]⟩
private def shearA : Program := .primitive ⟨2, [], [Poly.add (v 2 0) (v 2 1), v 2 1]⟩
private def shearB : Program := .primitive ⟨2, [], [v 2 0, Poly.add (v 2 0) (v 2 1)]⟩

private def x : Program := intPoint [3]
private def fx : Program := .compose f x
private def seed (point : Program) (components : List Rat) : FiberValue :=
  some ⟨coordinates point, components⟩
private def eta : FiberValue := seed (.compose g fx) [1]
private def stepwise : FiberValue := pullback .saved f x (pullback .saved g fx eta)

#eval check "the seed lies over g(f(3)) = 18" (eta == some ⟨[18], [1]⟩)
#eval check "stepwise pullback is 12 at 3" (stepwise == some ⟨[3], [12]⟩)
#eval check "composite program agrees"
  (fiberEqual stepwise (pullback .saved (.compose g f) x eta))
#eval check "composite as one primitive agrees"
  (fiberEqual stepwise (pullback .saved (composite (.compose g f)) x eta))
#eval check "declared composite agrees and denotes the same map"
  (fiberEqual stepwise (pullback .saved gf x eta) && same (.compose g f) gf)
#eval check "recomputed forward values agree"
  (fiberEqual stepwise (pullback .recomputed (.compose g f) x eta))
#eval check "the first-class tape agrees"
  (fiberEqual stepwise (backward (linearize (.compose g f) x) eta))
#eval check "the tape keeps the intermediate point f(3) = (3, 9)"
  ((linearize (.compose g f) x).steps.map (·.input) == [[3], [3, 9]])
#eval check "compose builds a node and never the composite"
  (Program.compose g f != composite (.compose g f))
#eval check "the result lies over x" (fiberAt stepwise x && !fiberAt stepwise (intPoint [4]))
#eval check "a seed at 17 fails" (pullback .saved (.compose g f) x (some ⟨[17], [1]⟩) == none)
#eval check "a wrong intermediate basepoint propagates the failure"
  (pullback .saved f x (pullback .saved g (.compose f (intPoint [2])) eta) == none)
#eval check "a tape from 3 rejects a seed at sq(4) = 16"
  (backward (linearize sq x) (seed (.compose sq (intPoint [4])) [1]) == none)
#eval check "a wrong component count fails" (pullback .saved g fx (some ⟨[18], [1, 0]⟩) == none)
#eval check "the failure value reads (0, 0)"
  (component (pullback .saved (.compose g f) x (some ⟨[17], [1]⟩)) 0 == (0, 0))
#eval check "the failure value equals nothing" (!fiberEqual none none)
#eval check "a component of 12 reads (12, 1)" (component stepwise 0 == (12, 1))

private def o : Program := intPoint [0, 0]
#eval check "B ∘ A pulls dx back to (1, 1)"
  (pullback .saved (.compose shearB shearA) o (seed o [1, 0]) == some ⟨[0, 0], [1, 1]⟩)
#eval check "A ∘ B pulls dx back to (2, 1)"
  (pullback .saved (.compose shearA shearB) o (seed o [1, 0]) == some ⟨[0, 0], [2, 1]⟩)
#eval check "identity" (cot (identity 3) [1, 2, 3] [4, 5, 6] == [4, 5, 6])

private def p : Program := intPoint [1, 2]
private def dg : FiberValue := differential g p
#eval check "dg = (2, 1) at (1, 2)" (dg == some ⟨[1, 2], [2, 1]⟩)

-- Euclid, Skew and Lorentz, with kernel-computed certificates.
private def euclid : Matrix := [[1, 0], [0, 1]]
private def skew : Matrix := [[2, 1], [1, 1]]
private def lorentz : Matrix := [[1, 0], [0, -1]]
private def inverseOf (gram : Matrix) : Matrix :=
  match certifyNondegenerate 2 gram with
  | .ok inverse => inverse
  | .error _ => []
#eval check "Skew has the exact inverse ((1, -1), (-1, 2))" (inverseOf skew == [[1, -1], [-1, 2]])
#eval check "Euclid gradient (2, 1)" (sharp (inverseOf euclid) dg == some ⟨[1, 2], [2, 1]⟩)
#eval check "Skew gradient (1, 0)" (sharp (inverseOf skew) dg == some ⟨[1, 2], [1, 0]⟩)
#eval check "Lorentz gradient (2, -1)" (sharp (inverseOf lorentz) dg == some ⟨[1, 2], [2, -1]⟩)
#eval check "flat (5, -7) under Skew is (3, -2), and sharp undoes it"
  (flat skew (vector p [5, -7]) == some ⟨[1, 2], [3, -2]⟩ &&
    sharp (inverseOf skew) (flat skew (vector p [5, -7])) == vector p [5, -7])
#eval check "dg(grad) = Skew(grad, grad) = 2" (pairing dg (sharp (inverseOf skew) dg) == (2, 1))

private def code {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error e => e.code
#eval check "diag(1, 0) is not nondegenerate" (code (certifyNondegenerate 2 [[1, 0], [0, 0]]) == "E_METRIC")
#eval check "diag(1, -1) is nondegenerate" (code (certifyNondegenerate 2 lorentz) == "ok")
#eval check "diag(1, -1) is not Riemannian" (code (certifyRiemannian 2 lorentz) == "E_METRIC")
#eval check "Euclid and Skew are Riemannian"
  (code (certifyRiemannian 2 euclid) == "ok" && code (certifyRiemannian 2 skew) == "ok")
#eval check "an asymmetric form is rejected" (code (certifyNondegenerate 2 [[1, 2], [0, 1]]) == "E_METRIC")
#eval check "a wrong-size form is rejected" (code (certifyNondegenerate 2 [[1]]) == "E_METRIC")
#eval check "a row swap needs pivoting"
  (code (certifyNondegenerate 3 [[0, 1, 0], [1, 0, 0], [0, 0, 3]]) == "ok")
#eval check "a 3 × 3 positive definite form is Riemannian"
  (code (certifyRiemannian 3 [[4, 2, 2], [2, 5, 3], [2, 3, 6]]) == "ok")
#eval check "16 dimensions are accepted, 17 are a limit"
  (code (checkObject 16 ((List.range 16).map toString)) == "ok" &&
    code (checkObject 17 ((List.range 17).map toString)) == "E_LIMIT")
#eval check "coordinates must match the dimension and be distinct"
  (code (checkObject 2 ["t"]) == "E_SMOOTH" && code (checkObject 2 ["t", "t"]) == "E_SMOOTH")
#eval check "a smooth map uses its source coordinates and has no relations"
  (code (checkMap 1 2 ⟨1, [], [v 1 0, v 1 0]⟩) == "ok" &&
    code (checkMap 2 1 ⟨1, [], [v 1 0]⟩) == "E_SMOOTH" &&
    code (checkMap 1 1 ⟨1, [v 1 0], [v 1 0]⟩) == "E_SMOOTH" &&
    code (checkMap 1 2 ⟨1, [], [v 1 0]⟩) == "E_SMOOTH")

end VastitasKernel.SmoothRuntimeRegression
