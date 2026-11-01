import VastitasOracle.PolynomialCotangent

/-! Official-kernel regression examples for the mathematical polynomial fragment.
The failed elaborations below test this API's types, not production Core rejection.
`decide +kernel` reduces exact rational statements in the kernel; no native reflection. -/
namespace VastitasOracle.PolynomialCotangent.Regression

private def A : Plane := ⟨"A2/A"⟩
private def B : Plane := ⟨"A2/B"⟩
private def C : Plane := ⟨"A2/C"⟩
private def origin : Point A := ⟨coordinates 0 0⟩
private def seed : Cotangent origin := ⟨coordinates 1 0⟩
private def u : Polynomial := .var 0
private def v : Polynomial := .var 1

private def pair (p q : Polynomial) : Axis → Polynomial := fun i => if i = 0 then p else q

-- Identity holds for every seed, including exact nonintegral coordinates.
example (p : Point A) (s : Cotangent p) : pullback (.identity A) p s = s :=
  pullback_identity p s

-- The two noncommuting endomorphisms required by #192: both fix the same origin.
private def f : PolynomialMap A A := ⟨pair (.add u v) v⟩
private def g : PolynomialMap A A := ⟨pair u (.add u v)⟩

private theorem f_origin : f.applyPoint origin = origin := by
  apply Point.ext
  apply coordinates_ext <;> decide +kernel

private theorem g_origin : g.applyPoint origin = origin := by
  apply Point.ext
  apply coordinates_ext <;> decide +kernel

private def fPull (s : Cotangent origin) : Cotangent origin :=
  pullback f origin (s.transport f_origin.symm)

private def gPull (s : Cotangent origin) : Cotangent origin :=
  pullback g origin (s.transport g_origin.symm)

theorem correct_order_value : fPull (gPull seed) = ⟨coordinates 1 1⟩ := by
  apply Cotangent.ext
  simp only [fPull, gPull, pullback]
  simp only [Cotangent.transport_components]
  apply coordinates_ext <;> decide +kernel

theorem reversed_order_value : gPull (fPull seed) = ⟨coordinates 2 1⟩ := by
  apply Cotangent.ext
  simp only [fPull, gPull, pullback]
  simp only [Cotangent.transport_components]
  apply coordinates_ext <;> decide +kernel

-- Both sides have exactly the SAME type. Endpoint rejection cannot detect this.
theorem reversed_order_is_false : fPull (gPull seed) ≠ gPull (fPull seed) := by
  rw [correct_order_value, reversed_order_value]
  intro h
  have impossible : (1 : Rat) = 2 := congrArg (fun s => s.components 0) h
  exact (by decide +kernel : (1 : Rat) ≠ 2) impossible

theorem shear_composite_value :
    pullback (g.comp f) origin ⟨coordinates 1 0⟩ = fPull (gPull seed) := by
  rw [correct_order_value]
  apply Cotangent.ext
  apply coordinates_ext <;> decide +kernel

-- Nonlinear maps force derivatives to be evaluated at the actual intermediate
-- point (7,6), not the source point (2,3). Distinct nominal endpoints are retained.
private def nonlinearF : PolynomialMap A B := ⟨pair (.add (.mul u u) v) (.mul u v)⟩
private def nonlinearG : PolynomialMap B C := ⟨pair (.add u (.mul v v)) (.mul u v)⟩
private def p : Point A := ⟨coordinates 2 3⟩
private def nonlinearSeed : Cotangent ((nonlinearG.comp nonlinearF).applyPoint p) :=
  ⟨coordinates 3 5⟩

example : (nonlinearF.applyPoint p).coordinates = coordinates 7 6 := by
  apply coordinates_ext <;> decide +kernel

example : ((nonlinearG.comp nonlinearF).applyPoint p).coordinates = coordinates 43 42 := by
  apply coordinates_ext <;> decide +kernel

theorem nonlinear_composition :
    pullback (nonlinearG.comp nonlinearF) p nonlinearSeed =
      pullback nonlinearF p (pullback nonlinearG (nonlinearF.applyPoint p)
        (nonlinearSeed.transport (PolynomialMap.at_comp nonlinearG nonlinearF p))) :=
  pullback_comp nonlinearG nonlinearF p nonlinearSeed

theorem nonlinear_value :
    pullback (nonlinearG.comp nonlinearF) p nonlinearSeed = ⟨coordinates 345 175⟩ := by
  apply Cotangent.ext
  apply coordinates_ext <;> decide +kernel

-- Coefficients, points and seeds are truly rational, not just integer examples.
private def rationalMap : PolynomialMap A B :=
  ⟨pair (.mul (.constant (1 / 2)) (.mul u u)) v⟩

example : pullback rationalMap ⟨coordinates (2 / 3) (3 / 4)⟩
    ⟨coordinates (3 / 2) (-1 / 3)⟩ = ⟨coordinates 1 (-1 / 3)⟩ := by
  apply Cotangent.ext
  apply coordinates_ext <;> decide +kernel

-- Differential invariance under actual commutative-ring relations.
example (x : Coordinates2) (i : Axis) :
    ((Polynomial.mul u (.add u v)).derivative i).eval x =
      ((Polynomial.add (.mul u u) (.mul u v)).derivative i).eval x :=
  (Polynomial.equivalent_jet (.mul_add u u v) x).2 i

-- Endpoint and basepoint mutations: the bodies must fail to elaborate. If an
-- index were erased, `fail_if_success` would itself fail this regression file.
example : True := by
  fail_if_success
    have : PolynomialMap A B := nonlinearF.comp nonlinearF
  fail_if_success
    have : Point B := p
  fail_if_success
    have : Cotangent p := pullback nonlinearF p
      (⟨coordinates 3 5⟩ : Cotangent (⟨coordinates 7 6⟩ : Point C))
  fail_if_success
    have : Cotangent p := pullback nonlinearF p
      (⟨coordinates 3 5⟩ : Cotangent (⟨coordinates 2 3⟩ : Point B))
  -- The point index itself is preserved even on the SAME nominal plane.
  fail_if_success
    have : Cotangent origin := (⟨coordinates 1 0⟩ : Cotangent p)
  exact True.intro

-- Even a correctly shaped function is not derivative evidence by itself.
private def zeroRule (x : Point A) (_ : Cotangent ((PolynomialMap.identity A).applyPoint x)) :
    Cotangent x := ⟨coordinates 0 0⟩

example : True := by
  fail_if_success
    have : VerifiedRule (PolynomialMap.identity A) := zeroRule
  fail_if_success
    have : VerifiedRule (PolynomialMap.identity A) := pullback (.identity A)
  exact True.intro

-- The forged zero derivative for identity cannot have the required certificate.
theorem zero_rule_cannot_be_verified :
    ¬ ∃ rule : VerifiedRule (PolynomialMap.identity A), rule.run = zeroRule := by
  rintro ⟨rule, same⟩
  have h := rule.correct origin seed
  rw [same, pullback_identity] at h
  have impossible : (0 : Rat) = 1 := congrArg (fun s => s.components 0) h
  exact (by decide +kernel : (0 : Rat) ≠ 1) impossible

-- A proof-carrying rule works through the same contract; no trusted flag exists.
example : (canonicalRule (PolynomialMap.identity A)).run origin seed = seed :=
  pullback_identity origin seed

end VastitasOracle.PolynomialCotangent.Regression
