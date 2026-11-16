import VastitasKernel.NatureErrorbar
import VastitasOracle.NatureModel

set_option autoImplicit false

/-! Oracle theorems about the declarations of `nature::errorbar` (Stage 6,
#841; ADR 0002 §5): what an accepted calibration, dataset and comparison
(`NatureErrorbar.checkCalibration`, `checkDataset`, `checkComparison`)
guarantee. Mathlib-free; arithmetic is exact over `ℚ`.

* **The test of ADR 0002 §5** (`predictionAt`, `gradientAt`, `varianceAt`,
  `PointConsistent`): at a full point `p` with the measured value `v ± u`,
  the calibrated coordinates `c` with uncertainties `u_c` and the coverage
  factor `k`, the prediction `A(p) = N(p)/D(p)`, its derivative
  `∂A/∂c = (∂_c N·D − N·∂_c D)/D²` and the consistency
  `(A(p) − v)² ≤ k²·(u² + Σ_c (∂A/∂c)²·u_c²)`. No square root is taken.
* **The derivative is exact** (`gradient_exact`): in the dual numbers
  `ℚ[ε]/(ε²)`, `D(p + εe_c)·(A(p) + ε·∂A/∂c(p)) = N(p + εe_c)`, so `∂A/∂c` is
  the derivative of the rational function `N/D` in the coordinate `c`.
* **The kernel computes that test** (`pointTest_eq`, `varianceFold_eq`,
  `pointConsistent_some`, `verdict?_sound`): a recomputed verdict exists only
  when every point is a full point of the chart `D(g)` where `D` does not
  vanish, and it is `consistent` exactly when every point satisfies the
  inequality.
* **The declarations** (`checkCalibration_sound`, `checkDataset_sound`,
  `checkComparison_sound`, C6–C8): an accepted calibration gives at least one
  coordinate, each at most once and below the dimension, with positive
  uncertainties; an accepted dataset has a positive coverage factor, between
  1 and `datasetPoints` points with positive uncertainties, each a full point
  of the chart of the model's prediction; an accepted comparison records the
  fingerprint of its calibration and the recomputed verdict.
* **Staleness** (`comparison_fingerprint`, `checkComparison_stale`,
  `checkComparison_verdict_unique`, C9): an accepted comparison's recorded
  fingerprint is `calibrationFingerprint` of the calibration's canonical
  content, a comparison whose recorded fingerprint differs is rejected, and
  the recorded verdict is determined by the data.
* **In a valid environment** (`comparison_sound`): the prediction of the
  dataset's model is the closed form of the model's transition average, and
  at every point `A(p) = T(p)/g(p)^{2e}` with the trace form of the
  certificate that the average's declaration records and the exponent of its
  branch.

That a changed calibration changes the fingerprint is the property of the
FNV-1a digest, not a theorem (digests collide); first-order propagation and
uncorrelated uncertainties are assumptions of the comparison (ADR 0002 §5).
Calibrations, datasets and comparisons change no `std` validity and no value
(`NatureWeakening`). -/
namespace VastitasOracle.NatureErrorbar

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.SmoothRuntime (evalAt partialDerivative)
open VastitasKernel.NatureErrorbar
open VastitasOracle.SmoothCalculus (Arity Dual dualPoint dual_tangent dot_indicator_map evalIn arity_of_canonical)
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid)
open VastitasOracle.SpectralAverage (AverageValid)

/-! ## The test of ADR 0002 §5 -/

/-- The prediction `A(p) = N(p)/D(p)` of the closed form `N / D`. -/
def predictionAt (numerator denominator : Poly) (p : List Rat) : Rat :=
  evalAt numerator p / evalAt denominator p

/-- The derivative of the prediction in the coordinate `c` at `p`, by the
quotient rule: `(∂_c N·D − N·∂_c D)/D²`. -/
def gradientAt (numerator denominator : Poly) (coordinate : Nat) (p : List Rat) : Rat :=
  (evalAt (partialDerivative coordinate numerator) p * evalAt denominator p -
      evalAt numerator p * evalAt (partialDerivative coordinate denominator) p) /
    (evalAt denominator p * evalAt denominator p)

/-- The first-order variance `u² + Σ_c (∂A/∂c)²·u_c²` of a point with the
uncertainty `u`, over the calibrated coordinates `c` with the uncertainties
`u_c`. -/
def varianceAt (numerator denominator : Poly) (calibrated : List (Nat × Measured)) (p : List Rat)
    (uncertainty : Rat) : Rat :=
  uncertainty * uncertainty +
    (calibrated.map fun c => gradientAt numerator denominator c.1 p * gradientAt numerator denominator c.1 p *
      (c.2.uncertainty * c.2.uncertainty)).sum

/-- **The consistency of a point** (ADR 0002 §5):
`(A(p) − v)² ≤ k²·(u² + Σ_c (∂A/∂c)²·u_c²)`. -/
def PointConsistent (coverage : Rat) (numerator denominator : Poly) (calibrated : List (Nat × Measured))
    (p : List Rat) (measured : Measured) : Prop :=
  (predictionAt numerator denominator p - measured.value) * (predictionAt numerator denominator p - measured.value) ≤
    coverage * coverage * varianceAt numerator denominator calibrated p measured.uncertainty

/-- The coordinate vector `e_c` of `ℚᵐ`. -/
def coordinateVector (m coordinate : Nat) : List Rat :=
  (List.range m).map fun i => if i = coordinate then 1 else 0

/-- **The derivative is exact.** Where `D(p) ≠ 0`, the dual number
`A(p) + ε·∂A/∂c(p)` is the quotient `N/D` at `p + εe_c` in `ℚ[ε]/(ε²)`:
`D(p + εe_c)·(A(p) + ε·∂A/∂c(p)) = N(p + εe_c)`. Since `D(p + εe_c)` is a
unit, `∂A/∂c(p)` is the derivative of `N/D` in the coordinate `c`. -/
theorem gradient_exact {m coordinate : Nat} {numerator denominator : Poly} (hN : Arity m numerator)
    (hD : Arity m denominator) {p : List Rat} (hp : p.length = m) (hc : coordinate < m)
    (hd : evalAt denominator p ≠ 0) :
    evalIn Dual.ofRat denominator (dualPoint p (coordinateVector m coordinate)) *
        ⟨predictionAt numerator denominator p, gradientAt numerator denominator coordinate p⟩ =
      evalIn Dual.ofRat numerator (dualPoint p (coordinateVector m coordinate)) := by
  have hv : (coordinateVector m coordinate).length = m := by simp [coordinateVector]
  rw [dual_tangent hD hp hv, dual_tangent hN hp hv, coordinateVector,
    dot_indicator_map m coordinate (fun j => evalAt (partialDerivative j denominator) p) hc,
    dot_indicator_map m coordinate (fun j => evalAt (partialDerivative j numerator) p) hc]
  refine Dual.ext' ?_ ?_
  · simp only [Dual.mul_re, predictionAt]
    grind
  · simp only [Dual.mul_eps, predictionAt, gradientAt]
    grind

/-! ## The kernel's test -/

/-- The variance as the kernel folds it, from `u²`. -/
def varianceFold (numerator denominator : Poly) (calibrated : List (Nat × Measured)) (p : List Rat)
    (uncertainty : Rat) : Rat :=
  calibrated.foldl (fun sum c => sum + gradientAt numerator denominator c.1 p *
    gradientAt numerator denominator c.1 p * (c.2.uncertainty * c.2.uncertainty)) (uncertainty * uncertainty)

theorem foldl_add_sum {α : Type} (h : α → Rat) :
    ∀ (l : List α) (a : Rat), l.foldl (fun s x => s + h x) a = a + (l.map h).sum
  | [], a => by
    simp only [List.foldl_nil, List.map_nil, List.sum_nil]
    grind
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_sum h l, List.map_cons, List.sum_cons]
    grind

theorem varianceFold_eq (numerator denominator : Poly) (calibrated : List (Nat × Measured)) (p : List Rat)
    (uncertainty : Rat) :
    varianceFold numerator denominator calibrated p uncertainty =
      varianceAt numerator denominator calibrated p uncertainty := by
  unfold varianceFold varianceAt
  exact foldl_add_sum _ _ _

/-- **The kernel's two sides** are `(A(p) − v)²` and `k²·(u² + Σ_c …)`, or
`none` where `D(p) = 0`. -/
theorem pointTest_eq (coverage : Rat) (numerator denominator : Poly) (calibrated : List (Nat × Measured))
    (p : List Rat) (measured : Measured) :
    pointTest coverage numerator denominator calibrated p measured =
      if evalAt denominator p == 0 then none else
        some ((predictionAt numerator denominator p - measured.value) *
            (predictionAt numerator denominator p - measured.value),
          coverage * coverage * varianceFold numerator denominator calibrated p measured.uncertainty) := by
  rfl

/-- **One point of the kernel's verdict.** Where the kernel decides a point,
`D(p) ≠ 0`, and the point is consistent exactly when it satisfies the test of
ADR 0002 §5. -/
theorem pointConsistent_some {coverage : Rat} {numerator denominator : Poly} {calibrated : List (Nat × Measured)}
    {p : List Rat} {measured : Measured} {b : Bool}
    (h : pointConsistent coverage numerator denominator calibrated p measured = some b) :
    evalAt denominator p ≠ 0 ∧ (b = true ↔ PointConsistent coverage numerator denominator calibrated p measured) := by
  unfold pointConsistent at h
  rw [pointTest_eq] at h
  split at h
  · cases h
  · rename_i hd
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨fun hz => hd (by rw [hz]; rfl), ?_⟩
    rw [decide_eq_true_iff, PointConsistent, varianceFold_eq]

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {results : List β}, l.mapM f = some results →
      (∀ a ∈ l, ∃ b ∈ results, f a = some b) ∧ (∀ b ∈ results, ∃ a ∈ l, f a = some b)
  | [], results, h => by
    simp only [List.mapM_nil] at h
    cases h
    simp
  | a :: l, results, h => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | none => simp [hb] at h
    | some b =>
      cases hbs : l.mapM f with
      | none => simp [hb, hbs] at h
      | some bs =>
        simp only [hb, hbs, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨forward, backward⟩ := mapM_some hbs
        constructor
        · intro a' ha'
          rcases List.mem_cons.mp ha' with rfl | ha'
          · exact ⟨b, List.mem_cons_self, hb⟩
          · obtain ⟨b', hb', e⟩ := forward a' ha'
            exact ⟨b', List.mem_cons_of_mem _ hb', e⟩
        · intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb'
          · exact ⟨a, List.mem_cons_self, hb⟩
          · obtain ⟨a', ha', e⟩ := backward b' hb'
            exact ⟨a', List.mem_cons_of_mem _ ha', e⟩

/-- The decision of one point by `pointVerdicts`: a full point `p` on the
chart, and the consistency of `p`. -/
theorem pointVerdict_some {m : Nat} {coverage : Rat} {numerator denominator localize : Poly}
    {calibrated : List (Nat × Measured)} {point : DataPoint} {b : Bool}
    (h : (do
      let p ← fullPoint m calibrated point
      if SmoothRuntime.evalAt localize p == 0 then none
      else pointConsistent coverage numerator denominator calibrated p point.measured) = some b) :
    ∃ p, fullPoint m calibrated point = some p ∧ evalAt localize p ≠ 0 ∧
      pointConsistent coverage numerator denominator calibrated p point.measured = some b := by
  cases hp : fullPoint m calibrated point with
  | none => simp [hp] at h
  | some p =>
    simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · rename_i hg
      exact ⟨p, rfl, fun hz => hg (by rw [hz]; rfl), h⟩

/-- **The recomputed verdict** (C8). When the kernel computes a verdict for a
dataset, every point is a full point `p` of the chart `D(g)` where the
denominator does not vanish, and the verdict is `consistent` exactly when
every point satisfies `(A(p) − v)² ≤ k²·(u² + Σ_c (∂A/∂c)²·u_c²)`. -/
theorem verdict?_sound {m : Nat} {coverage : Rat} {numerator denominator localize : Poly}
    {calibrated : List (Nat × Measured)} {points : List DataPoint} {verdict : Verdict}
    (h : verdict? m coverage numerator denominator localize calibrated points = some verdict) :
    (∀ point ∈ points, ∃ p, fullPoint m calibrated point = some p ∧ evalAt localize p ≠ 0 ∧
      evalAt denominator p ≠ 0) ∧
    (verdict = .consistent ↔ ∀ point ∈ points, ∀ p, fullPoint m calibrated point = some p →
      PointConsistent coverage numerator denominator calibrated p point.measured) := by
  unfold verdict? at h
  cases hv : pointVerdicts m coverage numerator denominator localize calibrated points with
  | none => rw [hv] at h; cases h
  | some results =>
    rw [hv] at h
    simp only [Option.map_some, Option.some.injEq] at h
    unfold pointVerdicts at hv
    obtain ⟨forward, backward⟩ := mapM_some hv
    refine ⟨fun point hpoint => ?_, ?_⟩
    · obtain ⟨b, -, hb⟩ := forward point hpoint
      obtain ⟨p, hp, hg, hc⟩ := pointVerdict_some hb
      exact ⟨p, hp, hg, (pointConsistent_some hc).1⟩
    · subst h
      constructor
      · intro hall point hpoint p hp
        obtain ⟨b, hbmem, hb⟩ := forward point hpoint
        obtain ⟨p', hp', -, hc⟩ := pointVerdict_some hb
        rw [hp] at hp'
        cases hp'
        have htrue : b = true := by
          by_cases hr : results.all id = true
          · exact List.all_eq_true.mp hr b hbmem
          · rw [ite_eq_right hr] at hall
            cases hall
        exact (pointConsistent_some hc).2.mp htrue
      · intro hall
        have hr : results.all id = true := by
          refine List.all_eq_true.mpr fun b hbmem => ?_
          obtain ⟨point, hpoint, hb⟩ := backward b hbmem
          obtain ⟨p, hp, -, hc⟩ := pointVerdict_some hb
          exact (pointConsistent_some hc).2.mpr (hall point hpoint p hp)
        rw [ite_eq_left hr]

/-! ## The declarations -/

/-- **An accepted calibration** (C6): a `calibration` family applied to a
declared smooth object of dimension `m`, at least one calibrated coordinate,
the coordinates distinct indices below `m`, and every uncertainty positive. -/
theorem checkCalibration_sound {env : Environment} {family object : DeclId} {parameters : List (Nat × Measured)}
    {method : CalibrationMethod} {reference revision : String}
    (h : checkCalibration env family object parameters method reference revision = true) :
    isCalibrationFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ m, smoothDimension? env object = some m ∧ parameters ≠ [] ∧ (parameters.map (·.1)).Nodup ∧
        ∀ parameter ∈ parameters, parameter.1 < m ∧ 0 < parameter.2.uncertainty := by
  simp only [checkCalibration, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := SpectralDeclarations.declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hm : smoothDimension? env object with
  | none => rw [hm] at hmatch; cases hmatch
  | some m =>
    rw [hm] at hmatch
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, indicesValid, List.all_eq_true,
      decide_eq_true_eq, measuredValid, List.mem_map] at hmatch
    obtain ⟨⟨hnonempty, hindices, hnodup⟩, hpositive⟩ := hmatch
    refine ⟨m, rfl, hnonempty, hnodup, fun parameter hparameter => ⟨?_, hpositive parameter hparameter⟩⟩
    exact hindices parameter.1 ⟨parameter, hparameter, rfl⟩

theorem fullPoint_length {m : Nat} {calibrated : List (Nat × Measured)} {point : DataPoint} {p : List Rat}
    (h : fullPoint m calibrated point = some p) : p.length = m := by
  unfold fullPoint at h
  dsimp only at h
  split at h
  · cases h
    simp
  · cases h

/-- **An accepted dataset** (C7): a `dataset` family applied to a declared
smooth object of dimension `m`, a positive coverage factor, between 1 and
`datasetPoints` points, a model and a calibration of that object, and every
point with a positive uncertainty and a full point of `m` coordinates on the
chart `D(g)` of the model's prediction, `g(p) ≠ 0`. -/
theorem checkDataset_sound {env : Environment} {family object model calibration : DeclId} {coverage : Rat}
    {points : List DataPoint} (h : checkDataset env family object model calibration coverage points = true) :
    isDatasetFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      0 < coverage ∧ points ≠ [] ∧ points.length ≤ Limits.datasetPoints ∧
      ∃ m modelFamily hamiltonian reading convention prepare observe predicts regime calibrationFamily calibrated
        method reference revision numerator denominator localize,
        smoothDimension? env object = some m ∧
        modelData? env model =
          some (modelFamily, object, hamiltonian, reading, convention, prepare, observe, predicts, regime) ∧
        calibrationData? env calibration = some (calibrationFamily, object, calibrated, method, reference, revision) ∧
        prediction? env model = some (numerator, denominator, localize) ∧
        ∀ point ∈ points, 0 < point.measured.uncertainty ∧
          ∃ p, fullPoint m calibrated point = some p ∧ p.length = m ∧ evalAt localize p ≠ 0 := by
  simp only [checkDataset, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨hdeclared, hcoverage⟩, hnonempty⟩, hlimit⟩, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := SpectralDeclarations.declaredAt_spec hdeclared
  refine ⟨hfamily, happ, hcoverage, hnonempty, hlimit, ?_⟩
  cases hm : smoothDimension? env object with
  | none => rw [hm] at hmatch; cases hmatch
  | some m =>
    cases hmodel : modelData? env model with
    | none => rw [hm, hmodel] at hmatch; cases hmatch
    | some mdata =>
      obtain ⟨modelFamily, modelObject, hamiltonian, reading, convention, prepare, observe, predicts, regime⟩ := mdata
      cases hcal : calibrationData? env calibration with
      | none => rw [hm, hmodel, hcal] at hmatch; cases hmatch
      | some cdata =>
        obtain ⟨calibrationFamily, calibrationObject, calibrated, method, reference, revision⟩ := cdata
        cases hpred : prediction? env model with
        | none => rw [hm, hmodel, hcal, hpred] at hmatch; cases hmatch
        | some pdata =>
          obtain ⟨numerator, denominator, localize⟩ := pdata
          rw [hm, hmodel, hcal, hpred] at hmatch
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hmatch
          obtain ⟨⟨hmodelObject, hcalibrationObject⟩, hpoints⟩ := hmatch
          subst hmodelObject hcalibrationObject
          refine ⟨m, modelFamily, hamiltonian, reading, convention, prepare, observe, predicts, regime,
            calibrationFamily, calibrated, method, reference, revision, numerator, denominator, localize,
            by first | rfl | exact hm, by first | rfl | exact hmodel, by first | rfl | exact hcal,
            by first | rfl | exact hpred, fun point hpoint => ?_⟩
          have hvalid := hpoints point hpoint
          simp only [pointValid, Bool.and_eq_true, measuredValid, decide_eq_true_eq] at hvalid
          obtain ⟨hu, hfull⟩ := hvalid
          refine ⟨hu, ?_⟩
          cases hp : fullPoint m calibrated point with
          | none => rw [hp] at hfull; cases hfull
          | some p =>
            rw [hp] at hfull
            simp only [bne_iff_ne, ne_eq] at hfull
            exact ⟨p, rfl, fullPoint_length hp, hfull⟩

/-- **An accepted comparison** (C8, C9): a `comparison` family applied to a
declared smooth object with coordinates `x₁, …, x_m`, a dataset of that object
under exactly the calibration it names, a calibration of that object whose
fingerprint is the recorded one, and the recorded verdict the one that the
kernel recomputes from the prediction of the dataset's model. -/
theorem checkComparison_sound {env : Environment} {family object dataset calibration : DeclId}
    {fingerprint : String} {verdict : Verdict}
    (h : checkComparison env family object dataset calibration fingerprint verdict = true) :
    isComparisonFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ coordinates datasetFamily model coverage points calibrationFamily calibrated method reference revision
        numerator denominator localize,
        smoothCoordinates? env object = some coordinates ∧
        datasetData? env dataset = some (datasetFamily, object, model, calibration, coverage, points) ∧
        calibrationData? env calibration = some (calibrationFamily, object, calibrated, method, reference, revision) ∧
        fingerprint = calibrationFingerprint coordinates calibrated method reference revision ∧
        prediction? env model = some (numerator, denominator, localize) ∧
        verdict? coordinates.length coverage numerator denominator localize calibrated points = some verdict := by
  simp only [checkComparison, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := SpectralDeclarations.declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hc : smoothCoordinates? env object with
  | none => rw [hc] at hmatch; cases hmatch
  | some coordinates =>
    cases hd : datasetData? env dataset with
    | none => rw [hc, hd] at hmatch; cases hmatch
    | some ddata =>
      obtain ⟨datasetFamily, datasetObject, model, datasetCalibration, coverage, points⟩ := ddata
      cases hcal : calibrationData? env calibration with
      | none => rw [hc, hd, hcal] at hmatch; cases hmatch
      | some cdata =>
        obtain ⟨calibrationFamily, calibrationObject, calibrated, method, reference, revision⟩ := cdata
        rw [hc, hd, hcal] at hmatch
        simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
        obtain ⟨⟨⟨⟨hdatasetObject, hcalibrationObject⟩, hcalibration⟩, hfingerprint⟩, hverdict⟩ := hmatch
        subst hdatasetObject hcalibrationObject hcalibration
        cases hpred : prediction? env model with
        | none => rw [hpred] at hverdict; cases hverdict
        | some pdata =>
          obtain ⟨numerator, denominator, localize⟩ := pdata
          rw [hpred] at hverdict
          simp only [beq_iff_eq] at hverdict
          exact ⟨coordinates, datasetFamily, model, coverage, points, calibrationFamily, calibrated, method,
            reference, revision, numerator, denominator, localize, rfl, rfl, rfl, hfingerprint, hpred, hverdict⟩

/-- **Staleness, accepted side** (C9). The recorded fingerprint of an accepted
comparison is the fingerprint of the canonical content of its calibration. -/
theorem comparison_fingerprint {env : Environment} {family object dataset calibration : DeclId}
    {fingerprint : String} {verdict : Verdict}
    (h : checkComparison env family object dataset calibration fingerprint verdict = true) :
    ∃ coordinates calibrationFamily calibrated method reference revision,
      smoothCoordinates? env object = some coordinates ∧
      calibrationData? env calibration = some (calibrationFamily, object, calibrated, method, reference, revision) ∧
      fingerprint = calibrationFingerprint coordinates calibrated method reference revision := by
  obtain ⟨-, -, coordinates, -, -, -, -, calibrationFamily, calibrated, method, reference, revision, -, -, -, hc, -,
    hcal, hfingerprint, -⟩ := checkComparison_sound h
  exact ⟨coordinates, calibrationFamily, calibrated, method, reference, revision, hc, hcal, hfingerprint⟩

/-- **Staleness, rejected side** (C9). A comparison whose recorded
fingerprint is not the fingerprint of the current calibration is rejected:
after a changed calibration whose fingerprint changed, the old comparison no
longer checks, whatever its verdict. -/
theorem checkComparison_stale {env : Environment} {family object dataset calibration : DeclId}
    {fingerprint : String} {verdict : Verdict} {coordinates : List String} {calibrationFamily calibrationObject : DeclId}
    {calibrated : List (Nat × Measured)} {method : CalibrationMethod} {reference revision : String}
    (hc : smoothCoordinates? env object = some coordinates)
    (hcal : calibrationData? env calibration =
      some (calibrationFamily, calibrationObject, calibrated, method, reference, revision))
    (stale : fingerprint ≠ calibrationFingerprint coordinates calibrated method reference revision) :
    checkComparison env family object dataset calibration fingerprint verdict = false := by
  cases h : checkComparison env family object dataset calibration fingerprint verdict with
  | false => rfl
  | true =>
    obtain ⟨coordinates', calibrationFamily', calibrated', method', reference', revision', hc', hcal', hf⟩ :=
      comparison_fingerprint h
    rw [hc] at hc'
    rw [hcal] at hcal'
    simp only [Option.some.injEq, Prod.mk.injEq] at hc' hcal'
    obtain ⟨-, -, rfl, rfl, rfl, rfl⟩ := hcal'
    subst hc'
    exact absurd hf stale

/-- **The verdict is determined by the data** (C8): two accepted comparisons
of the same dataset under the same calibration record the same verdict, so a
wrong recorded verdict is rejected. -/
theorem checkComparison_verdict_unique {env : Environment} {family object dataset calibration : DeclId}
    {fingerprint : String} {first second : Verdict}
    (hfirst : checkComparison env family object dataset calibration fingerprint first = true)
    (hsecond : checkComparison env family object dataset calibration fingerprint second = true) : first = second := by
  obtain ⟨-, -, coordinates, _, model, coverage, points, _, calibrated, _, _, _, numerator, denominator, localize, hc,
    hd, hcal, -, hpred, hverdict⟩ := checkComparison_sound hfirst
  obtain ⟨-, -, coordinates', _, model', coverage', points', _, calibrated', _, _, _, numerator', denominator',
    localize', hc', hd', hcal', -, hpred', hverdict'⟩ := checkComparison_sound hsecond
  rw [hc] at hc'
  rw [hd] at hd'
  rw [hcal] at hcal'
  simp only [Option.some.injEq, Prod.mk.injEq] at hc' hd' hcal'
  obtain ⟨-, -, rfl, -, rfl, rfl⟩ := hd'
  obtain ⟨-, -, rfl, -, -, -⟩ := hcal'
  subst hc'
  rw [hpred] at hpred'
  simp only [Option.some.injEq, Prod.mk.injEq] at hpred'
  obtain ⟨rfl, rfl, rfl⟩ := hpred'
  rw [hverdict] at hverdict'
  exact Option.some.inj hverdict'

/-! ## In a valid environment -/

/-- The prediction of a model, unfolded: the closed form of its predicted
transition average and the localization of that average's branch. -/
theorem prediction?_sound {env : Environment} {model : DeclId} {numerator denominator localize : Poly}
    (h : prediction? env model = some (numerator, denominator, localize)) :
    ∃ modelFamily object hamiltonian reading convention prepare observe predicts regime averageFamily averageObject
      branch source target certificate branchFamily branchObject spectrum witness exponent quotient,
      modelData? env model =
        some (modelFamily, object, hamiltonian, reading, convention, prepare, observe, predicts, regime) ∧
      transitionAverageData? env predicts =
        some (averageFamily, averageObject, branch, source, target, numerator, denominator, certificate) ∧
      branchData? env branch = some (branchFamily, branchObject, spectrum, localize, witness, exponent, quotient) := by
  cases hm : modelData? env model with
  | none => simp [prediction?, hm] at h
  | some mdata =>
    obtain ⟨modelFamily, object, hamiltonian, reading, convention, prepare, observe, predicts, regime⟩ := mdata
    cases ha : transitionAverageData? env predicts with
    | none => simp [prediction?, hm, ha] at h
    | some adata =>
      obtain ⟨averageFamily, averageObject, branch, source, target, numerator', denominator', certificate⟩ := adata
      cases hb : branchData? env branch with
      | none => simp [prediction?, hm, ha, hb] at h
      | some bdata =>
        obtain ⟨branchFamily, branchObject, spectrum, localize', witness, exponent, quotient⟩ := bdata
        simp [prediction?, hm, ha, hb] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨modelFamily, object, hamiltonian, reading, convention, prepare, observe, predicts, regime,
          averageFamily, averageObject, branch, source, target, certificate, branchFamily, branchObject, spectrum,
          witness, exponent, quotient, by first | rfl | exact hm, by first | rfl | exact ha,
          by first | rfl | exact hb⟩

theorem modelData_lookup {env : Environment} {id family object hamiltonian reading convention predicts : DeclId}
    {prepare observe : Nat} {regime : String}
    (h : modelData? env id =
      some (family, object, hamiltonian, reading, convention, prepare, observe, predicts, regime)) :
    lookup env id = some (.model family object hamiltonian reading convention prepare observe predicts regime) := by
  unfold modelData? at h
  split at h
  · rename_i found
    cases h
    exact found
  · cases h

/-- **Comparisons of a valid environment** (C8, C9, with C2 and C4). A
declared comparison on `X` records the fingerprint of its calibration; its
dataset's model predicts the transition average `N / D` of its own field on
`X`, whose declaration records the certificate with the checked trace form
`T`, of a branch with the chart `D(g)` and the exponent `e`; every
point of the dataset is a full point `p` of `X` on `D(g)`, where
`D(p) ≠ 0` and `A(p) = N(p)/D(p) = T(p)/g(p)^{2e}`; and the recorded verdict is
`consistent` exactly when every point satisfies
`(A(p) − v)² ≤ k²·(u² + Σ_c (∂A/∂c)²·u_c²)`. -/
theorem comparison_sound {env : Environment} (envValid : env.Valid) {id family object dataset calibration : DeclId}
    {fingerprint : String} {verdict : Verdict}
    (found : lookup env id = some (.comparison family object dataset calibration fingerprint verdict)) :
    ∃ coordinates datasetFamily model coverage points calibrationFamily calibrated method reference revision
      numerator denominator localize, ∃ (exponent : Nat) (certificate : AverageCertificate),
      smoothCoordinates? env object = some coordinates ∧
      datasetData? env dataset = some (datasetFamily, object, model, calibration, coverage, points) ∧
      calibrationData? env calibration = some (calibrationFamily, object, calibrated, method, reference, revision) ∧
      fingerprint = calibrationFingerprint coordinates calibrated method reference revision ∧
      prediction? env model = some (numerator, denominator, localize) ∧
      (∃ modelFamily modelObject hamiltonian reading convention prepare observe predicts regime averageFamily
          averageObject branch source target branchFamily branchObject spectrum witness quotient,
        modelData? env model =
          some (modelFamily, modelObject, hamiltonian, reading, convention, prepare, observe, predicts, regime) ∧
        transitionAverageData? env predicts =
          some (averageFamily, averageObject, branch, source, target, numerator, denominator, certificate) ∧
        branchData? env branch = some (branchFamily, branchObject, spectrum, localize, witness, exponent, quotient)) ∧
      (∀ point ∈ points, ∃ p, fullPoint coordinates.length calibrated point = some p ∧
        p.length = coordinates.length ∧ evalAt localize p ≠ 0 ∧ evalAt denominator p ≠ 0 ∧
        predictionAt numerator denominator p = evalAt certificate.trace p / evalAt localize p ^ (2 * exponent)) ∧
      (verdict = .consistent ↔ ∀ point ∈ points, ∀ p, fullPoint coordinates.length calibrated point = some p →
        PointConsistent coverage numerator denominator calibrated p point.measured) := by
  have valid := SpectralDeclarations.valid_of_lookup envValid found
  obtain ⟨-, -, coordinates, datasetFamily, model, coverage, points, calibrationFamily, calibrated, method, reference,
    revision, numerator, denominator, localize, hc, hd, hcal, hfingerprint, hpred, hverdict⟩ :=
    checkComparison_sound valid
  obtain ⟨modelFamily, modelObject, hamiltonian, reading, convention, prepare, observe, predicts, regime, averageFamily,
    averageObject, branch, source, target, certificate, branchFamily, branchObject, spectrum, witness, exponent,
    quotient, hmodel, haverage, hbranch⟩ := prediction?_sound hpred
  obtain ⟨-, -, implementation, coordinates', branchFamily', spectrum', localize', witness', exponent', quotient',
    spectrumFamily, endomorphism, fiber, spectral, endomorphismFamily, module, rows, hobject, hb, -, -, -, hw, ha⟩ :=
    SpectralAverage.transitionAverage_sound envValid (SpectralAverage.transitionAverageData_lookup haverage)
  rw [hbranch] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, -, -, rfl, rfl, rfl, -⟩ := hb
  have hg := arity_of_canonical hw.localizeCanonical
  obtain ⟨hchart, hcons⟩ := verdict?_sound hverdict
  refine ⟨coordinates, datasetFamily, model, coverage, points, calibrationFamily, calibrated, method, reference,
    revision, numerator, denominator, localize, exponent, certificate, hc, hd, hcal, hfingerprint, hpred,
    ⟨modelFamily, modelObject, hamiltonian, reading, convention, prepare, observe, predicts, regime, averageFamily,
      averageObject, branch, source, target, branchFamily, branchObject, spectrum, witness, quotient, hmodel, haverage,
      hbranch⟩, fun point hpoint => ?_, hcons⟩
  obtain ⟨p, hp, hgp, hdp⟩ := hchart point hpoint
  exact ⟨p, hp, fullPoint_length hp, hgp, hdp, (ha.value_at hg hgp).2⟩

end VastitasOracle.NatureErrorbar
