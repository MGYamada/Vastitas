import VastitasOracle.SpectralCore

set_option autoImplicit false

/-! Oracle theorems about the dephased transition averages of Stage 6 (#841;
`std::linalg::spectral`, ADR 0001 §13): what an accepted
`transition_average(B, from = i, to = j) = ratio(N, D)`
(`SpectralDeclarations.checkAverage`, `checkTransitionAverage`) guarantees
about its data, and what the runtime observation `average_at`
(`SpectralRuntime.averageAt`) computes. Mathlib-free; every statement over a
ring holds in every `Lean.Grind.CommRing` that receives `ℚ`
(`SmoothCalculus.RatHom`), so that the bridge can instantiate it at `ℝ`.

* **Budgeted computations are plain computations** (`divideT_ok`,
  `traceForm_ok`, `averageTrace_ok`, `averageIdentities_ok`): the integrand
  `F = adj[j, i]·adj[i, j]·W²` (`plainIntegrand`), its reduction by the monic
  `χ` (`plainDivideT`, `averageReduction`) and the trace form
  `T = Σ_{d < n} r_d·tr(Hᵈ)`, `tr(H⁰) = n` (`powerTrace`, `plainTraceForm`)
  are the unbudgeted computations of the check.
* **The certificate** (`AverageValid`, `checkAverage_sound`): an accepted
  average has a symmetric field, basis indices below the rank `n`, canonical
  `N` and `D ≠ 0` of arity `m`, a canonical stored `T` and unit quotient, and
  satisfies as exact polynomial identities
  1. `F − Q_F·χ − r = 0` with `(Q_F, r)` the reduction of `F` and
     `deg_t r < n`;
  2. `T = Σ_{d < n} r_d·tr(Hᵈ)`, the trace of `r` on `A[t]/χ`;
  3. `N·g^{2e} − D·T = 0`, the closed form;
  4. `D·Q − g^k = 0` with `k ≤ unitBound D`, so `D` is a unit on `D(g)`.
* **At a point of a ring** (`AverageValid.integrand_at`, `reduction_at`,
  `remainder_at`, `trace_at`, `closedForm_at`, `unit_at`): the identities
  evaluated; at a zero `(x, t)` of `χ` the integrand is the remainder,
  `F(x, t) = Σ_{d < n} r_d(x) tᵈ` (`integrand_at_root`), and with the gap
  certificate `F(x, t)·χ′(x, t)² = adj[j, i]·adj[i, j]·g(x)^{2e}`
  (`integrand_mul_slope_sq`): the products of the entries of the
  eigenprojector `adj/χ′` times `g^{2e}`.
* **At a rational point of the chart** (`AverageValid.value_at`,
  `averageAt_on_chart`, `averageAt_off_chart`): where `g(p) ≠ 0`,
  `D(p) ≠ 0` and `N(p)/D(p) = T(p)/g(p)^{2e}`, and the observation is that
  rational, never the failure pair `(0, 0)`; where `g(p) = 0` it is `(0, 0)`,
  whatever the closed form.
* **The declarations** (`checkTransitionAverage_sound`,
  `transitionAverage_sound`, `DeclaredAverage.checked`): an accepted
  transition average names a branch whose spectrum and gap certificate are
  valid for the rows of a symmetric endomorphism, and satisfies
  `AverageValid` with that data; an embedded `AverageRef` of a valid binding
  is its declaration.
* **Accepted Core** (`core_spectral_average_at`, `accepted_average_at`): an
  accepted `average_at(p, average = A)` evaluates, one unit of fuel later, to
  `SpectralRuntime.averageAt g N D p` with the declared data, which is
  `N(p)/D(p) = T(p)/g(p)^{2e}` on the chart and `(0, 0)` off it.

Proved for all inputs. That the trace form is `Σ_k P_k[j, i]²` for a real
symmetric field with simple spectrum is the bridge statement
(`VastitasBridge.Spectral.Average`). -/
namespace VastitasOracle.SpectralAverage

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.AlgebraRuntime
open VastitasKernel.SmoothRuntime (evalAt coordinates ratPair Program)
open VastitasKernel.SpectralRuntime (liftT extend fiberExponent degT tCoefficient)
open VastitasKernel.SpectralDeclarations
open VastitasOracle.SmoothCalculus (RatHom evalIn evalIn_nil evalIn_cons evalIn_add evalIn_mul evalIn_pow Arity
  arity_of_canonical arity_add arity_mul arity_pow arity_const arity_nil arity_partial evalAt_eq_evalIn)
open VastitasOracle.SpectralAlgebra
open VastitasOracle.AlgebraBasis (bind_ok pure_ok run_ok except_unless_ok foldlM_ok add_ok mul_ok power_ok)
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid polyEntry guard_ok unless_ok arity_polyEntry
  ring_mul_pow)

universe u

/-! ## The unbudgeted computations of the check -/

/-- The integrand `F = adj[j, i]·adj[i, j]·W²` of the trace form, in `A[t]`,
for `source = i` and `target = j`, with no budget. -/
def plainIntegrand (adjugate : PolyMatrix) (witness : Poly) (source target : Nat) : Poly :=
  Poly.mul (Poly.mul (polyEntry adjugate target source) (polyEntry adjugate source target))
    (Poly.mul witness witness)

/-- The division `divideT.go` by `χ`, monic of degree `n` in `t`, with no
budget. -/
def plainDivideGo (n : Nat) (characteristic : Poly) : Nat → Poly → Poly → Poly × Poly
  | 0, quotient, remainder => (quotient, remainder)
  | fuel + 1, quotient, remainder =>
    if remainder.isEmpty || degT remainder < n then (quotient, remainder) else
      plainDivideGo n characteristic fuel
        (Poly.add quotient (liftT (degT remainder - n) (tCoefficient remainder (degT remainder))))
        (Poly.sub remainder
          (Poly.mul (liftT (degT remainder - n) (tCoefficient remainder (degT remainder))) characteristic))

/-- The division `divideT` with no budget: the quotient and the remainder. -/
def plainDivideT (n : Nat) (characteristic x : Poly) : Poly × Poly :=
  plainDivideGo n characteristic (degT x + 1) [] x

/-- The quotient and the remainder of the integrand of a transition average
modulo `χ`. -/
def averageReduction (rows : PolyMatrix) (characteristic : Poly) (adjugate : PolyMatrix) (witness : Poly)
    (source target : Nat) : Poly × Poly :=
  plainDivideT rows.length characteristic (plainIntegrand adjugate witness source target)

/-- The trace of `tᵈ` on `A[t]/χ` for `χ` the characteristic polynomial of
the rows `H` of rank `n`, as the check writes it: `n` for `d = 0`, and
`tr(Hᵈ)` otherwise. -/
def powerTrace (arity : Nat) (rows : PolyMatrix) (d : Nat) : Poly :=
  if d == 0 then Poly.const arity (rows.length : Rat) else tracePoly (plainPower arity rows.length rows d)

/-- The trace form `Σ_{d < n} r_d·tr(Hᵈ)` of `r`, with no budget. -/
def plainTraceForm (arity : Nat) (rows : PolyMatrix) (remainder : Poly) : Poly :=
  (List.range rows.length).foldl
    (fun sum d => Poly.add sum (Poly.mul (tCoefficient remainder d) (powerTrace arity rows d))) []

/-- The identities of a transition average with no budget, as
`averageIdentities` computes them. -/
def plainAverageIdentities (arity : Nat) (rows : PolyMatrix) (characteristic : Poly) (adjugate : PolyMatrix)
    (localize witness : Poly) (exponent source target : Nat) (numerator denominator : Poly)
    (certificate : AverageCertificate) : AverageIdentities where
  reduction := Poly.sub (Poly.sub (plainIntegrand adjugate witness source target)
      (Poly.mul (averageReduction rows characteristic adjugate witness source target).1 characteristic))
    (averageReduction rows characteristic adjugate witness source target).2
  remainder := (averageReduction rows characteristic adjugate witness source target).2
  trace := plainTraceForm arity rows (averageReduction rows characteristic adjugate witness source target).2
  closedForm := Poly.sub (Poly.mul numerator (Poly.pow arity localize (2 * exponent)))
    (Poly.mul denominator
      (plainTraceForm arity rows (averageReduction rows characteristic adjugate witness source target).2))
  unit := Poly.sub (Poly.mul denominator certificate.unitQuotient) (Poly.pow arity localize certificate.unitExponent)

/-! ### Budgeted computations are plain computations -/

theorem averageIntegrand_ok {adjugate : PolyMatrix} {witness : Poly} {source target : Nat} {r : Poly} {s s' : Nat}
    (h : (averageIntegrand adjugate witness source target).run s = .ok (r, s')) :
    r = plainIntegrand adjugate witness source target := by
  unfold averageIntegrand at h
  obtain ⟨entries, _, hentries, h⟩ := bind_ok h
  obtain ⟨square, _, hsquare, h⟩ := bind_ok h
  rw [mul_ok h, mul_ok hentries, mul_ok hsquare]
  rfl

theorem divideT_go_ok {n : Nat} {characteristic : Poly} :
    ∀ {fuel : Nat} {quotient remainder : Poly} {r : Poly × Poly} {s s' : Nat},
      (divideT.go n characteristic fuel quotient remainder).run s = .ok (r, s') →
        r = plainDivideGo n characteristic fuel quotient remainder
  | 0, _, _, _, _, _, h => pure_ok h
  | fuel + 1, quotient, remainder, r, s, s', h => by
    simp only [divideT.go] at h
    simp only [plainDivideGo]
    split at h
    · rename_i hstop
      rw [ite_eq_left hstop]
      exact pure_ok h
    · rename_i hgo
      rw [ite_eq_right hgo]
      obtain ⟨q, _, hq, h⟩ := bind_ok h
      obtain ⟨product, _, hproduct, h⟩ := bind_ok h
      obtain ⟨rest, _, hrest, h⟩ := bind_ok h
      rw [add_ok hq] at h
      rw [sub_ok hrest, mul_ok hproduct] at h
      exact divideT_go_ok h

theorem divideT_ok {n : Nat} {characteristic x : Poly} {r : Poly × Poly} {s s' : Nat}
    (h : (divideT n characteristic x).run s = .ok (r, s')) : r = plainDivideT n characteristic x :=
  divideT_go_ok h

theorem traceForm_ok {arity : Nat} {rows : PolyMatrix} {remainder r : Poly} {s s' : Nat}
    (h : (traceForm arity rows remainder).run s = .ok (r, s')) : r = plainTraceForm arity rows remainder := by
  unfold traceForm at h
  unfold plainTraceForm
  refine foldlM_ok (fun sum d s s' r hstep => ?_) h
  show r = Poly.add sum (Poly.mul (tCoefficient remainder d) (powerTrace arity rows d))
  dsimp only at hstep
  unfold powerTrace
  split at hstep
  · rename_i hd
    rw [ite_eq_left hd]
    obtain ⟨power, _, hpower, hstep⟩ := bind_ok hstep
    obtain ⟨product, _, hproduct, hstep⟩ := bind_ok hstep
    rw [add_ok hstep, mul_ok hproduct, pure_ok hpower]
  · rename_i hd
    rw [ite_eq_right hd]
    obtain ⟨power, _, hpower, hstep⟩ := bind_ok hstep
    obtain ⟨product, _, hproduct, hstep⟩ := bind_ok hstep
    rw [add_ok hstep, mul_ok hproduct, tracePower_ok hpower]

theorem averageTrace_ok {arity : Nat} {rows : PolyMatrix} {characteristic : Poly} {adjugate : PolyMatrix}
    {witness : Poly} {source target : Nat} {r : Poly × Poly × Poly} {s s' : Nat}
    (h : (averageTrace arity rows characteristic adjugate witness source target).run s = .ok (r, s')) :
    r = (Poly.sub (Poly.sub (plainIntegrand adjugate witness source target)
        (Poly.mul (averageReduction rows characteristic adjugate witness source target).1 characteristic))
        (averageReduction rows characteristic adjugate witness source target).2,
      (averageReduction rows characteristic adjugate witness source target).2,
      plainTraceForm arity rows (averageReduction rows characteristic adjugate witness source target).2) := by
  unfold averageTrace at h
  obtain ⟨integrand, _, hintegrand, h⟩ := bind_ok h
  have hi := averageIntegrand_ok hintegrand
  subst hi
  obtain ⟨⟨quotient, remainder⟩, _, hdivide, h⟩ := bind_ok h
  obtain ⟨difference, _, hdifference, h⟩ := bind_ok h
  obtain ⟨reduction, _, hreduction, h⟩ := bind_ok h
  obtain ⟨trace, _, htrace, h⟩ := bind_ok h
  have hdiv := divideT_ok hdivide
  unfold residual at hdifference
  obtain ⟨product, _, hproduct, hdifference⟩ := bind_ok hdifference
  rw [pure_ok h, sub_ok hreduction, sub_ok hdifference, mul_ok hproduct, traceForm_ok htrace]
  unfold averageReduction
  rw [← hdiv]

theorem averageIdentities_ok {arity : Nat} {rows : PolyMatrix} {characteristic : Poly} {adjugate : PolyMatrix}
    {localize witness : Poly} {exponent source target : Nat} {numerator denominator : Poly}
    {certificate : AverageCertificate} {values : AverageIdentities} {s s' : Nat}
    (h : (averageIdentities arity rows characteristic adjugate localize witness exponent source target numerator
      denominator certificate).run s = .ok (values, s')) :
    values = plainAverageIdentities arity rows characteristic adjugate localize witness exponent source target
      numerator denominator certificate := by
  unfold averageIdentities at h
  obtain ⟨⟨reduction, remainder, trace⟩, _, htrace, h⟩ := bind_ok h
  have hvalues := averageTrace_ok htrace
  simp only [Prod.mk.injEq] at hvalues
  obtain ⟨rfl, rfl, rfl⟩ := hvalues
  obtain ⟨power, _, hpower, h⟩ := bind_ok h
  obtain ⟨left, _, hleft, h⟩ := bind_ok h
  obtain ⟨product, _, hproduct, h⟩ := bind_ok h
  obtain ⟨closedForm, _, hclosed, h⟩ := bind_ok h
  obtain ⟨unitProduct, _, hunitProduct, h⟩ := bind_ok h
  obtain ⟨unitPower, _, hunitPower, h⟩ := bind_ok h
  obtain ⟨unit, _, hunit, h⟩ := bind_ok h
  rw [pure_ok h, sub_ok hunit, mul_ok hunitProduct, power_ok hunitPower, sub_ok hclosed, mul_ok hleft,
    power_ok hpower, mul_ok hproduct]
  rfl

/-! ### Arities -/

theorem arity_tracePoly {k : Nat} {matrix : PolyMatrix} (h : MatrixArity k matrix) : Arity k (tracePoly matrix) := by
  unfold tracePoly
  refine foldl_of_mem (Arity k) _ _ [] (arity_nil k) fun acc ri hri hacc => ?_
  obtain ⟨row, i⟩ := ri
  have hrow : row ∈ matrix := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hri)
  refine arity_add hacc ?_
  rw [List.getD_eq_getElem?_getD]
  cases hget : row[i]? with
  | none => exact arity_nil k
  | some a => exact h row hrow a (List.mem_of_getElem? hget)

theorem arity_powerTrace {m : Nat} {rows : PolyMatrix} (h : MatrixArity m rows) (d : Nat) :
    Arity m (powerTrace m rows d) := by
  unfold powerTrace
  split
  · exact arity_const m _
  · exact arity_tracePoly (arity_plainPower h d)

theorem arity_plainTraceForm {m : Nat} {rows : PolyMatrix} {remainder : Poly} (h : MatrixArity m rows)
    (hr : Arity (m + 1) remainder) : Arity m (plainTraceForm m rows remainder) := by
  unfold plainTraceForm
  refine foldl_of_mem (Arity m) _ _ [] (arity_nil m) fun acc d _ hacc => ?_
  exact arity_add hacc (arity_mul (arity_tCoefficient hr d) (arity_powerTrace h d))

theorem arity_plainIntegrand {m : Nat} {adjugate : PolyMatrix} {witness : Poly} (h : MatrixArity (m + 1) adjugate)
    (hw : Arity (m + 1) witness) (source target : Nat) : Arity (m + 1) (plainIntegrand adjugate witness source target) :=
  arity_mul (arity_mul (arity_polyEntry h _ _) (arity_polyEntry h _ _)) (arity_mul hw hw)

theorem arity_plainDivideGo {m n : Nat} {characteristic : Poly} (hχ : Arity (m + 1) characteristic) :
    ∀ (fuel : Nat) {quotient remainder : Poly}, Arity (m + 1) quotient → Arity (m + 1) remainder →
      Arity (m + 1) (plainDivideGo n characteristic fuel quotient remainder).1 ∧
        Arity (m + 1) (plainDivideGo n characteristic fuel quotient remainder).2
  | 0, _, _, hq, hr => ⟨hq, hr⟩
  | fuel + 1, quotient, remainder, hq, hr => by
    simp only [plainDivideGo]
    split
    · exact ⟨hq, hr⟩
    · have hterm := arity_liftT (arity_tCoefficient hr (degT remainder)) (degT remainder - n)
      exact arity_plainDivideGo hχ fuel (arity_add hq hterm) (arity_sub hr (arity_mul hterm hχ))

theorem arity_averageReduction {m : Nat} {rows : PolyMatrix} {characteristic : Poly} {adjugate : PolyMatrix}
    {witness : Poly} (hχ : Arity (m + 1) characteristic) (h : MatrixArity (m + 1) adjugate)
    (hw : Arity (m + 1) witness) (source target : Nat) :
    Arity (m + 1) (averageReduction rows characteristic adjugate witness source target).1 ∧
      Arity (m + 1) (averageReduction rows characteristic adjugate witness source target).2 :=
  arity_plainDivideGo hχ _ (arity_nil _) (arity_plainIntegrand h hw source target)

/-! ## The certificate -/

/-- **The checked identities of a transition average**, as exact polynomial
identities, for the rows `H` (`n × n` of arity `m`), `χ` and `adj(tI − H)`
of a spectrum (arity `m + 1`, `t` last), the localization `g`, witness `W`
and exponent `e` of a branch, the basis indices `i = source` and
`j = target`, the closed form `N / D` and the certificate (`T`, `Q`, `k`).
`(Q_F, r)` is the reduction of the integrand `F` by `χ`. -/
structure AverageValid (m : Nat) (rows : PolyMatrix) (characteristic : Poly) (adjugate : PolyMatrix)
    (localize witness : Poly) (exponent source target : Nat) (numerator denominator : Poly)
    (certificate : AverageCertificate) : Prop where
  rank : rows.length ≤ Limits.spectralRank
  exponentLimit : exponent ≤ Limits.spectralPower
  sourceBasis : source < rows.length
  targetBasis : target < rows.length
  numeratorCanonical : Poly.canonical m numerator = true
  denominatorCanonical : Poly.canonical m denominator = true
  denominatorNonzero : denominator ≠ []
  traceCanonical : Poly.canonical m certificate.trace = true
  unitQuotientCanonical : Poly.canonical m certificate.unitQuotient = true
  unitExponentBound : certificate.unitExponent ≤ unitBound denominator
  /-- `deg_t r < n`. -/
  reduced : (averageReduction rows characteristic adjugate witness source target).2 = [] ∨
    degT (averageReduction rows characteristic adjugate witness source target).2 < rows.length
  /-- Identity 1: `F − Q_F·χ − r = 0`. -/
  reduction : Poly.sub (Poly.sub (plainIntegrand adjugate witness source target)
      (Poly.mul (averageReduction rows characteristic adjugate witness source target).1 characteristic))
    (averageReduction rows characteristic adjugate witness source target).2 = []
  /-- Identity 2: `T = Σ_{d < n} r_d·tr(Hᵈ)`. -/
  trace : certificate.trace =
    plainTraceForm m rows (averageReduction rows characteristic adjugate witness source target).2
  /-- Identity 3: `N·g^{2e} − D·T = 0`. -/
  closedForm : Poly.sub (Poly.mul numerator (Poly.pow m localize (2 * exponent)))
    (Poly.mul denominator certificate.trace) = []
  /-- Identity 4: `D·Q − g^k = 0`. -/
  unit : Poly.sub (Poly.mul denominator certificate.unitQuotient) (Poly.pow m localize certificate.unitExponent) = []

/-- A guard `unless c do throw e` with a decidable proposition `c`, followed
by the join point `jp` of the rest. -/
theorem unless_prop_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε} {jp : Unit → Except ε α} {b : α}
    (h : (if c then jp () else (throw e : Except ε Unit) >>= jp) = .ok b) : c ∧ jp () = .ok b := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    exact ⟨hc, h⟩
  · rw [ite_eq_right hc] at h
    cases h

/-- **Soundness of the average check.** An accepted transition average has a
symmetric field and satisfies `AverageValid`. -/
theorem checkAverage_sound {m : Nat} {rows : PolyMatrix} {symmetric : Bool} {characteristic : Poly}
    {adjugate : PolyMatrix} {localize witness : Poly} {exponent source target : Nat} {numerator denominator : Poly}
    {certificate : AverageCertificate}
    (h : checkAverage m rows symmetric characteristic adjugate localize witness exponent source target numerator
      denominator certificate = .ok ()) :
    symmetric = true ∧
      AverageValid m rows characteristic adjugate localize witness exponent source target numerator denominator
        certificate := by
  unfold checkAverage at h
  obtain ⟨hrank, h⟩ := guard_ok h
  obtain ⟨hexponent, h⟩ := guard_ok h
  obtain ⟨hsymmetric, h⟩ := unless_ok h
  obtain ⟨hsource, h⟩ := unless_prop_ok h
  obtain ⟨htarget, h⟩ := unless_prop_ok h
  obtain ⟨hshape, h⟩ := unless_ok h
  obtain ⟨hcertificate, h⟩ := unless_ok h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hshape hcertificate
  obtain ⟨⟨hnumerator, hdenominator⟩, hnonzero⟩ := hshape
  obtain ⟨⟨htraceCanonical, hquotient⟩, hbound⟩ := hcertificate
  cases hrun : AlgebraBasis.run (averageIdentities m rows characteristic adjugate localize witness exponent source
      target numerator denominator certificate) with
  | error e =>
    rw [hrun] at h
    cases h
  | ok values =>
    rw [hrun] at h
    obtain ⟨_, hrun'⟩ := run_ok hrun
    have hvalues := averageIdentities_ok hrun'
    subst hvalues
    obtain ⟨hreduction, h⟩ := unless_ok h
    obtain ⟨htrace, h⟩ := unless_ok h
    obtain ⟨hclosed, h⟩ := unless_ok h
    have hunit := except_unless_ok h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hreduction
    obtain ⟨hreduction, hreduced⟩ := hreduction
    have htrace' : plainTraceForm m rows (averageReduction rows characteristic adjugate witness source target).2 =
        certificate.trace := beq_iff_eq.mp htrace
    refine ⟨hsymmetric, {
      rank := by omega
      exponentLimit := by omega
      sourceBasis := hsource
      targetBasis := htarget
      numeratorCanonical := hnumerator
      denominatorCanonical := hdenominator
      denominatorNonzero := fun hz => by rw [hz] at hnonzero; cases hnonzero
      traceCanonical := htraceCanonical
      unitQuotientCanonical := hquotient
      unitExponentBound := hbound
      reduced := by
        rcases hreduced with hempty | hdeg
        · exact .inl (List.isEmpty_iff.mp hempty)
        · exact .inr hdeg
      reduction := List.isEmpty_iff.mp hreduction
      trace := htrace'.symm
      closedForm := by
        have := List.isEmpty_iff.mp hclosed
        simp only [plainAverageIdentities] at this
        rw [htrace'] at this
        exact this
      unit := List.isEmpty_iff.mp hunit }⟩

/-! ## At a point of a ring -/

section Ring

variable {R : Type u} [Lean.Grind.CommRing R]
variable {m : Nat} {rows : PolyMatrix} {characteristic : Poly} {adjugate : PolyMatrix} {localize witness : Poly}
  {exponent source target : Nat} {numerator denominator : Poly} {certificate : AverageCertificate}

namespace AverageValid

variable (ha : AverageValid m rows characteristic adjugate localize witness exponent source target numerator
  denominator certificate)
include ha

/-- **The closed form at a point**: `N(z)·g(z)^{2e} = D(z)·T(z)`. -/
theorem closedForm_at (hg : Arity m localize) (ι : RatHom R) (z : List R) :
    evalIn ι numerator z * evalIn ι localize z ^ (2 * exponent) =
      evalIn ι denominator z * evalIn ι certificate.trace z := by
  have h := evalIn_eq_of_sub_eq_nil ι ha.closedForm z
  rw [evalIn_mul ι (arity_of_canonical ha.numeratorCanonical) (arity_pow hg _), evalIn_pow ι hg,
    evalIn_mul ι (arity_of_canonical ha.denominatorCanonical) (arity_of_canonical ha.traceCanonical)] at h
  exact h

/-- **The unit certificate at a point**: `D(z)·Q(z) = g(z)^k`. -/
theorem unit_at (hg : Arity m localize) (ι : RatHom R) (z : List R) :
    evalIn ι denominator z * evalIn ι certificate.unitQuotient z = evalIn ι localize z ^ certificate.unitExponent := by
  have h := evalIn_eq_of_sub_eq_nil ι ha.unit z
  rw [evalIn_mul ι (arity_of_canonical ha.denominatorCanonical) (arity_of_canonical ha.unitQuotientCanonical),
    evalIn_pow ι hg] at h
  exact h

omit ha in
/-- **The integrand at a point**: `F(z) = adj[j, i](z)·adj[i, j](z)·W(z)²`. -/
theorem integrand_at (hadj : MatrixArity (m + 1) adjugate) (hw : Arity (m + 1) witness) (ι : RatHom R)
    (z : List R) :
    evalIn ι (plainIntegrand adjugate witness source target) z =
      ringEntry (evalMatrix ι adjugate z) target source * ringEntry (evalMatrix ι adjugate z) source target *
        (evalIn ι witness z * evalIn ι witness z) := by
  rw [plainIntegrand, evalIn_mul ι (arity_mul (arity_polyEntry hadj _ _) (arity_polyEntry hadj _ _)) (arity_mul hw hw),
    evalIn_mul ι (arity_polyEntry hadj _ _) (arity_polyEntry hadj _ _), evalIn_mul ι hw hw,
    SpectralDeclarations.ringEntry_evalMatrix, SpectralDeclarations.ringEntry_evalMatrix]

/-- **The reduction at a point**: `F(z) = Q_F(z)·χ(z) + r(z)`. -/
theorem reduction_at (hχ : Arity (m + 1) characteristic) (hadj : MatrixArity (m + 1) adjugate)
    (hw : Arity (m + 1) witness) (ι : RatHom R) (z : List R) :
    evalIn ι (plainIntegrand adjugate witness source target) z =
      evalIn ι (averageReduction rows characteristic adjugate witness source target).1 z *
          evalIn ι characteristic z +
        evalIn ι (averageReduction rows characteristic adjugate witness source target).2 z := by
  have h := evalIn_eq_of_sub_eq_nil ι ha.reduction z
  rw [evalIn_sub, evalIn_mul ι (arity_averageReduction hχ hadj hw source target).1 hχ] at h
  grind

/-- **The remainder in `t`**: `r(x, t) = Σ_{d < n} r_d(x) tᵈ`, `deg_t r < n`. -/
theorem remainder_at (hχ : Arity (m + 1) characteristic) (hadj : MatrixArity (m + 1) adjugate)
    (hw : Arity (m + 1) witness) (ι : RatHom R) {x : List R} (hx : x.length = m) (t : R) :
    evalIn ι (averageReduction rows characteristic adjugate witness source target).2 (x ++ [t]) =
      ringSum rows.length (fun d =>
        evalIn ι (tCoefficient (averageReduction rows characteristic adjugate witness source target).2 d) x *
          t ^ d) := by
  have harity : Arity (x.length + 1) (averageReduction rows characteristic adjugate witness source target).2 := by
    rw [hx]
    exact (arity_averageReduction hχ hadj hw source target).2
  refine evalIn_tCoefficient_of_lt ι t _ harity fun term hterm => ?_
  rcases ha.reduced with hempty | hdeg
  · rw [hempty] at hterm
    cases hterm
  · exact Nat.lt_of_le_of_lt (fiberExponent_le_degT hterm) hdeg

/-- **The integrand at a zero of `χ`** is the remainder:
`F(x, t) = Σ_{d < n} r_d(x) tᵈ` where `χ(x, t) = 0`. -/
theorem integrand_at_root (hχ : Arity (m + 1) characteristic) (hadj : MatrixArity (m + 1) adjugate)
    (hw : Arity (m + 1) witness) (ι : RatHom R) {x : List R} (hx : x.length = m) {t : R}
    (hroot : evalIn ι characteristic (x ++ [t]) = 0) :
    evalIn ι (plainIntegrand adjugate witness source target) (x ++ [t]) =
      ringSum rows.length (fun d =>
        evalIn ι (tCoefficient (averageReduction rows characteristic adjugate witness source target).2 d) x *
          t ^ d) := by
  rw [ha.reduction_at hχ hadj hw ι, hroot, ha.remainder_at hχ hadj hw ι hx t]
  grind

end AverageValid

/-- The sum of `n` ones is the image of `n`. -/
theorem ringSum_one (ι : RatHom R) : ∀ n : Nat, ringSum n (fun _ => (1 : R)) = ι.toFun (n : Rat)
  | 0 => by
    rw [ringSum_zero, show ((0 : Nat) : Rat) = 0 by grind, ι.map_zero]
  | n + 1 => by
    rw [ringSum_succ, ringSum_one ι n, show ((n + 1 : Nat) : Rat) = (n : Rat) + 1 by grind, ι.map_add, ι.map_one]

/-- The trace of the `n × n` identity is the image of `n`. -/
theorem ringTrace_ringIdentity (ι : RatHom R) (n : Nat) :
    ringTrace (ringIdentity n : List (List R)) = ι.toFun (n : Rat) := by
  rw [ringTrace_eq, ringIdentity, length_ringScalar, ← ringSum_one ι n]
  exact ringSum_congr fun i hi => by rw [ringEntry_ringScalar 1 hi hi]; simp

/-- A constant at any point. -/
theorem evalIn_const (ι : RatHom R) (arity : Nat) (value : Rat) (x : List R) :
    evalIn ι (Poly.const arity value) x = ι.toFun value := by
  unfold Poly.const
  split
  · rename_i hzero
    have : value = 0 := by simpa using hzero
    rw [this, ι.map_zero, evalIn_nil]
  · rw [evalIn_cons, evalIn_nil, Monomial.one, VastitasOracle.SmoothCalculus.monomialValueIn_zero]
    grind

/-- **`powerTrace` at a point** is `tr(H(x)ᵈ)` for every `d`, `tr(H(x)⁰) = n`. -/
theorem evalIn_powerTrace (ι : RatHom R) (hrows : MatrixArity m rows) (x : List R) (d : Nat) :
    evalIn ι (powerTrace m rows d) x = ringTrace (ringPow rows.length (evalMatrix ι rows x) d) := by
  unfold powerTrace
  split
  · rename_i hd
    have : d = 0 := by simpa using hd
    subst this
    rw [evalIn_const, ringPow, ringTrace_ringIdentity ι]
  · rw [evalIn_tracePoly, evalMatrix_plainPower ι hrows]

theorem evalIn_foldl_trace (ι : RatHom R) (hrows : MatrixArity m rows) {remainder : Poly}
    (hr : Arity (m + 1) remainder) (x : List R) :
    ∀ (k : Nat) (acc : Poly),
      evalIn ι ((List.range k).foldl
          (fun sum d => Poly.add sum (Poly.mul (tCoefficient remainder d) (powerTrace m rows d))) acc) x =
        evalIn ι acc x +
          ringSum k (fun d => evalIn ι (tCoefficient remainder d) x * ringTrace (ringPow rows.length (evalMatrix ι rows x) d))
  | 0, acc => by
    rw [List.range_zero, List.foldl_nil, ringSum_zero]
    grind
  | k + 1, acc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, evalIn_add,
      evalIn_foldl_trace ι hrows hr x k acc, evalIn_mul ι (arity_tCoefficient hr k) (arity_powerTrace hrows k),
      evalIn_powerTrace ι hrows x k, ringSum_succ]
    grind

namespace AverageValid

variable (ha : AverageValid m rows characteristic adjugate localize witness exponent source target numerator
  denominator certificate)
include ha

/-- **The trace form at a point**: `T(x) = Σ_{d < n} r_d(x)·tr(H(x)ᵈ)`, the
trace of `r(x, ·)` on `R[t]/χ(x, ·)` in the basis `1, t, …, t^{n−1}`. -/
theorem trace_at (hχ : Arity (m + 1) characteristic) (hrows : MatrixArity m rows)
    (hadj : MatrixArity (m + 1) adjugate) (hw : Arity (m + 1) witness) (ι : RatHom R) (x : List R) :
    evalIn ι certificate.trace x =
      ringSum rows.length (fun d =>
        evalIn ι (tCoefficient (averageReduction rows characteristic adjugate witness source target).2 d) x *
          ringTrace (ringPow rows.length (evalMatrix ι rows x) d)) := by
  rw [ha.trace, plainTraceForm,
    evalIn_foldl_trace ι hrows (arity_averageReduction hχ hadj hw source target).2 x rows.length [], evalIn_nil]
  grind

end AverageValid

/-- **The integrand times the squared slope at a zero of `χ`**: with the gap
`W·χ′ − gᵉ = Q·χ`, `F(z)·χ′(z)² = adj[j, i](z)·adj[i, j](z)·g(z)^{2e}` where
`χ(z) = 0`. Divided by `χ′(z)²`, it is `g(z)^{2e}` times the product of the
entries `(j, i)` and `(i, j)` of the eigenprojector `adj(z)/χ′(z)`. -/
theorem integrand_mul_slope_sq {idempotence : PolyMatrix} {quotient : Poly}
    (hv : SpectralValid m rows ⟨characteristic, adjugate, idempotence⟩)
    (hw : WitnessValid m rows.length characteristic localize witness exponent quotient) (ι : RatHom R)
    (z : List R) (hroot : evalIn ι characteristic z = 0) :
    evalIn ι (plainIntegrand adjugate witness source target) z *
        (evalIn ι (VastitasKernel.SmoothRuntime.partialDerivative m characteristic) z *
          evalIn ι (VastitasKernel.SmoothRuntime.partialDerivative m characteristic) z) =
      ringEntry (evalMatrix ι adjugate z) target source * ringEntry (evalMatrix ι adjugate z) source target *
        evalIn ι localize z ^ (2 * exponent) := by
  have hgap := hw.gap_at hv.characteristic_arity ι z
  rw [hroot] at hgap
  rw [AverageValid.integrand_at hv.adjugate_arity (arity_of_canonical hw.witnessCanonical) ι z]
  have hpow : evalIn ι localize z ^ (2 * exponent) =
      evalIn ι localize z ^ exponent * evalIn ι localize z ^ exponent := by
    rw [Nat.two_mul, Lean.Grind.Semiring.pow_add]
  rw [hpow]
  have hslope : evalIn ι witness z * evalIn ι (VastitasKernel.SmoothRuntime.partialDerivative m characteristic) z =
      evalIn ι localize z ^ exponent := by grind
  rw [← hslope]
  grind

end Ring

/-! ## At a rational point of the chart -/

theorem rat_pow_ne_zero {g : Rat} (hg : g ≠ 0) (k : Nat) : g ^ k ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih => grind

namespace AverageValid

variable {m : Nat} {rows : PolyMatrix} {characteristic : Poly} {adjugate : PolyMatrix} {localize witness : Poly}
  {exponent source target : Nat} {numerator denominator : Poly} {certificate : AverageCertificate}
variable (ha : AverageValid m rows characteristic adjugate localize witness exponent source target numerator
  denominator certificate)
include ha

/-- **The value on the chart.** At a rational point `p` with `g(p) ≠ 0`, the
denominator does not vanish, and `N(p)/D(p) = T(p)/g(p)^{2e}`. -/
theorem value_at (hg : Arity m localize) {p : List Rat} (hgp : evalAt localize p ≠ 0) :
    evalAt denominator p ≠ 0 ∧
      evalAt numerator p / evalAt denominator p = evalAt certificate.trace p / evalAt localize p ^ (2 * exponent) := by
  simp only [evalAt_eq_evalIn] at hgp ⊢
  have hunit := ha.unit_at hg RatHom.id p
  have hclosed := ha.closedForm_at hg RatHom.id p
  have hd : evalIn RatHom.id denominator p ≠ 0 := by
    intro hzero
    rw [hzero, Rat.zero_mul] at hunit
    exact rat_pow_ne_zero hgp _ hunit.symm
  have hpow := rat_pow_ne_zero hgp (2 * exponent)
  refine ⟨hd, ?_⟩
  grind

/-- **The observation on the chart.** At a point with `g(p) ≠ 0`,
`average_at` is the rational `N(p)/D(p) = T(p)/g(p)^{2e}`, never the failure
pair. -/
theorem averageAt_on_chart (hg : Arity m localize) {point : Program}
    (hgp : evalAt localize (coordinates point) ≠ 0) :
    SpectralRuntime.averageAt localize numerator denominator point =
        ratPair (evalAt numerator (coordinates point) / evalAt denominator (coordinates point)) ∧
      evalAt numerator (coordinates point) / evalAt denominator (coordinates point) =
        evalAt certificate.trace (coordinates point) / evalAt localize (coordinates point) ^ (2 * exponent) ∧
      SpectralRuntime.averageAt localize numerator denominator point ≠ (0, 0) := by
  obtain ⟨hd, hvalue⟩ := ha.value_at hg hgp
  have hat : SpectralRuntime.averageAt localize numerator denominator point =
      ratPair (evalAt numerator (coordinates point) / evalAt denominator (coordinates point)) := by
    simp [SpectralRuntime.averageAt, hgp, hd]
  exact ⟨hat, hvalue, by rw [hat]; exact SpectralRuntime.ratPair_ne_failure _⟩

end AverageValid

/-- **The observation off the chart** is the failure pair `(0, 0)`, whatever
the closed form. -/
theorem averageAt_off_chart {localize numerator denominator : Poly} {point : Program}
    (hgp : evalAt localize (coordinates point) = 0) :
    SpectralRuntime.averageAt localize numerator denominator point = (0, 0) := by
  simp [SpectralRuntime.averageAt, hgp]

/-! ## The declaration -/

/-- **An accepted transition average declaration**: its family is a
`transition_average` family applied to a declared smooth object of dimension
`m`; it names a branch of that object with a valid gap certificate for the
`χ` of its spectrum, whose endomorphism has symmetric rows `H`; and the closed
form and certificate satisfy `AverageValid` for that data. -/
theorem checkTransitionAverage_sound {env : Environment} {family object branch : DeclId} {source target : Nat}
    {numerator denominator : Poly} {certificate : AverageCertificate}
    (h : checkTransitionAverage env family object branch source target numerator denominator certificate = true) :
    isTransitionAverageFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ m branchFamily spectrum localize witness exponent quotient spectrumFamily spectrumObject endomorphism
        fiber spectral endomorphismFamily endomorphismObject module rows symmetric,
        smoothDimension? env object = some m ∧
        branchData? env branch = some (branchFamily, object, spectrum, localize, witness, exponent, quotient) ∧
        spectrumData? env spectrum = some (spectrumFamily, spectrumObject, endomorphism, fiber, spectral) ∧
        endomorphismData? env endomorphism =
          some (endomorphismFamily, endomorphismObject, module, rows, symmetric) ∧
        symmetric = true ∧
        AverageValid m rows spectral.characteristic spectral.adjugate localize witness exponent source target
          numerator denominator certificate := by
  simp only [checkTransitionAverage, Bool.and_eq_true] at h
  obtain ⟨hdeclared, hmatch⟩ := h
  obtain ⟨hfamily, happ, _⟩ := SpectralDeclarations.declaredAt_spec hdeclared
  refine ⟨hfamily, happ, ?_⟩
  cases hm : smoothDimension? env object with
  | none => rw [hm] at hmatch; cases hmatch
  | some m =>
    cases hb : branchData? env branch with
    | none => rw [hm, hb] at hmatch; cases hmatch
    | some bdata =>
      obtain ⟨branchFamily, branchObject, spectrum, localize, witness, exponent, quotient⟩ := bdata
      rw [hm, hb] at hmatch
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨hobject, hrest⟩ := hmatch
      subst hobject
      cases hs : spectrumData? env spectrum with
      | none => rw [hs] at hrest; cases hrest
      | some sdata =>
        obtain ⟨spectrumFamily, spectrumObject, endomorphism, fiber, spectral⟩ := sdata
        rw [hs] at hrest
        dsimp only at hrest
        cases he : endomorphismData? env endomorphism with
        | none => rw [he] at hrest; cases hrest
        | some edata =>
          obtain ⟨endomorphismFamily, endomorphismObject, module, rows, symmetric⟩ := edata
          rw [he] at hrest
          dsimp only at hrest
          obtain ⟨hsym, ha⟩ := checkAverage_sound (VastitasOracle.FrameDeclarations.isOk_ok hrest)
          exact ⟨m, branchFamily, spectrum, localize, witness, exponent, quotient, spectrumFamily, spectrumObject,
            endomorphism, fiber, spectral, endomorphismFamily, endomorphismObject, module, rows, symmetric, rfl, rfl,
            hs, he, hsym, ha⟩

theorem transitionAverageData_lookup {env : Environment} {id family object branch : DeclId} {source target : Nat}
    {numerator denominator : Poly} {certificate : AverageCertificate}
    (h : transitionAverageData? env id =
      some (family, object, branch, source, target, numerator, denominator, certificate)) :
    lookup env id = some (.transitionAverage family object branch source target numerator denominator certificate) := by
  unfold transitionAverageData? at h
  split at h
  · rename_i found
    cases h
    exact found
  · cases h

theorem branch_lookup {env : Environment} {id family object spectrum : DeclId} {localize witness : Poly}
    {exponent : Nat} {quotient : Poly}
    (h : branchData? env id = some (family, object, spectrum, localize, witness, exponent, quotient)) :
    lookup env id = some (.branch family object spectrum localize witness exponent quotient) :=
  SpectralCore.branchData_lookup h

theorem endomorphism_lookup {env : Environment} {id family object module : DeclId} {rows : PolyMatrix}
    {symmetric : Bool} (h : endomorphismData? env id = some (family, object, module, rows, symmetric)) :
    lookup env id = some (.endomorphism family object module rows symmetric) :=
  SpectralDeclarations.endomorphismData_lookup h

/-- **Transition averages of a valid environment.** A declared transition
average from `i` to `j` names a branch of its object whose spectrum's
certificate is valid for the symmetric rows `H` of the spectrum's
endomorphism, on the same object, and whose gap certificate is valid for that
`χ`; its closed form satisfies `AverageValid` for that data. -/
theorem transitionAverage_sound {env : Environment} (envValid : env.Valid) {id family object branch : DeclId}
    {source target : Nat} {numerator denominator : Poly} {certificate : AverageCertificate}
    (found : lookup env id =
      some (.transitionAverage family object branch source target numerator denominator certificate)) :
    isTransitionAverageFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates branchFamily spectrum localize witness exponent quotient spectrumFamily
        endomorphism fiber spectral endomorphismFamily module rows,
        lookup env object = some (.smoothAffine implementation coordinates) ∧
        branchData? env branch = some (branchFamily, object, spectrum, localize, witness, exponent, quotient) ∧
        spectrumData? env spectrum = some (spectrumFamily, object, endomorphism, fiber, spectral) ∧
        endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, true) ∧
        SpectralValid coordinates.length rows spectral ∧
        WitnessValid coordinates.length rows.length spectral.characteristic localize witness exponent quotient ∧
        AverageValid coordinates.length rows spectral.characteristic spectral.adjugate localize witness exponent
          source target numerator denominator certificate := by
  obtain ⟨hfamily, happ, m, branchFamily, spectrum, localize, witness, exponent, quotient, spectrumFamily,
    spectrumObject, endomorphism, fiber, spectral, endomorphismFamily, endomorphismObject, module, rows, symmetric,
    hm, hb, hs, he, hsym, ha⟩ :=
    checkTransitionAverage_sound (SpectralDeclarations.valid_of_lookup envValid found)
  subst hsym
  obtain ⟨-, -, implementation, coordinates, spectrumFamily', endomorphism', fiber', spectral', hobject, hs',
    endomorphismFamily', module', rows', symmetric', he', hv, hw⟩ :=
    SpectralDeclarations.branch_sound envValid (branch_lookup hb)
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hs'
  rw [he] at he'
  simp only [Option.some.injEq, Prod.mk.injEq] at he'
  obtain ⟨-, rfl, -, rfl, rfl⟩ := he'
  have hm' := SpectralCore.smoothDimension_of_lookup hobject
  rw [hm] at hm'
  cases hm'
  exact ⟨hfamily, happ, implementation, coordinates, branchFamily, spectrum, localize, witness, exponent, quotient,
    spectrumFamily, endomorphism, fiber, spectral, endomorphismFamily, module, rows, hobject, hb, hs, he, hv, hw,
    ha⟩

/-! ## The embedded average of a binding -/

/-- The embedded transition average is its declaration: a transition average
declaration on the object of the embedded branch, of exactly that branch,
with exactly the embedded closed form, and the embedded branch is its
declaration. -/
def DeclaredAverage (env : Environment) (average : AverageRef) : Prop :=
  SpectralCore.DeclaredBranch env average.branch ∧
    ∃ family source target certificate, transitionAverageData? env average.average =
      some (family, average.object, average.branch.branch, source, target, average.numerator, average.denominator,
        certificate)

theorem declaredAverage_of_averageDeclared {env : Environment} {average : AverageRef}
    (h : averageDeclared env average = true) : DeclaredAverage env average := by
  unfold averageDeclared at h
  cases hd : transitionAverageData? env average.average with
  | none => rw [hd] at h; cases h
  | some data =>
    obtain ⟨family, object, branch, source, target, numerator, denominator, certificate⟩ := data
    rw [hd] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hobject, hbranch⟩, hnumerator⟩, hdenominator⟩, hdeclared⟩ := h
    subst hobject hbranch hnumerator hdenominator
    exact ⟨SpectralCore.declaredBranch_of_branchDeclared hdeclared, family, source, target, certificate, hd⟩

/-- **The embedded average is checked.** In a valid environment the embedded
data of a declared transition average satisfies every hypothesis of the
theorems above: a valid spectral certificate of symmetric rows, a valid gap
certificate, and `AverageValid` with the embedded localization, witness,
exponent and closed form. -/
theorem DeclaredAverage.checked {env : Environment} (envValid : env.Valid) {average : AverageRef}
    (h : DeclaredAverage env average) :
    ∃ m idempotence quotient source target certificate,
      smoothDimension? env average.object = some m ∧
      average.branch.spectrum.endomorphism.symmetric = true ∧
      SpectralValid m average.branch.spectrum.endomorphism.rows
        ⟨average.branch.spectrum.characteristic, average.branch.spectrum.adjugate, idempotence⟩ ∧
      WitnessValid m average.branch.spectrum.endomorphism.rows.length average.branch.spectrum.characteristic
        average.branch.localize average.branch.witness average.branch.exponent quotient ∧
      AverageValid m average.branch.spectrum.endomorphism.rows average.branch.spectrum.characteristic
        average.branch.spectrum.adjugate average.branch.localize average.branch.witness average.branch.exponent
        source target average.numerator average.denominator certificate := by
  obtain ⟨hbranch, family, source, target, certificate, found⟩ := h
  obtain ⟨m, idempotence, quotient, hm, hv, hw⟩ := hbranch.checked envValid
  obtain ⟨-, -, implementation, coordinates, branchFamily, spectrum, localize, witness, exponent, quotient',
    spectrumFamily, endomorphism, fiber, spectral, endomorphismFamily, module, rows, hobject, hb, hs, he, -, -, ha⟩ :=
    transitionAverage_sound envValid (transitionAverageData_lookup found)
  obtain ⟨⟨⟨endoFamily, endoFound⟩, spectrumFamily', fiber', certificate', spectrumFound, hchar, hadj⟩, branchFamily',
    quotient'', branchFound⟩ := hbranch
  rw [hb] at branchFound
  simp only [Option.some.injEq, Prod.mk.injEq] at branchFound
  obtain ⟨-, -, rfl, rfl, rfl, rfl, -⟩ := branchFound
  rw [hs] at spectrumFound
  simp only [Option.some.injEq, Prod.mk.injEq] at spectrumFound
  obtain ⟨-, -, rfl, -, rfl⟩ := spectrumFound
  rw [he] at endoFound
  simp only [Option.some.injEq, Prod.mk.injEq] at endoFound
  obtain ⟨-, -, -, rfl, hsym⟩ := endoFound
  have hm' := SpectralCore.smoothDimension_of_lookup hobject
  have hm2 : smoothDimension? env average.object = some m := hm
  rw [hm2] at hm'
  cases hm'
  rw [hchar, hadj] at ha
  exact ⟨coordinates.length, idempotence, quotient, source, target, certificate, hm2, hsym.symm, hv, hw, ha⟩

/-! ## Accepted Core -/

theorem averageAt_inv {env : Environment} {smooth line : DeclId} {average : AverageRef} {values : List Value}
    {value : Value} (h : evalPrimitive env (.averageAt smooth line average) values = some value) :
    ∃ point, values = [.indexed (.smooth point)] ∧
      value = .pairInt
        (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator point).1
        (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator point).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.averageAt, PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, rfl, (Option.some.inj h).symm⟩
  · contradiction

section Accepted

variable {module : Module} {functions : Core.Typing.Signatures} {ctx : Core.Typing.Context} {world : World}
  {fuel : Nat} {values : Values} {id : DeclId} {result : Result} {operands : List ValueType}
  {output : ValueType}

/-- **`average_at` on accepted Core.** An accepted
`average_at(p, average = A)` evaluates, one unit of fuel later, to
`SpectralRuntime.averageAt g N D p` with the declared localization `g` of the
branch of `A` and the declared closed form `N / D`; the point has the
coordinates of the average's object. -/
theorem core_spectral_average_at {point : Core.Term} {smooth line : DeclId} {average : AverageRef}
    {pointValue : Value}
    (found : module.declarations.primitive? id = some (.averageAt smooth line average))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    DeclaredAverage module.declarations.indexed average ∧ output = .integerPair ∧
      ∃ m x, smoothDimension? module.declarations.indexed average.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ (coordinates x).length = m ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.pairInt
            (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x).1
            (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point] result _ operands
    output found input outputType accepted
  have valid : averageAtValid module.declarations.indexed smooth line average = true := rule.bindingValid
  unfold averageAtValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨hsmooth, _⟩, hdeclared⟩ := valid
  obtain ⟨p, rfl⟩ := SpectralPrimitives.averageAt_shape rule.association
  obtain ⟨-, -, pointZero, resultEq⟩ := SpectralPrimitives.averageAt_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval]) typed (by intro _ h; cases h)
  obtain ⟨x, shapes, rfl⟩ := averageAt_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  obtain ⟨program, n, valueEq, hx, welltyped⟩ :=
    SmoothFibers.point_value (SmoothPrimitives.smooth_family hsmooth) pointZero typed.1
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at valueEq
  subst valueEq
  exact ⟨declaredAverage_of_averageDeclared hdeclared, resultEq.symm, n, x, hx, rfl,
    SmoothFibers.coordinates_length welltyped, evaluated⟩

/-- **The value of an accepted `average_at` (C3).** In a valid environment an
accepted `average_at(p, average = A)` evaluates to the exact rational
`N(p)/D(p)` where `g(p) ≠ 0`, which is `T(p)/g(p)^{2e}` for the checked trace
form `T`, and to the failure pair `(0, 0)` where `g(p) = 0`. -/
theorem accepted_average_at {point : Core.Term} {smooth line : DeclId} {average : AverageRef}
    {pointValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.averageAt smooth line average))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    ∃ m x source target certificate,
      smoothDimension? module.declarations.indexed average.object = some m ∧
      pointValue = .indexed (.smooth x) ∧ (coordinates x).length = m ∧
      AverageValid m average.branch.spectrum.endomorphism.rows average.branch.spectrum.characteristic
        average.branch.spectrum.adjugate average.branch.localize average.branch.witness average.branch.exponent
        source target average.numerator average.denominator certificate ∧
      eval module (fuel + 1) values (.primitive id [point] result) =
        some (.pairInt
          (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x).1
          (SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x).2) ∧
      (evalAt average.branch.localize (coordinates x) ≠ 0 →
        SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x =
          ratPair (evalAt average.numerator (coordinates x) / evalAt average.denominator (coordinates x)) ∧
        evalAt average.numerator (coordinates x) / evalAt average.denominator (coordinates x) =
          evalAt certificate.trace (coordinates x) /
            evalAt average.branch.localize (coordinates x) ^ (2 * average.branch.exponent)) ∧
      (evalAt average.branch.localize (coordinates x) = 0 →
        SpectralRuntime.averageAt average.branch.localize average.numerator average.denominator x = (0, 0)) := by
  obtain ⟨declared, -, m, x, hm, rfl, hx, evaluated⟩ :=
    core_spectral_average_at found input outputType accepted pointEval typed
  obtain ⟨m', idempotence, quotient, source, target, certificate, hm', -, -, hw, ha⟩ := declared.checked envValid
  rw [hm] at hm'
  cases hm'
  have hg := arity_of_canonical hw.localizeCanonical
  exact ⟨m, x, source, target, certificate, hm, rfl, hx, ha, evaluated,
    fun hgp => ⟨(ha.averageAt_on_chart hg hgp).1, (ha.averageAt_on_chart hg hgp).2.1⟩,
    fun hgp => averageAt_off_chart hgp⟩

end Accepted

end VastitasOracle.SpectralAverage
