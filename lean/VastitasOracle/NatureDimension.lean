import VastitasKernel.IndexedAudit
import VastitasOracle.Support

set_option autoImplicit false

/-! Oracle theorems about the declarations of `nature::dimension` (Stage 4,
#759; ADR 0002 §3): what the kernel checks of `NatureDimension` guarantee.
Every theorem reads the kernel's own checks, and none needs mathlib.

**Dimensions.** A dimension is a list of factors `(base, exponent)` with
integer exponents. The kernel compares two dimensions by the exponent of each
base, so a dimension denotes an element of the free abelian group on the base
dimensions (`SameDimension`, `sameDimension_iff`). `addScaled d k o` is
`d + k·o` (`exponentOf_addScaled`) for the total exponent `exponent` of a
list of factors, which is the kernel's exponent in a canonical dimension
(`exponent_eq_exponentOf`).

**C16, the declarations.**
- A base dimension is one of at most `Limits.dimensionBases` base dimensions
  of the program (`checkBaseDimension_iff`, `mem_baseDimensions`).
- A quantity kind has a canonical dimension: base dimensions, each once, with
  nonzero exponents within the bound (`checkQuantity_iff`,
  `CanonicalDimension`).
- A reading is declared at a `reading` family applied to a smooth object and
  reads each coordinate, in coordinate order, as a declared quantity: one
  quantity per coordinate (`checkReading_iff`).
- A scale is of a declared quantity and has a positive magnitude within the
  entry bound (`checkScale_iff`).
- In a valid environment: `valid_quantity`, `valid_reading`, `valid_scale`.

**C17–C19, a physical metric.** An accepted physical metric is declared at a
`physical_metric` family applied to its object, its declared value is
canonical, and it `Interprets` a metric of its object under a reading of its
object (`physicalMetric_sound`, in a valid environment
`valid_physicalMetric`):
- the reading has one quantity per coordinate of the object;
- the entries, evaluated with the magnitudes of their scales, are the Gram
  matrix of the metric (`Interprets.evaluates`);
- every term `g_ij dxⁱ dxʲ` with a nonzero entry has one dimension, its
  `termDimension`: the dimension of `g_ij` plus the dimensions of the
  quantities of `xⁱ` and `xʲ` (`exponentOf_termDimension`). A declared value
  is that dimension, and needs a nonzero term. The order of the terms does not
  matter and a zero entry constrains nothing (`Interprets.oneDimension`,
  `Interprets.declaredValue`). Every exponent of that dimension is within
  `Limits.dimensionExponent`, so a declared value can write it
  (`consistentValue_bounded`).
The entries of each form: `euclidean` is the identity, dimensionless
(`entryValues_euclidean`); an explicit entry `c · Π sᵢ^{eᵢ}` has the value
`c · Π mᵢ^{eᵢ}` and the dimension `Σ eᵢ · dᵢ`, the law of ADR 0002 for the
dimension of a product of scales (`entryValues_gram`,
`scaleMonomialValue_sound`); `normalized` has the diagonal `1 / sᵢ²` of
dimension `-2·dᵢ` (`entryValues_normalized`).

**C17, `dx² + dt²`.** An accepted `euclidean` interpretation reads every
coordinate with one dimension (`euclidean_sound`). Under a reading of a
coordinate of dimension `L` and one of dimension `T`, two distinct base
dimensions, it is rejected whatever its declared value (`euclidean_rejected`).

**C19, kinds.** `normalized` needs each scale of exactly its coordinate's
quantity kind (`Interprets.normalizedKinds`); a scale of another kind is
rejected whatever its dimension (`normalized_rejected_of_kind`). Explicit
rows compare dimensions only.

**The roadmap example by computation** (`Roadmap`). On the chart `X[x, t]`
read as `(x: Length, t: Time)` with the base dimensions `L` and `T`, the
kernel evaluates (`decide +kernel`):
- C17: the Euclidean metric is rejected (`Roadmap.euclidean_check_rejected`,
  also by `euclidean_rejected`), and no environment with that interpretation
  is valid (`Roadmap.euclidean_invalid`);
- C18: with `l0 = 3` and `t0 = 2`, `gram((l0^-2, 0), (0, t0^-2))` interprets
  `G = diag(1/9, 1/4)` (`Roadmap.scaled_accepted`), and the whole environment
  with that interpretation is valid (`Roadmap.interpreted_valid`); a
  magnitude mismatch and a scale of the wrong dimension are rejected
  (`Roadmap.mismatch_rejected`, `Roadmap.wrong_dimension_rejected`), and
  `dx² − c²dt²` with a speed scale is accepted (`Roadmap.minkowski_accepted`);
- C19: `normalized(x: l0, t: t0)` is accepted, and `normalized` with a
  `Wavelength` scale on the `Length` coordinate is rejected
  (`Roadmap.normalized_accepted`, `Roadmap.wavelength_rejected`), while
  explicit rows accept it (`Roadmap.wavelength_rows_accepted`).

**ADR 0002 "Evidence".** "The oracle must prove that an accepted
interpretation is consistent": `physicalMetric_sound` and
`valid_physicalMetric`. "And that `nature` declarations change no `std`
validity and no binding": `NatureWeakening`.

**Boundary.** These theorems state what the checker accepts: a syntactic
dimension check, the first level of #300. They do not establish a physical
law or the truth of a reading; that the Gram matrix is a metric is the
bridge's (`VastitasBridge.Differential.Metric`). The bounds of `Limits` are
resource limits, and the soundness theorems do not depend on them;
`consistentValue_bounded` only states that the exponent bound holds for the
value. -/
namespace VastitasOracle.NatureDimension

open VastitasKernel VastitasKernel.Indexed VastitasKernel.NatureDimension
open VastitasOracle.Support (mapM_some_index)

/-! ## Dimensions

A dimension is stored as a list of factors `(base, exponent)`. The kernel
compares two dimensions by the exponent of each base (`exponentOf`,
`sameDimension`), so a dimension denotes an element of the free abelian group
on the base dimensions. -/

/-- Two dimensions are one element of the dimension group: every base
dimension has one exponent in both. -/
def SameDimension (first second : DimensionVector) : Prop :=
  ∀ base, exponentOf first base = exponentOf second base

theorem SameDimension.refl (dimension : DimensionVector) : SameDimension dimension dimension := fun _ => rfl

theorem SameDimension.symm {first second : DimensionVector} (h : SameDimension first second) :
    SameDimension second first := fun base => (h base).symm

theorem SameDimension.trans {first second third : DimensionVector} (h : SameDimension first second)
    (h' : SameDimension second third) : SameDimension first third := fun base => (h base).trans (h' base)

/-- The total exponent of `base` in a list of factors: the sum of the
exponents of the factors that name it. In a canonical dimension each base
appears at most once, and this is `exponentOf` (`exponent_eq_exponentOf`). -/
def exponent : DimensionVector → DeclId → Int
  | [], _ => 0
  | (factor, power) :: rest, base => (if factor = base then power else 0) + exponent rest base

@[simp] theorem exponentOf_nil (base : DeclId) : exponentOf [] base = 0 := rfl

theorem exponentOf_cons (factor : DeclId) (power : Int) (rest : DimensionVector) (base : DeclId) :
    exponentOf ((factor, power) :: rest) base = if factor = base then power else exponentOf rest base := by
  unfold exponentOf
  rw [List.find?_cons]
  split <;> simp_all

theorem exponentOf_eq_zero {dimension : DimensionVector} {base : DeclId}
    (h : base ∉ dimension.map (·.1)) : exponentOf dimension base = 0 := by
  induction dimension with
  | nil => rfl
  | cons factor rest ih =>
    obtain ⟨b, e⟩ := factor
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [exponentOf_cons, ih h.2]
    simp [Ne.symm h.1]

theorem exponent_eq_zero {dimension : DimensionVector} {base : DeclId}
    (h : base ∉ dimension.map (·.1)) : exponent dimension base = 0 := by
  induction dimension with
  | nil => rfl
  | cons factor rest ih =>
    obtain ⟨b, e⟩ := factor
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [exponent, Ne.symm h.1, ih h.2]

/-- In a dimension that names each base at most once, the total exponent is
the exponent that the kernel reads. -/
theorem exponent_eq_exponentOf {dimension : DimensionVector} (distinct : (dimension.map (·.1)).Nodup)
    (base : DeclId) : exponent dimension base = exponentOf dimension base := by
  induction dimension with
  | nil => rfl
  | cons factor rest ih =>
    obtain ⟨b, e⟩ := factor
    simp only [List.map_cons, List.nodup_cons] at distinct
    rw [exponentOf_cons, exponent]
    by_cases h : b = base
    · subst h
      simp [exponent_eq_zero distinct.1]
    · simp [h, ih distinct.2]

/-- `sameDimension` decides `SameDimension`: a base that neither dimension
names has the exponent `0` in both. -/
theorem sameDimension_iff {first second : DimensionVector} :
    sameDimension first second = true ↔ SameDimension first second := by
  unfold sameDimension SameDimension
  rw [List.all_eq_true]
  constructor
  · intro h base
    by_cases mem : base ∈ (first ++ second).map (·.1)
    · obtain ⟨⟨b, e⟩, member, rfl⟩ := List.mem_map.mp mem
      simpa using h (b, e) member
    · rw [List.map_append, List.mem_append, not_or] at mem
      rw [exponentOf_eq_zero mem.1, exponentOf_eq_zero mem.2]
  · rintro h ⟨base, _⟩ _
    simp [h base]

/-- One step of `addScaled`: the factor of `factor` is replaced by `total`. -/
theorem exponentOf_replace (sum : DimensionVector) (factor : DeclId) (total : Int) (base : DeclId) :
    exponentOf (sum.filter (·.1 != factor) ++ (if total == 0 then [] else [(factor, total)])) base =
      if factor = base then total else exponentOf sum base := by
  induction sum with
  | nil =>
    by_cases ht : total = 0 <;> by_cases hb : factor = base <;> simp [ht, hb, exponentOf_cons]
  | cons head rest ih =>
    obtain ⟨c, f⟩ := head
    by_cases hc : c = factor <;> by_cases hcb : c = base <;> by_cases hfb : factor = base <;>
      simp_all [exponentOf_cons]

/-- **The dimension of a product.** `addScaled dimension k other` adds `k`
times every exponent of `other` to `dimension`. -/
theorem exponentOf_addScaled (k : Int) : ∀ (other dimension : DimensionVector) (base : DeclId),
    exponentOf (addScaled dimension k other) base = exponentOf dimension base + k * exponent other base
  | [], dimension, base => by simp [addScaled, exponent]
  | (b, e) :: rest, dimension, base => by
    have step : addScaled dimension k ((b, e) :: rest) =
        addScaled (dimension.filter (·.1 != b) ++
          (if exponentOf dimension b + k * e == 0 then [] else [(b, exponentOf dimension b + k * e)])) k rest :=
      rfl
    rw [step, exponentOf_addScaled k rest, exponentOf_replace]
    simp only [exponent]
    by_cases h : b = base
    · subst h
      simp only [ite_true]
      rw [Int.mul_add]
      omega
    · simp [h]

/-- A dimension in canonical form (`canonicalDimension`): every factor names a
base dimension, with a nonzero exponent within `Limits.dimensionExponent` in
absolute value, and no base twice. -/
structure CanonicalDimension (env : Environment) (dimension : DimensionVector) : Prop where
  bases : ∀ factor ∈ dimension, lookup env factor.1 = some .baseDimension
  nonzero : ∀ factor ∈ dimension, factor.2 ≠ 0
  bounded : ∀ factor ∈ dimension, factor.2.natAbs ≤ Limits.dimensionExponent
  distinct : (dimension.map (·.1)).Nodup

theorem isBaseDimension_iff {env : Environment} {id : DeclId} :
    isBaseDimension env id = true ↔ lookup env id = some .baseDimension := by
  unfold isBaseDimension
  split <;> simp_all

theorem canonicalDimension_iff {env : Environment} {dimension : DimensionVector} :
    canonicalDimension env dimension = true ↔ CanonicalDimension env dimension := by
  simp only [canonicalDimension, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨each, distinct⟩
    have factor : ∀ factor ∈ dimension, lookup env factor.1 = some .baseDimension ∧ factor.2 ≠ 0 ∧
        factor.2.natAbs ≤ Limits.dimensionExponent := by
      rintro ⟨b, e⟩ member
      have := each (b, e) member
      simp only [isBaseDimension_iff, bne_iff_ne, ne_eq, exponentBounded, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    exact ⟨fun f m => (factor f m).1, fun f m => (factor f m).2.1, fun f m => (factor f m).2.2, distinct⟩
  · rintro ⟨bases, nonzero, bounded, distinct⟩
    refine ⟨?_, distinct⟩
    rintro ⟨b, e⟩ member
    simp only [isBaseDimension_iff, bne_iff_ne, ne_eq, exponentBounded, decide_eq_true_eq]
    exact ⟨⟨bases _ member, nonzero _ member⟩, bounded _ member⟩

/-- In a canonical dimension the total exponent is the exponent the kernel
reads. -/
theorem CanonicalDimension.exponent_eq {env : Environment} {dimension : DimensionVector}
    (canonical : CanonicalDimension env dimension) (base : DeclId) :
    exponent dimension base = exponentOf dimension base :=
  exponent_eq_exponentOf canonical.distinct base

/-! ## Views -/

theorem quantityDimension_eq_some {env : Environment} {id : DeclId} {dimension : DimensionVector} :
    quantityDimension? env id = some dimension ↔ lookup env id = some (.quantity dimension) := by
  unfold quantityDimension?
  split <;> simp_all

theorem smoothCoordinates_eq_some {env : Environment} {id : DeclId} {coordinates : List String} :
    smoothCoordinates? env id = some coordinates ↔
      ∃ implementation, lookup env id = some (.smoothAffine implementation coordinates) := by
  unfold smoothCoordinates?
  split <;> simp_all

/-- `failure` in `Option` is `none`. -/
theorem failure_option {α : Type} : (failure : Option α) = none := rfl

theorem scaleValue_eq_some {env : Environment} {scale : DeclId} {magnitude : Rat} {dimension : DimensionVector} :
    scaleValue env scale = some (magnitude, dimension) ↔
      ∃ quantity, scaleData? env scale = some (quantity, magnitude) ∧ magnitudeValid magnitude = true ∧
        quantityDimension? env quantity = some dimension := by
  unfold scaleValue
  cases data : scaleData? env scale with
  | none => simp
  | some data' =>
    obtain ⟨quantity, magnitude'⟩ := data'
    by_cases valid : magnitudeValid magnitude' = true
    · cases q : quantityDimension? env quantity with
      | none => simp [valid, q, guard]
      | some d =>
        simp [valid, q, guard]
        constructor
        · rintro ⟨rfl, rfl⟩
          exact ⟨quantity, ⟨rfl, rfl⟩, valid, q⟩
        · rintro ⟨_, ⟨rfl, rfl⟩, _, q'⟩
          rw [q] at q'
          exact ⟨rfl, Option.some.inj q'⟩
    · simp [valid, guard, failure_option]
      rintro rfl valid'
      exact absurd valid' valid

/-! ## Declarations (C16) -/

/-- The base dimensions of the environment are its base-dimension entries. -/
theorem mem_baseDimensions {env : Environment} {id : DeclId} :
    id ∈ baseDimensions env ↔ ∃ entry ∈ env, entry.id = id ∧ entry.declaration = .baseDimension := by
  simp only [baseDimensions, List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, h⟩
    refine ⟨entry, member, ?_⟩
    split at h <;> simp_all
  · rintro ⟨entry, member, rfl, h⟩
    exact ⟨entry, member, by simp [h]⟩

/-- **Base dimensions.** An accepted base dimension is one of at most
`Limits.dimensionBases` base dimensions of the program. -/
theorem checkBaseDimension_iff {env : Environment} :
    checkBaseDimension env = true ↔ (baseDimensions env).length ≤ Limits.dimensionBases := by
  simp [checkBaseDimension]

/-- **Quantities.** An accepted quantity kind has a canonical dimension:
every factor names a base dimension, with a nonzero bounded exponent, and no
base twice. -/
theorem checkQuantity_iff {env : Environment} {dimension : DimensionVector} :
    checkQuantity env dimension = true ↔ CanonicalDimension env dimension :=
  canonicalDimension_iff

/-- **Readings.** An accepted reading is declared at a `reading` family
applied to a declared smooth object, and reads each coordinate of the object,
in coordinate order, as a declared quantity: one quantity per coordinate. -/
theorem checkReading_iff {env : Environment} {family object : DeclId} {quantities : List DeclId} :
    checkReading env family object quantities = true ↔
      familyRepresentation env family = some .reading ∧
      validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      (∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
        coordinates.length = quantities.length) ∧
      ∀ quantity ∈ quantities, ∃ dimension, lookup env quantity = some (.quantity dimension) := by
  simp only [checkReading, isReadingFamily, declaredAt, smoothDimension?, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, Option.isSome_iff_exists, Option.map_eq_some_iff, quantityDimension_eq_some]
  constructor
  · rintro ⟨⟨⟨family, declared⟩, coordinates, found, length⟩, each⟩
    obtain ⟨implementation, found⟩ := smoothCoordinates_eq_some.mp found
    exact ⟨family, declared, ⟨implementation, coordinates, found, length⟩, each⟩
  · rintro ⟨family, declared, ⟨implementation, coordinates, found, length⟩, each⟩
    exact ⟨⟨⟨family, declared⟩, coordinates, smoothCoordinates_eq_some.mpr ⟨implementation, found⟩, length⟩, each⟩

/-- **Scales.** An accepted scale is of a declared quantity and has a positive
magnitude within the metric entry bound. -/
theorem checkScale_iff {env : Environment} {quantity : DeclId} {magnitude : Rat} :
    checkScale env quantity magnitude = true ↔
      (∃ dimension, lookup env quantity = some (.quantity dimension)) ∧ 0 < magnitude ∧
        SmoothDeclarations.entryBounded magnitude = true := by
  simp [checkScale, magnitudeValid, Option.isSome_iff_exists, quantityDimension_eq_some]

/-! ## The entries of a physical metric -/

/-- The evaluated entry in row `i`, column `j`. -/
def entryAt (values : List (List (Rat × DimensionVector))) (i j : Nat) : Option (Rat × DimensionVector) :=
  values[i]?.bind (·[j]?)

theorem diagonalEntries_shape (n : Nat) (diagonal : List (Rat × DimensionVector)) :
    (diagonalEntries n diagonal).length = n ∧ ∀ row ∈ diagonalEntries n diagonal, row.length = n := by
  simp only [diagonalEntries, List.length_map, List.length_range, List.mem_map, List.mem_range, true_and]
  rintro _ ⟨i, _, rfl⟩
  simp

theorem entryAt_diagonalEntries (n : Nat) (diagonal : List (Rat × DimensionVector)) (i j : Nat) :
    entryAt (diagonalEntries n diagonal) i j =
      if i < n ∧ j < n then some (if i = j then diagonal.getD i (0, []) else (0, [])) else none := by
  by_cases hi : i < n <;> by_cases hj : j < n <;>
    simp [entryAt, diagonalEntries, hi, hj]

/-- **Euclidean entries.** `euclidean` is the identity, dimensionless. -/
theorem entryValues_euclidean (env : Environment) (n : Nat) (quantities : List DeclId) :
    entryValues env n quantities .euclidean =
      some (diagonalEntries n ((List.range n).map fun _ => (1, []))) := rfl

theorem entryAt_euclidean {n i j : Nat} (hi : i < n) (hj : j < n) :
    entryAt (diagonalEntries n ((List.range n).map fun _ => ((1 : Rat), ([] : DimensionVector)))) i j =
      some (if i = j then 1 else 0, []) := by
  rw [entryAt_diagonalEntries]
  by_cases h : i = j
  · subst h
    simp [hi]
  · simp [h, hi, hj]

/-- **Explicit entries.** `gram rows` evaluates each entry of `n` rows of `n`
scale monomials by `scaleMonomialValue`. -/
theorem entryValues_gram {env : Environment} {n : Nat} {quantities : List DeclId}
    {rows : List (List ScaleMonomial)} {values : List (List (Rat × DimensionVector))}
    (h : entryValues env n quantities (.gram rows) = some values) :
    rows.length = n ∧ (∀ row ∈ rows, row.length = n) ∧ values.length = n ∧ (∀ row ∈ values, row.length = n) ∧
      ∀ i j : Nat, entryAt values i j = (rows[i]?.bind (·[j]?)).bind (scaleMonomialValue env) := by
  simp only [entryValues] at h
  by_cases shape : (rows.length == n && rows.all (·.length == n)) = true
  · simp only [shape, guard, ite_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at shape
    obtain ⟨length, each⟩ := mapM_some_index h
    have columns : ∀ row ∈ values, row.length = n := by
      intro row member
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem member
      have entry := each i
      rw [List.getElem?_eq_getElem hi] at entry
      cases r : rows[i]? with
      | none =>
        rw [r] at entry
        cases entry
      | some r' =>
        rw [r, Option.bind_some] at entry
        rw [(mapM_some_index entry).1]
        obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp r
        exact shape.2 _ (List.getElem_mem bound)
    refine ⟨shape.1, shape.2, by rw [length, shape.1], columns, fun i j => ?_⟩
    rw [entryAt, ← each i]
    cases row : rows[i]? with
    | none => rfl
    | some row' =>
      simp only [Option.bind_some]
      have bound : i < values.length := by
        rw [length]; exact (List.getElem?_eq_some_iff.mp row).1
      cases mapped : row'.mapM (scaleMonomialValue env) with
      | none =>
        have entry := each i
        rw [row, Option.bind_some, mapped, List.getElem?_eq_getElem bound] at entry
        cases entry
      | some entries =>
        obtain ⟨_, each'⟩ := mapM_some_index mapped
        simp [← each' j]
  · simp only [shape, guard] at h
    nomatch h

/-- `c · Π mᵢ^{eᵢ}` for the factors `((sᵢ, eᵢ), (mᵢ, dᵢ))`, multiplied from
the left as the kernel multiplies. -/
def monomialMagnitude (coefficient : Rat) : List ((DeclId × Int) × (Rat × DimensionVector)) → Rat
  | [] => coefficient
  | ((_, power), (magnitude, _)) :: rest => monomialMagnitude (coefficient * magnitude ^ power) rest

/-- `Σ eᵢ · exponent(dᵢ, base)`: the exponent of `base` in the dimension of a
product of scales. -/
def monomialExponent : List ((DeclId × Int) × (Rat × DimensionVector)) → DeclId → Int
  | [], _ => 0
  | ((_, power), (_, dimension)) :: rest, base => power * exponent dimension base + monomialExponent rest base

/-- `guard p >>= f` succeeds only when `p` holds. -/
theorem guard_bind_eq_some {p : Prop} [Decidable p] {α : Type} {f : Unit → Option α} {x : α}
    (h : (guard p >>= f) = some x) : p ∧ f () = some x := by
  by_cases hp : p
  · simp only [guard, hp, ite_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
    exact ⟨hp, h⟩
  · simp only [guard, hp, ite_false, failure_option, Option.bind_eq_bind, Option.bind_none] at h
    nomatch h

/-- The fold of `scaleStep` in `scaleMonomialValue`: each step multiplies by
a scale's magnitude raised to its exponent and adds its dimension times the
exponent. -/
theorem foldl_scaleStep :
    ∀ (factors : List ((DeclId × Int) × (Rat × DimensionVector))) (value : Rat) (dimension : DimensionVector),
      (factors.foldl scaleStep (value, dimension)).1 = monomialMagnitude value factors ∧
      ∀ base, exponentOf (factors.foldl scaleStep (value, dimension)).2 base =
        exponentOf dimension base + monomialExponent factors base
  | [], value, dimension => ⟨rfl, fun base => by simp [monomialExponent]⟩
  | ((scale, power), (magnitude, scaleDimension)) :: rest, value, dimension => by
    have step : (((scale, power), (magnitude, scaleDimension)) :: rest).foldl scaleStep (value, dimension) =
        rest.foldl scaleStep (value * magnitude ^ power, addScaled dimension power scaleDimension) := rfl
    obtain ⟨magnitudeEq, exponentEq⟩ :=
      foldl_scaleStep rest (value * magnitude ^ power) (addScaled dimension power scaleDimension)
    rw [step]
    refine ⟨magnitudeEq, fun base => ?_⟩
    rw [exponentEq base, exponentOf_addScaled]
    simp only [monomialExponent]
    omega

/-- **The dimension of a product of scales (ADR 0002 "Laws").** An entry
`c · Π sᵢ^{eᵢ}` that the kernel evaluates has at most
`Limits.dimensionScaleFactors` factors, a bounded coefficient, distinct
scales and nonzero bounded exponents. Every factor names a valid scale with
magnitude `mᵢ` and dimension `dᵢ`; the value is `c · Π mᵢ^{eᵢ}`, and the
dimension is `Σ eᵢ · dᵢ`. -/
theorem scaleMonomialValue_sound {env : Environment} {monomial : ScaleMonomial} {value : Rat}
    {dimension : DimensionVector} (h : scaleMonomialValue env monomial = some (value, dimension)) :
    monomial.factors.length ≤ Limits.dimensionScaleFactors ∧
      SmoothDeclarations.entryBounded monomial.coefficient = true ∧
      (monomial.factors.map (·.1)).Nodup ∧
      (∀ factor ∈ monomial.factors, factor.2 ≠ 0 ∧ factor.2.natAbs ≤ Limits.dimensionExponent) ∧
      ∃ scales, monomial.factors.mapM (fun factor => scaleValue env factor.1) = some scales ∧
        value = monomialMagnitude monomial.coefficient (monomial.factors.zip scales) ∧
        ∀ base, exponentOf dimension base = monomialExponent (monomial.factors.zip scales) base := by
  unfold scaleMonomialValue at h
  obtain ⟨count, h⟩ := guard_bind_eq_some h
  obtain ⟨bounded, h⟩ := guard_bind_eq_some h
  obtain ⟨distinct, h⟩ := guard_bind_eq_some h
  obtain ⟨exponents, h⟩ := guard_bind_eq_some h
  cases mapped : monomial.factors.mapM (fun factor => scaleValue env factor.1) with
  | none => simp [mapped] at h
  | some scales =>
    simp only [mapped, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨_, h⟩ := guard_bind_eq_some h
    simp only [Option.pure_def, Option.some.injEq] at h
    obtain ⟨magnitudeEq, exponentEq⟩ := foldl_scaleStep (monomial.factors.zip scales) monomial.coefficient []
    rw [h] at magnitudeEq exponentEq
    refine ⟨count, bounded, distinct, ?_, scales, rfl, magnitudeEq, fun base => ?_⟩
    · rintro ⟨scale, power⟩ member
      have each := List.all_eq_true.mp exponents (scale, power) member
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, exponentBounded, decide_eq_true_eq] at each
      exact each
    · simpa using exponentEq base

/-- **Normalized entries.** `normalized scales` names one scale per
coordinate, in coordinate order, of exactly the coordinate's quantity, and its
diagonal is `1 / sᵢ²` of dimension `-2 · dim(sᵢ)`. -/
theorem entryValues_normalized {env : Environment} {n : Nat} {quantities scales : List DeclId}
    {values : List (List (Rat × DimensionVector))}
    (h : entryValues env n quantities (.normalized scales) = some values) :
    scales.length = n ∧ quantities.length = n ∧
      ∃ diagonal, values = diagonalEntries n diagonal ∧ diagonal.length = n ∧
        ∀ (i : Nat) scale quantity, scales[i]? = some scale → quantities[i]? = some quantity →
          ∃ magnitude dimension, scaleData? env scale = some (quantity, magnitude) ∧
            quantityDimension? env quantity = some dimension ∧
            diagonal[i]? = some (1 / (magnitude * magnitude), addScaled [] (-2) dimension) := by
  simp only [entryValues] at h
  by_cases shape : (scales.length == n && quantities.length == n) = true
  · simp only [shape, guard, ite_true, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at shape
    obtain ⟨diagonal, mapped, rfl⟩ := h
    obtain ⟨length, each⟩ := mapM_some_index mapped
    refine ⟨shape.1, shape.2, diagonal, rfl, by simp [length, shape.1, shape.2], ?_⟩
    intro i scale quantity hs hq
    have pair : (scales.zip quantities)[i]? = some (scale, quantity) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hs, hq⟩
    have bound : i < diagonal.length := by
      rw [length]; exact (List.getElem?_eq_some_iff.mp pair).1
    have entry := each i
    rw [pair, Option.bind_some, List.getElem?_eq_getElem bound] at entry
    rw [List.getElem?_eq_getElem bound]
    generalize diagonal[i] = d at entry ⊢
    simp only at entry
    cases data : scaleData? env scale with
    | none => simp [data] at entry
    | some data' =>
      obtain ⟨kind, magnitude⟩ := data'
      by_cases same : kind = quantity
      · subst same
        cases value : scaleValue env scale with
        | none => simp [data, value, failure_option] at entry
        | some value' =>
          obtain ⟨magnitude', dimension⟩ := value'
          obtain ⟨kind', data', _, dimension'⟩ := scaleValue_eq_some.mp value
          rw [data] at data'
          simp only [Option.some.injEq, Prod.mk.injEq] at data'
          obtain ⟨rfl, rfl⟩ := data'
          simp [data, value] at entry
          exact ⟨magnitude, dimension, rfl, dimension', by rw [entry]⟩
      · simp [data, same, failure_option] at entry
  · simp only [shape, guard] at h
    nomatch h

/-! ## The terms of a physical metric -/

/-- The dimension of the term `g_ij dxⁱ dxʲ`: the dimension `entry` of
`g_ij` plus the dimensions of the quantities of `xⁱ` and `xʲ`, read from
`coordinates`. -/
def termDimension (coordinates : List DimensionVector) (entry : DimensionVector) (i j : Nat) : DimensionVector :=
  addScaled (addScaled entry 1 (coordinates.getD i [])) 1 (coordinates.getD j [])

/-- The exponents of a term dimension: those of the entry plus those of the
two coordinates. -/
theorem exponentOf_termDimension (coordinates : List DimensionVector) (entry : DimensionVector) (i j : Nat)
    (base : DeclId) :
    exponentOf (termDimension coordinates entry i j) base =
      exponentOf entry base + exponent (coordinates.getD i []) base + exponent (coordinates.getD j []) base := by
  simp [termDimension, exponentOf_addScaled]

/-- The term in row `i`, column `j` of the evaluated entries `values` has a
nonzero entry, and `dimension` is its term dimension. -/
def NonzeroTerm (coordinates : List DimensionVector) (values : List (List (Rat × DimensionVector)))
    (i j : Nat) (dimension : DimensionVector) : Prop :=
  ∃ magnitude entry, entryAt values i j = some (magnitude, entry) ∧ magnitude ≠ 0 ∧
    dimension = termDimension coordinates entry i j

/-- `nonzeroTerms` lists exactly the nonzero terms with their term
dimensions. -/
theorem mem_nonzeroTerms {coordinates : List DimensionVector} {values : List (List (Rat × DimensionVector))}
    {i j : Nat} {dimension : DimensionVector} :
    (i, j, dimension) ∈ nonzeroTerms coordinates values ↔ NonzeroTerm coordinates values i j dimension := by
  simp only [nonzeroTerms, List.mem_flatMap, List.mem_filterMap, NonzeroTerm, entryAt]
  constructor
  · rintro ⟨⟨row, i'⟩, hrow, ⟨⟨magnitude, entry⟩, j'⟩, hentry, h⟩
    rw [List.mem_zipIdx_iff_getElem?] at hrow hentry
    by_cases zero : magnitude = 0
    · simp [zero] at h
    · simp only [zero, beq_iff_eq, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨magnitude, entry, by simp [hrow, hentry], zero, rfl⟩
  · rintro ⟨magnitude, entry, found, nonzero, rfl⟩
    cases hrow : values[i]? with
    | none => simp [hrow] at found
    | some row =>
      rw [hrow, Option.bind_some] at found
      refine ⟨(row, i), List.mem_zipIdx_iff_getElem?.mpr hrow, ((magnitude, entry), j),
        List.mem_zipIdx_iff_getElem?.mpr found, ?_⟩
      simp [nonzero, termDimension]

/-- `consistentValue` holds when every two nonzero terms have one dimension,
and a declared value is the dimension of every nonzero term, of which there is
at least one. -/
theorem consistentValue_sound {terms : List (Nat × Nat × DimensionVector)} {value : Option DimensionVector}
    (h : consistentValue terms value = true) :
    (∀ t ∈ terms, ∀ t' ∈ terms, SameDimension t.2.2 t'.2.2) ∧
      ∀ v, value = some v → terms ≠ [] ∧ ∀ t ∈ terms, SameDimension t.2.2 v := by
  cases terms with
  | nil =>
    simp only [consistentValue, Option.isNone_iff_eq_none] at h
    subst h
    simp
  | cons first rest =>
    obtain ⟨i, j, d⟩ := first
    simp only [consistentValue, Bool.and_eq_true, List.all_eq_true, sameDimension_iff] at h
    obtain ⟨⟨_, each⟩, declared⟩ := h
    have toFirst : ∀ t ∈ (i, j, d) :: rest, SameDimension t.2.2 d := by
      intro t member
      rcases List.mem_cons.mp member with rfl | member
      · exact SameDimension.refl _
      · exact (each t member).symm
    refine ⟨fun t mt t' mt' => (toFirst t mt).trans (toFirst t' mt').symm, fun v hv => ⟨by simp, ?_⟩⟩
    subst hv
    simp only [Option.all_some, sameDimension_iff] at declared
    exact fun t member => (toFirst t member).trans declared

/-- **The value can be declared.** When `consistentValue` holds, every
exponent of the dimension of every term is within `Limits.dimensionExponent`
in absolute value, so the value of an accepted physical metric is a
dimension that `value = …` can write. -/
theorem consistentValue_bounded {terms : List (Nat × Nat × DimensionVector)} {value : Option DimensionVector}
    (h : consistentValue terms value = true) :
    ∀ t ∈ terms, ∀ base, (exponentOf t.2.2 base).natAbs ≤ Limits.dimensionExponent := by
  cases terms with
  | nil => simp
  | cons first rest =>
    obtain ⟨i, j, d⟩ := first
    simp only [consistentValue, dimensionBounded, Bool.and_eq_true, List.all_eq_true, sameDimension_iff] at h
    obtain ⟨⟨bounded, each⟩, _⟩ := h
    have own : ∀ base, (exponentOf d base).natAbs ≤ Limits.dimensionExponent := by
      intro base
      unfold exponentOf
      cases found : d.find? (·.1 == base) with
      | none => simp
      | some factor =>
        obtain ⟨b, e⟩ := factor
        have bound := bounded (b, e) (List.mem_of_find?_eq_some found)
        simpa [exponentBounded] using bound
    intro t member base
    rcases List.mem_cons.mp member with rfl | member
    · exact own base
    · rw [← each t member base]
      exact own base

/-- The evaluated entries equal the Gram matrix entry by entry, so as
matrices. -/
theorem entriesEqual_sound {n : Nat} {gram : SmoothRuntime.Matrix} {values : List (List (Rat × DimensionVector))}
    (square : SmoothDeclarations.square n gram = true) (rows : values.length = n)
    (columns : ∀ row ∈ values, row.length = n) (h : entriesEqual gram values = true) :
    values.map (·.map Prod.fst) = gram := by
  simp only [SmoothDeclarations.square, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at square
  simp only [entriesEqual, List.all_eq_true] at h
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  by_cases hi : i < n
  · have hv : i < values.length := by omega
    have hg : i < gram.length := by omega
    rw [List.getElem?_eq_getElem hv, List.getElem?_eq_getElem hg, Option.map_some, Option.some.injEq]
    have row := h (values[i], i) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hv))
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map]
    have lengthV := columns values[i] (List.getElem_mem hv)
    have lengthG := square.2 gram[i] (List.getElem_mem hg)
    by_cases hj : j < n
    · have hvj : j < values[i].length := by omega
      have hgj : j < gram[i].length := by omega
      rw [List.getElem?_eq_getElem hvj, List.getElem?_eq_getElem hgj, Option.map_some, Option.some.injEq]
      have entry := row (values[i][j], j) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hvj))
      simp only [beq_iff_eq] at entry
      rw [entry, SmoothDeclarations.entry, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hg, Option.getD_some, List.getElem?_eq_getElem hgj, Option.getD_some]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), Option.map_none]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega), Option.map_none]

/-- The shape of the evaluated entries: `n` rows of `n` entries. -/
theorem entryValues_shape {env : Environment} {n : Nat} {quantities : List DeclId} {entries : PhysicalGram}
    {values : List (List (Rat × DimensionVector))} (h : entryValues env n quantities entries = some values) :
    values.length = n ∧ ∀ row ∈ values, row.length = n := by
  cases entries with
  | euclidean =>
    rw [entryValues_euclidean, Option.some.injEq] at h
    subst h
    exact diagonalEntries_shape n _
  | gram rows =>
    obtain ⟨_, _, length, columns, _⟩ := entryValues_gram h
    exact ⟨length, columns⟩
  | normalized scales =>
    obtain ⟨_, _, diagonal, rfl, _⟩ := entryValues_normalized h
    exact diagonalEntries_shape n _

/-! ## Soundness of an accepted physical metric (C17–C19) -/

/-- What an accepted physical metric states about its data. `n` is the
dimension of the object, `gram` the Gram matrix of the metric, `quantities`
the reading of the coordinates, `dimensions` their dimensions, and `values`
the evaluated entries, each a magnitude and a dimension:

- the metric is a metric of the object (`metricOf`), and the reading is a
  reading of the object (`readingOf`) with one quantity per coordinate
  (`perCoordinate`);
- the evaluated entries are the Gram matrix of the metric (`evaluates`);
- for `normalized`, each scale is of exactly its coordinate's quantity
  (`normalizedKinds`);
- every two nonzero terms have one term dimension (`oneDimension`), and a
  declared value is the term dimension of every nonzero term, of which there
  is at least one (`declaredValue`). -/
structure Interprets (env : Environment) (object metric reading : DeclId) (value : Option DimensionVector)
    (entries : PhysicalGram) (n : Nat) (gram : SmoothRuntime.Matrix) (quantities : List DeclId)
    (dimensions : List DimensionVector) (values : List (List (Rat × DimensionVector))) : Prop where
  metricOf : metricData? env metric = some (object, n, gram)
  readingOf : ∃ family, readingData? env reading = some (family, object, quantities)
  perCoordinate : quantities.length = n
  square : SmoothDeclarations.square n gram = true
  quantityDimensions : quantities.mapM (quantityDimension? env) = some dimensions
  evaluated : entryValues env n quantities entries = some values
  evaluates : values.map (·.map Prod.fst) = gram
  normalizedKinds : ∀ scales, entries = .normalized scales →
    ∀ (i : Nat) scale quantity, scales[i]? = some scale → quantities[i]? = some quantity →
      ∃ magnitude, scaleData? env scale = some (quantity, magnitude)
  oneDimension : ∀ i j d i' j' d', NonzeroTerm dimensions values i j d → NonzeroTerm dimensions values i' j' d' →
    SameDimension d d'
  declaredValue : ∀ v, value = some v → (∃ i j d, NonzeroTerm dimensions values i j d) ∧
    ∀ i j d, NonzeroTerm dimensions values i j d → SameDimension d v

/-- **Soundness of an accepted physical metric.** An accepted interpretation
is declared at a `physical_metric` family applied to its object, its declared
value is canonical, and it `Interprets` a metric of its object under a reading
of its object. -/
theorem physicalMetric_sound {env : Environment} {family object metric reading : DeclId}
    {value : Option DimensionVector} {entries : PhysicalGram}
    (h : checkPhysicalMetric env family object metric reading value entries = true) :
    isPhysicalMetricFamily env family = true ∧ declaredAt env family object = true ∧
      (∀ v, value = some v → CanonicalDimension env v) ∧
      ∃ n gram quantities dimensions values,
        Interprets env object metric reading value entries n gram quantities dimensions values := by
  unfold checkPhysicalMetric at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨physical, declared⟩, canonical⟩, h⟩ := h
  refine ⟨physical, declared, fun v hv => ?_, ?_⟩
  · subst hv
    exact canonicalDimension_iff.mp (by simpa using canonical)
  cases hm : metricData? env metric with
  | none => simp [hm] at h
  | some m =>
    obtain ⟨metricObject, n, gram⟩ := m
    cases hr : readingData? env reading with
    | none => simp [hm, hr] at h
    | some r =>
      obtain ⟨readingFamily, readingObject, quantities⟩ := r
      simp only [hm, hr, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨sameMetric, sameReading⟩, coordinates⟩, square⟩, terms⟩ := h
      subst sameMetric sameReading
      cases hd : quantities.mapM (quantityDimension? env) with
      | none => simp [hd] at terms
      | some dimensions =>
        cases hv : entryValues env n quantities entries with
        | none => simp [hd, hv] at terms
        | some values =>
          simp only [hd, hv, Bool.and_eq_true] at terms
          obtain ⟨equal, consistent⟩ := terms
          obtain ⟨rows, columns⟩ := entryValues_shape hv
          obtain ⟨one, declaredValue⟩ := consistentValue_sound consistent
          refine ⟨n, gram, quantities, dimensions, values, ⟨hm, ⟨readingFamily, hr⟩, coordinates, square, hd, hv,
            entriesEqual_sound square rows columns equal, ?_, ?_, ?_⟩⟩
          · rintro scales rfl i scale quantity hs hq
            obtain ⟨_, _, _, _, _, each⟩ := entryValues_normalized hv
            obtain ⟨magnitude, _, data, _, _⟩ := each i scale quantity hs hq
            exact ⟨magnitude, data⟩
          · intro i j d i' j' d' t t'
            exact one _ (mem_nonzeroTerms.mpr t) _ (mem_nonzeroTerms.mpr t')
          · intro v hv
            obtain ⟨nonempty, each⟩ := declaredValue v hv
            refine ⟨?_, fun i j d t => each _ (mem_nonzeroTerms.mpr t)⟩
            obtain ⟨⟨i, j, d⟩, member⟩ := List.exists_mem_of_ne_nil _ nonempty
            exact ⟨i, j, d, mem_nonzeroTerms.mp member⟩

/-! ## The Euclidean metric (C17) -/

/-- **The Euclidean metric needs one dimension.** An accepted `euclidean`
interpretation reads every coordinate with one dimension: the term `dxᵢ²`
has twice the dimension of `xᵢ`, and every two of these terms agree. -/
theorem euclidean_sound {env : Environment} {family object metric reading : DeclId}
    {value : Option DimensionVector}
    (h : checkPhysicalMetric env family object metric reading value .euclidean = true) :
    ∃ readingFamily quantities dimensions, readingData? env reading = some (readingFamily, object, quantities) ∧
      quantities.mapM (quantityDimension? env) = some dimensions ∧
      ∀ i j, i < quantities.length → j < quantities.length → ∀ base,
        exponent (dimensions.getD i []) base = exponent (dimensions.getD j []) base := by
  obtain ⟨_, _, _, n, gram, quantities, dimensions, values, sound⟩ := physicalMetric_sound h
  obtain ⟨readingFamily, read⟩ := sound.readingOf
  refine ⟨readingFamily, quantities, dimensions, read, sound.quantityDimensions, fun i j hi hj base => ?_⟩
  have evaluated := sound.evaluated
  rw [entryValues_euclidean, Option.some.injEq] at evaluated
  rw [sound.perCoordinate] at hi hj
  have term : ∀ k, k < n → NonzeroTerm dimensions values k k (termDimension dimensions [] k k) := by
    intro k hk
    refine ⟨1, [], ?_, by decide, rfl⟩
    rw [← evaluated, entryAt_euclidean hk hk]
    simp
  have same := sound.oneDimension i i _ j j _ (term i hi) (term j hj) base
  rw [exponentOf_termDimension, exponentOf_termDimension] at same
  simp only [exponentOf_nil, Int.zero_add] at same
  omega

/-- **`dx² + dt²` is rejected (C17).** Under a reading of a coordinate of
dimension `L` and a coordinate of dimension `T`, two distinct base
dimensions, the Euclidean metric has no physical interpretation, whatever its
declared value: `dx²` has dimension `L²` and `dt²` has dimension `T²`. -/
theorem euclidean_rejected {env : Environment} {family object metric reading readingFamily length time L T : DeclId}
    {value : Option DimensionVector}
    (read : readingData? env reading = some (readingFamily, object, [length, time]))
    (lengthDimension : quantityDimension? env length = some [(L, 1)])
    (timeDimension : quantityDimension? env time = some [(T, 1)]) (distinct : L ≠ T) :
    checkPhysicalMetric env family object metric reading value .euclidean = false := by
  cases accepted : checkPhysicalMetric env family object metric reading value .euclidean with
  | false => rfl
  | true =>
    obtain ⟨_, quantities, dimensions, read', mapped, same⟩ := euclidean_sound accepted
    rw [read, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at read'
    obtain ⟨_, _, rfl⟩ := read'
    simp only [List.mapM_cons, List.mapM_nil, lengthDimension, timeDimension, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at mapped
    subst mapped
    have := same 0 1 (by simp) (by simp) L
    simp [exponent, Ne.symm distinct] at this

/-! ## Kinds (C19) -/

/-- **Kinds are not dimensions (C19).** `normalized` is rejected when a scale
is of another quantity kind than its coordinate, whatever their dimensions
and magnitudes. -/
theorem normalized_rejected_of_kind {env : Environment} {family object metric reading readingFamily : DeclId}
    {value : Option DimensionVector} {quantities scales : List DeclId} {i : Nat} {scale quantity kind : DeclId}
    {magnitude : Rat}
    (read : readingData? env reading = some (readingFamily, object, quantities))
    (coordinate : quantities[i]? = some quantity) (named : scales[i]? = some scale)
    (scaleKind : scaleData? env scale = some (kind, magnitude)) (different : kind ≠ quantity) :
    checkPhysicalMetric env family object metric reading value (.normalized scales) = false := by
  cases accepted : checkPhysicalMetric env family object metric reading value (.normalized scales) with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, n, gram, quantities', dimensions, values, sound⟩ := physicalMetric_sound accepted
    obtain ⟨_, read'⟩ := sound.readingOf
    rw [read, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at read'
    obtain ⟨_, _, rfl⟩ := read'
    obtain ⟨_, found⟩ := sound.normalizedKinds scales rfl i scale quantity named coordinate
    rw [scaleKind, Option.some.injEq, Prod.mk.injEq] at found
    exact absurd found.1 different

/-! ## Nature declarations of a valid environment -/

theorem entry_of_lookup {env : Environment} {id : DeclId} {declaration : Declaration}
    (found : lookup env id = some declaration) : ∃ entry ∈ env, entry.declaration = declaration := by
  unfold lookup at found
  cases entry : env.find? (fun entry => entry.id == id) with
  | none => simp [entry] at found
  | some e =>
    simp only [entry, Option.map_some, Option.some.injEq] at found
    exact ⟨e, List.mem_of_find?_eq_some entry, found⟩

/-- In a valid environment every quantity kind has a canonical dimension. -/
theorem valid_quantity {env : Environment} (valid : env.Valid) {id : DeclId} {dimension : DimensionVector}
    (found : lookup env id = some (.quantity dimension)) : CanonicalDimension env dimension := by
  obtain ⟨entry, member, declaration⟩ := entry_of_lookup found
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, declaration] at accepted
  exact checkQuantity_iff.mp accepted

/-- In a valid environment every scale has a positive magnitude, of a
declared quantity. -/
theorem valid_scale {env : Environment} (valid : env.Valid) {id quantity : DeclId} {magnitude : Rat}
    (found : lookup env id = some (.scale quantity magnitude)) :
    (∃ dimension, lookup env quantity = some (.quantity dimension)) ∧ 0 < magnitude := by
  obtain ⟨entry, member, declaration⟩ := entry_of_lookup found
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, declaration] at accepted
  obtain ⟨quantityFound, positive, _⟩ := checkScale_iff.mp accepted
  exact ⟨quantityFound, positive⟩

/-- In a valid environment every reading reads each coordinate of its smooth
object as a declared quantity. -/
theorem valid_reading {env : Environment} (valid : env.Valid) {id family object : DeclId}
    {quantities : List DeclId} (found : lookup env id = some (.reading family object quantities)) :
    (∃ implementation coordinates, lookup env object = some (.smoothAffine implementation coordinates) ∧
      coordinates.length = quantities.length) ∧
      ∀ quantity ∈ quantities, ∃ dimension, lookup env quantity = some (.quantity dimension) := by
  obtain ⟨entry, member, declaration⟩ := entry_of_lookup found
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, declaration] at accepted
  obtain ⟨_, _, coordinates, quantitiesFound⟩ := checkReading_iff.mp accepted
  exact ⟨coordinates, quantitiesFound⟩

/-- In a valid environment every physical metric `Interprets` a metric of its
object under a reading of its object. -/
theorem valid_physicalMetric {env : Environment} (valid : env.Valid) {id family object metric reading : DeclId}
    {value : Option DimensionVector} {entries : PhysicalGram}
    (found : lookup env id = some (.physicalMetric family object metric reading value entries)) :
    ∃ n gram quantities dimensions values,
      Interprets env object metric reading value entries n gram quantities dimensions values := by
  obtain ⟨entry, member, declaration⟩ := entry_of_lookup found
  have accepted := valid.declarations entry member
  simp only [Entry.Valid, declaration] at accepted
  exact (physicalMetric_sound accepted).2.2.2

/-! ## The roadmap example by computation (C17, C18)

A concrete environment: the smooth object `X[x, t]`, its Euclidean metric
`E` and the metric `G = diag(1/9, 1/4)`, the base dimensions `L` and `T`, the
quantities `Length = L` and `Time = T`, the reading `phys` with
`x: Length, t: Time`, and the scales `l0 = 3` of `Length` and `t0 = 2` of
`Time`. The kernel evaluates every check below (`decide +kernel`); no
`native_decide` and no axiom beyond Lean's own. -/

/-- The parents of a classification; other declarations have none. -/
def parentsOf : Declaration → List DeclId
  | .classification parents _ => parents
  | _ => []

/-- The check of an entry without parents does not read the class ranks. -/
theorem validEntry_ranks {env : Environment} {entry : Entry} (orphan : parentsOf entry.declaration = [])
    (ranks ranks' : List (DeclId × Nat)) : validEntry env ranks entry = validEntry env ranks' entry := by
  cases h : entry.declaration <;> simp_all [validEntry, parentsOf, validParents]

namespace Roadmap

/-- A declaration of the example. Short names keep the kernel's string
comparisons cheap. -/
def ident (name : String) : DeclId := ⟨⟨⟨"n", "n", "0"⟩, []⟩, name⟩

/-- A family with one smooth object parameter. -/
def objectFamily (representation : FamilyRepresentation) : Declaration :=
  .family ⟨[.object (ident "A")], [.canonical 0], representation⟩

/-- The std and nature declarations of the example: besides the roadmap
declarations, the metrics `G5 = diag(1/9, 1/5)` and `Mink = diag(1, -9)`, the
quantities `Wavelength = L` and `Speed = L·T⁻¹`, and the scales `l1 = 2` of
`Length`, `w = 3` of `Wavelength` and `c = 3` of `Speed`. -/
def env : Environment := [
  ⟨ident "R", .marker⟩,
  ⟨ident "S", .implementation (ident "R") .smoothAffine []⟩,
  ⟨ident "A", .classification [] [ident "S"]⟩,
  ⟨ident "X", .smoothAffine (ident "S") ["x", "t"]⟩,
  ⟨ident "M", objectFamily .metricForm⟩,
  ⟨ident "E", .metric (ident "M") (ident "X") [[1, 0], [0, 1]]⟩,
  ⟨ident "G", .metric (ident "M") (ident "X") [[1 / 9, 0], [0, 1 / 4]]⟩,
  ⟨ident "G5", .metric (ident "M") (ident "X") [[1 / 9, 0], [0, 1 / 5]]⟩,
  ⟨ident "Mink", .metric (ident "M") (ident "X") [[1, 0], [0, -9]]⟩,
  ⟨ident "Rd", objectFamily .reading⟩,
  ⟨ident "P", objectFamily .physicalMetric⟩,
  ⟨ident "L", .baseDimension⟩,
  ⟨ident "T", .baseDimension⟩,
  ⟨ident "Length", .quantity [(ident "L", 1)]⟩,
  ⟨ident "Time", .quantity [(ident "T", 1)]⟩,
  ⟨ident "Wave", .quantity [(ident "L", 1)]⟩,
  ⟨ident "Speed", .quantity [(ident "L", 1), (ident "T", -1)]⟩,
  ⟨ident "phys", .reading (ident "Rd") (ident "X") [ident "Length", ident "Time"]⟩,
  ⟨ident "l0", .scale (ident "Length") 3⟩,
  ⟨ident "t0", .scale (ident "Time") 2⟩,
  ⟨ident "l1", .scale (ident "Length") 2⟩,
  ⟨ident "w", .scale (ident "Wave") 3⟩,
  ⟨ident "c", .scale (ident "Speed") 3⟩]

/-- `gram((x^-2, 0), (0, t^-2))` for the scales `x` and `t`. -/
def scaledBy (x t : String) : PhysicalGram :=
  .gram [[⟨1, [(ident x, -2)]⟩, ⟨0, []⟩], [⟨0, []⟩, ⟨1, [(ident t, -2)]⟩]]

/-- `gram((l0^-2, 0), (0, t0^-2))`. -/
def scaled : PhysicalGram := scaledBy "l0" "t0"

/-- The example with `interpret(G, reading = phys, gram((l0^-2, 0), (0, t0^-2)), value = 1)`. -/
def interpreted : Environment :=
  env ++ [⟨ident "PG", .physicalMetric (ident "P") (ident "X") (ident "G") (ident "phys") (some []) scaled⟩]

/-- The interpretation of `E` under `phys`. -/
def euclideanEntry : Entry :=
  ⟨ident "PE", .physicalMetric (ident "P") (ident "X") (ident "E") (ident "phys") none .euclidean⟩

/-- The example with `interpret(E, reading = phys, euclidean)`. -/
def euclidean : Environment := env ++ [euclideanEntry]

/-- **C18.** With `l0 = 3` and `t0 = 2`, `gram((l0^-2, 0), (0, t0^-2))`
interprets `G = diag(1/9, 1/4)`, dimensionless. -/
theorem scaled_accepted :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G") (ident "phys") (some []) scaled = true := by
  decide +kernel

/-- **C18.** The whole example with the scaled interpretation is a valid
environment. -/
theorem interpreted_valid : interpreted.Valid := by
  have orphans : interpreted.all (fun entry => parentsOf entry.declaration == []) = true := by decide +kernel
  have entries : interpreted.all (validEntry interpreted []) = true := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, fun entry member => ?_⟩
  have orphan : parentsOf entry.declaration = [] := by
    simpa using List.all_eq_true.mp orphans entry member
  rw [← Audit.validEntry_iff, validEntry_ranks orphan _ []]
  exact List.all_eq_true.mp entries entry member

/-- **C17.** The Euclidean metric under `phys` is rejected, whatever the
declared value, by `euclidean_rejected`. -/
theorem euclidean_check_rejected (value : Option DimensionVector) :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "E") (ident "phys") value .euclidean = false :=
  euclidean_rejected (readingFamily := ident "Rd") (length := ident "Length") (time := ident "Time")
    (L := ident "L") (T := ident "T") (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **C17.** The same rejection, evaluated by the kernel. -/
theorem euclidean_check_rejected' :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "E") (ident "phys") none .euclidean = false := by
  decide +kernel

/-- **C17.** No environment of the example with the Euclidean interpretation
is valid. -/
theorem euclidean_invalid : ¬ euclidean.Valid := by
  intro valid
  have accepted := valid.declarations euclideanEntry (List.mem_append_right _ (List.mem_singleton_self _))
  have rejected : checkPhysicalMetric euclidean (ident "P") (ident "X") (ident "E") (ident "phys") none
      .euclidean = false :=
    euclidean_rejected (readingFamily := ident "Rd") (length := ident "Length") (time := ident "Time")
      (L := ident "L") (T := ident "T") (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simp [Entry.Valid, euclideanEntry, rejected] at accepted

/-- **C18.** An entry whose magnitude differs from the metric is rejected:
`gram((l0^-2, 0), (0, t0^-2))` does not interpret `G5 = diag(1/9, 1/5)`. -/
theorem mismatch_rejected :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G5") (ident "phys") none scaled = false := by
  decide +kernel

/-- **C18.** A scale of the wrong dimension is rejected although the
magnitudes agree: with `l1 = 2` of `Length`, `gram((l0^-2, 0), (0, l1^-2))`
evaluates to `G`, but `dx²/l0²` is dimensionless and `dt²/l1²` has the
dimension `L⁻²T²`. -/
theorem wrong_dimension_rejected :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G") (ident "phys") none (scaledBy "l0" "l1") =
      false := by
  decide +kernel

/-- **C18.** `dx² − c²dt²` with the speed scale `c = 3` interprets
`diag(1, -9)`, with the value `L²`. -/
theorem minkowski_accepted :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "Mink") (ident "phys") (some [(ident "L", 2)])
      (.gram [[⟨1, []⟩, ⟨0, []⟩], [⟨0, []⟩, ⟨-1, [(ident "c", 2)]⟩]]) = true := by
  decide +kernel

/-- **C19.** `normalized(x: l0, t: t0)` interprets `G`. -/
theorem normalized_accepted :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G") (ident "phys") none
      (.normalized [ident "l0", ident "t0"]) = true := by
  decide +kernel

/-- **C19.** `normalized` with the `Wavelength` scale `w = 3` on the `Length`
coordinate `x` is rejected, although `w` has the dimension and the magnitude
of `l0`: by `normalized_rejected_of_kind`. -/
theorem wavelength_rejected :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G") (ident "phys") none
      (.normalized [ident "w", ident "t0"]) = false :=
  normalized_rejected_of_kind (readingFamily := ident "Rd") (quantities := [ident "Length", ident "Time"])
    (i := 0) (quantity := ident "Length") (kind := ident "Wave") (magnitude := 3) (by decide +kernel) rfl rfl
    (by decide +kernel) (by decide +kernel)

/-- **C19.** In explicit rows only dimensions count, so `w` may stand for a
length there. -/
theorem wavelength_rows_accepted :
    checkPhysicalMetric env (ident "P") (ident "X") (ident "G") (ident "phys") (some []) (scaledBy "w" "t0") =
      true := by
  decide +kernel

end Roadmap

end VastitasOracle.NatureDimension
