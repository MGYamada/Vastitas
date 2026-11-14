import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the declarations of the minimal `nature::dimension` profile
(Stage 4, #759, ADR 0002 §3): base dimensions, quantity kinds, physical
readings of a chart, scales, and physical interpretations of a metric.
"Dimension" here is a physical dimension, an element of the free abelian group
on the base dimensions, not the dimension of a vector space. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration, and the source pass
`elaborateNature` (`IndexedNatureSource`) states the same rules with their
diagnostics.

- A *dimension* (`DimensionVector`) is stored in canonical form: every factor
  names a base dimension, no base twice, every exponent is nonzero and within
  `Limits.dimensionExponent` in absolute value. Two dimensions are compared by
  the exponent of each base, whatever the order of their factors
  (`sameDimension`).
- A *quantity kind* is nominal: two quantities with one dimension are two
  kinds. Only `normalized` compares kinds, and it compares declarations.
- A *reading* names one quantity per coordinate of a smooth object, in
  coordinate order. A *scale* is a positive rational magnitude of a quantity,
  within `Limits.metricEntryBits`.
- A *physical metric* interprets a metric of its object under a reading of
  that object. Its entries, evaluated with the magnitudes of their scales,
  equal the Gram matrix of the metric exactly. The term `g_ij dxⁱ dxʲ` has the
  dimension of the entry plus the dimensions of the quantities of `xⁱ` and
  `xʲ`; every term with a nonzero entry has one dimension, the value, within
  the exponent bound, and a declared value equals it. Every exponent is
  bounded before any power is computed, and so is the size of every scale
  monomial multiplied out (`monomialBounded`).

The checks only accept or reject nature declarations. No other declaration's
check and no binding reads a nature declaration. -/
namespace VastitasKernel.NatureDimension

open VastitasKernel.Indexed

/-! ## Dimensions -/

/-- The base dimensions of the environment, in declaration order. -/
def baseDimensions (env : Environment) : List DeclId :=
  env.filterMap fun entry => match entry.declaration with
    | .baseDimension => some entry.id
    | _ => none

/-- An exponent within `Limits.dimensionExponent` in absolute value. -/
def exponentBounded (exponent : Int) : Bool := exponent.natAbs ≤ Limits.dimensionExponent

/-- The exponent of `base` in a dimension; `0` when no factor names it. -/
def exponentOf (dimension : DimensionVector) (base : DeclId) : Int :=
  ((dimension.find? (·.1 == base)).map (·.2)).getD 0

/-- Two dimensions are equal: every base has one exponent in both. The order
of the factors does not matter, and a base that one of them does not name has
the exponent `0`. -/
def sameDimension (first second : DimensionVector) : Bool :=
  (first ++ second).all fun (base, _) => exponentOf first base == exponentOf second base

/-- `dimension + k · other`. A base whose exponent becomes `0` is dropped, so
the result of canonical dimensions is canonical except for the bound. -/
def addScaled (dimension : DimensionVector) (k : Int) (other : DimensionVector) : DimensionVector :=
  other.foldl (fun sum (base, exponent) =>
    let total := exponentOf sum base + k * exponent
    sum.filter (·.1 != base) ++ (if total == 0 then [] else [(base, total)])) dimension

/-- A dimension in canonical form: every factor names a base dimension of
`env`, with a nonzero exponent within the bound, and no base twice. -/
def canonicalDimension (env : Environment) (dimension : DimensionVector) : Bool :=
  dimension.all (fun (base, exponent) => isBaseDimension env base && exponent != 0 && exponentBounded exponent) &&
    decide (dimension.map (·.1)).Nodup

/-! ## Declarations -/

/-- A base dimension: the program declares at most `Limits.dimensionBases` of
them. -/
def checkBaseDimension (env : Environment) : Bool :=
  (baseDimensions env).length ≤ Limits.dimensionBases

/-- The quantity declaration `quantity dimension`: a canonical dimension. -/
def checkQuantity (env : Environment) (dimension : DimensionVector) : Bool :=
  canonicalDimension env dimension

/-- The declaration is at `family<object>`: the family accepts the object, so
the object is a smooth object of the family's domain. -/
def declaredAt (env : Environment) (family object : DeclId) : Bool :=
  validApplication env ⟨family, [.object (.global object)]⟩

/-- The reading declaration `reading family object quantities`: a `reading`
family applied to a smooth object, and one quantity per coordinate. -/
def checkReading (env : Environment) (family object : DeclId) (quantities : List DeclId) : Bool :=
  isReadingFamily env family && declaredAt env family object &&
    smoothDimension? env object == some quantities.length &&
    quantities.all fun quantity => (quantityDimension? env quantity).isSome

/-- A magnitude of a scale: positive and within the metric entry bound. -/
def magnitudeValid (magnitude : Rat) : Bool :=
  decide (0 < magnitude) && SmoothDeclarations.entryBounded magnitude

/-- The scale declaration `scale quantity magnitude`: a quantity and a valid
magnitude. -/
def checkScale (env : Environment) (quantity : DeclId) (magnitude : Rat) : Bool :=
  (quantityDimension? env quantity).isSome && magnitudeValid magnitude

/-! ## Physical metrics -/

/-- The magnitude and the dimension of a scale: the magnitude and the
dimension of its quantity. -/
def scaleValue (env : Environment) (scale : DeclId) : Option (Rat × DimensionVector) := do
  let (quantity, magnitude) ← scaleData? env scale
  guard (magnitudeValid magnitude = true)
  pure (magnitude, ← quantityDimension? env quantity)

/-- The bits that a factor `x` adds to a product: `0` for `0` and `1`, and
otherwise the number of binary digits of `x`, so that `x < 2 ^ natBits x` for
`x ≥ 2`. A product of factors whose bits add up to at most `b ≥ 1` is below
`2 ^ b`. -/
def natBits (x : Nat) : Nat := if x ≤ 1 then 0 else x.log2 + 1

/-- The bits of the numerator and of the denominator of the scale monomial
`c · Π mᵢ^{eᵢ}` multiplied out without cancelling, for the magnitudes and
exponents `(mᵢ, eᵢ)` of `powers`: the bits of the numerator and of the
denominator of `c`, plus `|eᵢ|` times those of the numerator and of the
denominator of `mᵢ`, which change places for `eᵢ < 0`. The numerator and the
denominator of the value, and of every product that `scaleMonomialValue`
computes, divide the two products, so they have at most these bits. -/
def monomialBits (coefficient : Rat) (powers : List (Rat × Int)) : Nat × Nat :=
  powers.foldl (fun (numerator, denominator) (magnitude, exponent) =>
    let up := exponent.natAbs * natBits magnitude.num.natAbs
    let down := exponent.natAbs * natBits magnitude.den
    if exponent < 0 then (numerator + down, denominator + up) else (numerator + up, denominator + down))
    (natBits coefficient.num.natAbs, natBits coefficient.den)

/-- A scale monomial multiplied out has the bound of a Gram entry: at most
`Limits.metricEntryBits` bits in its numerator and in its denominator
(`monomialBits`). The kernel checks it before it computes any power, so the
evaluation of an entry never builds a larger number. A monomial whose factors
cancel is measured before they cancel. -/
def monomialBounded (coefficient : Rat) (powers : List (Rat × Int)) : Bool :=
  let (numerator, denominator) := monomialBits coefficient powers
  numerator ≤ Limits.metricEntryBits && denominator ≤ Limits.metricEntryBits

/-- One factor of a scale monomial, with the magnitude and the dimension of
its scale: multiply the value by the magnitude raised to the exponent, and
add the exponent times the dimension. -/
def scaleStep (product : Rat × DimensionVector) (factor : (DeclId × Int) × (Rat × DimensionVector)) :
    Rat × DimensionVector :=
  (product.1 * factor.2.1 ^ factor.1.2, addScaled product.2 factor.1.2 factor.2.2)

/-- The value and the dimension of the scale monomial `c · Π sᵢ^{eᵢ}`: the
product with the magnitudes of the scales, and `Σ eᵢ · dim(sᵢ)`. It is `none`
for a monomial with more than `Limits.dimensionScaleFactors` factors, a
coefficient beyond the metric entry bound, a scale named twice, an exponent
that is `0` or beyond its bound, a factor that is not a valid scale, or a
product beyond `monomialBounded`. Every exponent and the size of the product
are bounded before any power is computed. -/
def scaleMonomialValue (env : Environment) (monomial : ScaleMonomial) : Option (Rat × DimensionVector) := do
  guard (monomial.factors.length ≤ Limits.dimensionScaleFactors)
  guard (SmoothDeclarations.entryBounded monomial.coefficient = true)
  guard (monomial.factors.map (·.1)).Nodup
  guard (monomial.factors.all (fun (_, exponent) => exponent != 0 && exponentBounded exponent) = true)
  let scales ← monomial.factors.mapM fun factor => scaleValue env factor.1
  guard (monomialBounded monomial.coefficient
    ((monomial.factors.zip scales).map fun factor => (factor.2.1, factor.1.2)) = true)
  pure ((monomial.factors.zip scales).foldl scaleStep (monomial.coefficient, []))

/-- The `n × n` matrix whose diagonal is `diagonal` and whose other entries are
`0` of dimension `1`. -/
def diagonalEntries (n : Nat) (diagonal : List (Rat × DimensionVector)) : List (List (Rat × DimensionVector)) :=
  (List.range n).map fun i => (List.range n).map fun j =>
    if i == j then diagonal.getD i (0, []) else (0, [])

/-- The value and the dimension of every entry of a physical Gram matrix on
an `n`-dimensional object whose coordinates are read as `quantities`, row by
row, or `none` when the entries are not well formed:

- `euclidean`: the identity, dimensionless;
- `gram rows`: `n` rows of `n` scale monomials (`scaleMonomialValue`);
- `normalized scales`: one scale per coordinate, in coordinate order, of the
  coordinate's own quantity, and the diagonal `1 / sᵢ²` of dimension
  `-2 · dim(sᵢ)`. -/
def entryValues (env : Environment) (n : Nat) (quantities : List DeclId) :
    PhysicalGram → Option (List (List (Rat × DimensionVector)))
  | .euclidean => some (diagonalEntries n ((List.range n).map fun _ => (1, [])))
  | .gram rows => do
    guard (rows.length == n && rows.all (·.length == n))
    rows.mapM (·.mapM (scaleMonomialValue env))
  | .normalized scales => do
    guard (scales.length == n && quantities.length == n)
    let diagonal ← (scales.zip quantities).mapM fun (scale, quantity) => do
      let (kind, _) ← scaleData? env scale
      guard (kind == quantity)
      let (magnitude, dimension) ← scaleValue env scale
      pure (1 / (magnitude * magnitude), addScaled [] (-2) dimension)
    pure (diagonalEntries n diagonal)

/-- The row, the column and the dimension of every term with a nonzero entry,
in row-major order. The term `g_ij dxⁱ dxʲ` has the dimension of `g_ij` plus
the dimensions `dᵢ` and `dⱼ` of the quantities of `xⁱ` and `xʲ`. -/
def nonzeroTerms (coordinates : List DimensionVector) (entries : List (List (Rat × DimensionVector))) :
    List (Nat × Nat × DimensionVector) :=
  entries.zipIdx.flatMap fun (row, i) => row.zipIdx.filterMap fun ((value, dimension), j) =>
    if value == 0 then none
    else some (i, j, addScaled (addScaled dimension 1 (coordinates.getD i [])) 1 (coordinates.getD j []))

/-- Every exponent of a dimension is within `Limits.dimensionExponent` in
absolute value. -/
def dimensionBounded (dimension : DimensionVector) : Bool :=
  dimension.all fun (_, exponent) => exponentBounded exponent

/-- Every nonzero term has one dimension, within the exponent bound, so that a
value can declare it, and a declared value equals it. A zero entry constrains
nothing. Without a nonzero term the metric has no value, and a declared value
is rejected. -/
def consistentValue (terms : List (Nat × Nat × DimensionVector)) (value : Option DimensionVector) : Bool :=
  match terms with
  | [] => value.isNone
  | (_, _, first) :: rest =>
    dimensionBounded first && rest.all (fun term => sameDimension first term.2.2) && value.all (sameDimension first)

/-- The evaluated entries equal the Gram matrix entry by entry. -/
def entriesEqual (gram : SmoothRuntime.Matrix) (entries : List (List (Rat × DimensionVector))) : Bool :=
  entries.zipIdx.all fun (row, i) => row.zipIdx.all fun ((value, _), j) =>
    value == SmoothDeclarations.entry gram i j

/-- The physical metric declaration `physicalMetric family object metric
reading value entries`: a `physical_metric` family applied to a smooth object;
a metric and a reading of that object; a canonical declared value; entries
that evaluate to the Gram matrix of the metric; and one dimension of the
nonzero terms, equal to the declared value. -/
def checkPhysicalMetric (env : Environment) (family object metric reading : DeclId)
    (value : Option DimensionVector) (entries : PhysicalGram) : Bool :=
  isPhysicalMetricFamily env family && declaredAt env family object && value.all (canonicalDimension env) &&
  match metricData? env metric, readingData? env reading with
  | some (metricObject, n, gram), some (_, readingObject, quantities) =>
    metricObject == object && readingObject == object && quantities.length == n &&
      SmoothDeclarations.square n gram &&
    match quantities.mapM (quantityDimension? env), entryValues env n quantities entries with
    | some dimensions, some values =>
      entriesEqual gram values && consistentValue (nonzeroTerms dimensions values) value
    | _, _ => false
  | _, _ => false

end VastitasKernel.NatureDimension
