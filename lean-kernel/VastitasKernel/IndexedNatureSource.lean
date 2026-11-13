import VastitasKernel.IndexedMetricSource

set_option autoImplicit false

/-! Source elaboration of the declarations of `nature::dimension` (Stage 4,
#759, ADR 0002 §3): base dimensions, quantity kinds, readings, scales and
physical metrics. `resolveBody` resolves their paths and leaves the
magnitudes and coefficients as placeholders, and the quantities of a reading
and the scales of a normalized metric in source order. This pass runs after
the frames and before the relative morphisms. It elaborates the base
dimensions, quantities, readings and scales first, and then the physical
metrics, which read them:

- a quantity keeps its dimension without the factors of exponent `0`;
- a reading and a normalized metric put their declarations in coordinate
  order, once every coordinate of the object is named exactly once;
- a scale gets its magnitude and a scale monomial its coefficient, each a
  constant expression evaluated within one run of `algebraWork`, and a scale
  monomial multiplied out is bounded (`NatureDimension.monomialBounded`)
  before any of its powers is computed;
- a physical metric is evaluated with the functions of the declaration audit,
  `NatureDimension.scaleMonomialValue` and `NatureDimension.entryValues`, each
  entry is compared with the Gram entry as soon as it is evaluated, and the
  dimensions of its terms, within the exponent bound, and its declared value
  are checked as the declaration audit checks them.

Every rejection is `E_DIMENSION` at the declaration, except the bounds of
`Limits.dimensionBases`, `Limits.dimensionExponent`,
`Limits.dimensionScaleFactors`, `Limits.metricEntryBits` and the algebraic
limits of a constant expression (`E_LIMIT`). The declaration audit checks
every stored declaration again (`NatureDimension`). A program without nature
declarations is unchanged. Messages name declarations by their full path and
write dimensions as products of base dimensions in declaration order, such as
`L^2*T^-1`, with `1` for a dimensionless one; a base dimension whose name
another base dimension of the program shares is written by its full path. A
message writes a magnitude only within `Limits.metricEntryBits`. -/
namespace VastitasKernel.Indexed.Source

def dimensionProblem {α : Type} (span : Span) (reason : String) : Namespace.Result α :=
  Namespace.problem span "E_DIMENSION" reason

private def natureSpan (sources : List (DeclId × Span × Body)) (id : DeclId) : Span :=
  ((sources.find? (·.1 == id)).map (·.2.1)).getD {}

private def natureBody (sources : List (DeclId × Span × Body)) (id : DeclId) : Option Body :=
  (sources.find? (·.1 == id)).map (·.2.2)

/-- The first element of a list that a later element repeats. -/
private def firstRepeated {α : Type} [BEq α] : List α → Option α
  | [] => none
  | x :: rest => if rest.contains x then some x else firstRepeated rest

/-- A dimension as a diagnostic writes it: the powers of its base dimensions
in their declaration order, `L^2*T^-1`, and `1` for a dimensionless one. A
base dimension has its short name, or its full path when another base
dimension of the program has the same short name. -/
private def dimensionText (env : Environment) (dimension : DimensionVector) : String :=
  let order := NatureDimension.baseDimensions env
  let rank (base : DeclId) : Nat := (order.idxOf? base).getD order.length
  let name (base : DeclId) : String :=
    if order.any fun other => other != base && other.name == base.name then qualified base else base.name
  let factors := (dimension.filter (·.2 != 0)).mergeSort fun a b => rank a.1 ≤ rank b.1
  if factors.isEmpty then "1"
  else String.intercalate "*" <| factors.map fun (base, exponent) =>
    if exponent == 1 then name base else s!"{name base}^{exponent}"

/-- `count` things: `one` for one, otherwise `many`, after the number. -/
private def countText (count : Nat) (one many : String) : String :=
  s!"{count} {if count == 1 then one else many}"

/-- A magnitude that a diagnostic writes: the number within the bound of a
Gram entry, and otherwise only its size, so that the message stays short. -/
private def magnitudeText (value : Rat) : String :=
  if SmoothDeclarations.entryBounded value then s!"the magnitude {value}"
  else s!"a magnitude with more than {Limits.metricEntryBits} bits in its numerator or denominator"

/-- A Gram entry that a diagnostic writes, within the same bound. -/
private def gramEntryText (value : Rat) : String :=
  if SmoothDeclarations.entryBounded value then toString value
  else s!"a number with more than {Limits.metricEntryBits} bits in its numerator or denominator"

/-- How a diagnostic lists the coordinates of an object. -/
private def coordinateText (coordinates : List String) : String :=
  if coordinates.isEmpty then "it has no coordinates"
  else "its coordinates are " ++ String.intercalate ", " (coordinates.map fun coordinate => s!"`{coordinate}`")

/-- The canonical form of a dimension that `what` writes: every factor names a
base dimension, within the exponent bound, and no base twice. Factors with
exponent `0` are dropped. -/
private def elaborateDimension (span : Span) (env : Environment) (what : String) (dimension : DimensionVector) :
    Namespace.Result DimensionVector := do
  for (base, exponent) in dimension do
    unless isBaseDimension env base do
      dimensionProblem span <| s!"{what} names `{qualified base}`, which is not a base dimension; a dimension " ++
        "is a product of powers of base dimensions"
    unless NatureDimension.exponentBounded exponent do
      Namespace.problem span "E_LIMIT" <| s!"{what} raises `{qualified base}` to the power {exponent}, beyond " ++
        s!"the limit of {Limits.dimensionExponent} in absolute value"
  if let some base := firstRepeated (dimension.map (·.1)) then
    dimensionProblem span <| s!"{what} names the base dimension `{qualified base}` twice; a dimension names " ++
      "each base dimension once"
  pure (dimension.filter (·.2 != 0))

/-- The value of a constant expression that `what` names, within one run of
`algebraWork`. -/
private def constantValue (span : Span) (what : String) (expression : PolyExpr) : Namespace.Result Rat :=
  match AlgebraBasis.run (expression.evaluate []) with
  | .error (.limit resource) => algebraProblem span (.limit resource)
  | .error error => dimensionProblem span s!"{what} is not a constant rational number: {error.message}"
  | .ok value => pure (SmoothRuntime.evalAt value [])

/-- The coordinates of the object of the nature declaration `what`, declared
at `family<object>`: the family has the representation `form`, and it accepts
the object, which is a smooth object. -/
private def natureObject (span : Span) (env : Environment) (what form : String) (familyHolds : Bool)
    (family object : DeclId) : Namespace.Result (List String) := do
  unless familyHolds do
    dimensionProblem span s!"{what} is declared at a `{form}` family, but `{qualified family}` is not one"
  let some coordinates := smoothCoordinates? env object
    | dimensionProblem span <| s!"{what} is of `{qualified object}`, which is not a smooth affine object; it " ++
        "needs a smooth object declared with `Affine(n)[…]`"
  unless NatureDimension.declaredAt env family object do
    dimensionProblem span <| s!"{what} is declared at `{family.name}<{object.name}>`, but the family " ++
      s!"`{qualified family}` does not accept `{qualified object}`"
  pure coordinates

/-- The declarations that `what` names per coordinate of `object`, in
coordinate order. Every coordinate is named exactly once. -/
private def byCoordinate {α : Type} (span : Span) (what : String) (object : DeclId) (coordinates : List String)
    (named : List (String × α)) : Namespace.Result (List α) := do
  for (name, _) in named do
    unless coordinates.contains name do
      dimensionProblem span <| s!"{what} names `{name}`, which is not a coordinate of `{qualified object}`; " ++
        coordinateText coordinates
  if let some name := firstRepeated (named.map (·.1)) then
    dimensionProblem span s!"{what} names the coordinate `{name}` twice; it names each coordinate exactly once"
  coordinates.mapM fun coordinate => do
    let some (_, value) := named.find? (·.1 == coordinate)
      | dimensionProblem span <| s!"{what} does not name the coordinate `{coordinate}` of `{qualified object}`; " ++
          "it names each coordinate exactly once"
    pure value

/-- A reading: the quantities in coordinate order. -/
private def elaborateReading (span : Span) (env : Environment) (id family object : DeclId)
    (named : List String) (quantities : List DeclId) : Namespace.Result Indexed.Declaration := do
  let what := s!"the reading `{qualified id}`"
  let coordinates ← natureObject span env what "reading" (isReadingFamily env family) family object
  let ordered ← byCoordinate span what object coordinates (named.zip quantities)
  for (coordinate, quantity) in coordinates.zip ordered do
    unless (quantityDimension? env quantity).isSome do
      dimensionProblem span s!"{what} reads `{coordinate}` as `{qualified quantity}`, which is not a quantity"
  pure (.reading family object ordered)

/-- A scale: a quantity and a positive magnitude within the entry bound. -/
private def elaborateScale (span : Span) (env : Environment) (id quantity : DeclId) (magnitude : PolyExpr) :
    Namespace.Result Indexed.Declaration := do
  let what := s!"the scale `{qualified id}`"
  unless (quantityDimension? env quantity).isSome do
    dimensionProblem span s!"{what} is of `{qualified quantity}`, which is not a quantity"
  let magnitude ← constantValue span s!"the magnitude of {what}" magnitude
  unless SmoothDeclarations.entryBounded magnitude do
    Namespace.problem span "E_LIMIT" <| s!"the magnitude of {what} has more than {Limits.metricEntryBits} bits " ++
      "in its numerator or denominator"
  unless decide (0 < magnitude) do
    dimensionProblem span <| s!"{what} has the magnitude {magnitude}, which is not positive; a scale is a " ++
      "positive rational magnitude"
  pure (.scale quantity magnitude)

/-- The base dimensions, quantities, readings and scales. -/
private def elaborateDeclaration (sources : List (DeclId × Span × Body)) (env : Environment) (entry : Entry) :
    Namespace.Result Entry := do
  let span := natureSpan sources entry.id
  match entry.declaration, natureBody sources entry.id with
  | .quantity dimension, _ =>
    pure ⟨entry.id, .quantity (← elaborateDimension span env s!"the quantity `{qualified entry.id}`" dimension)⟩
  | .reading family object quantities, some (.reading _ _ named) =>
    pure ⟨entry.id, ← elaborateReading span env entry.id family object (named.map (·.1)) quantities⟩
  | .scale quantity _, some (.scale _ magnitude) =>
    pure ⟨entry.id, ← elaborateScale span env entry.id quantity magnitude⟩
  | _, _ => pure entry

/-- One scale monomial of a physical metric, at row `row` and column `column`:
at most `Limits.dimensionScaleFactors` factors, each a scale within the
exponent bound, no scale twice, a constant coefficient within the entry
bound, and the monomial multiplied out within the entry bound
(`NatureDimension.monomialBounded`, before any power is computed). Factors
with exponent `0` are dropped. -/
private def elaborateMonomial (span : Span) (env : Environment) (what : String) (row column : Nat)
    (source : ScaleMonomial) (factors : List (DeclId × Int)) : Namespace.Result Indexed.ScaleMonomial := do
  let entry := s!"the entry in row {row + 1}, column {column + 1} of {what}"
  if factors.length > Limits.dimensionScaleFactors then
    Namespace.problem span "E_LIMIT" <| s!"{entry} has {factors.length} scale factors, more than the limit of " ++
      s!"{Limits.dimensionScaleFactors}"
  for (scale, exponent) in factors do
    unless (scaleData? env scale).isSome do
      dimensionProblem span s!"{entry} names `{qualified scale}`, which is not a scale"
    unless NatureDimension.exponentBounded exponent do
      Namespace.problem span "E_LIMIT" <| s!"{entry} raises `{qualified scale}` to the power {exponent}, beyond " ++
        s!"the limit of {Limits.dimensionExponent} in absolute value"
  if let some scale := firstRepeated (factors.map (·.1)) then
    dimensionProblem span s!"{entry} names the scale `{qualified scale}` twice; write one power of each scale"
  let coefficient ← constantValue span s!"the coefficient of {entry}" source.coefficient
  unless SmoothDeclarations.entryBounded coefficient do
    Namespace.problem span "E_LIMIT" <| s!"the coefficient of {entry} has more than {Limits.metricEntryBits} " ++
      "bits in its numerator or denominator"
  let powers := factors.filterMap fun (scale, exponent) =>
    (scaleData? env scale).map fun (_, magnitude) => (magnitude, exponent)
  unless NatureDimension.monomialBounded coefficient powers do
    let (numerator, denominator) := NatureDimension.monomialBits coefficient powers
    Namespace.problem span "E_LIMIT" <| s!"{entry}, multiplied out, has up to {numerator} bits in its " ++
      s!"numerator and {denominator} in its denominator, beyond the limit of {Limits.metricEntryBits} bits of a " ++
      "Gram entry; the kernel adds the bits of the coefficient and of each magnitude, once per unit of its exponent"
  pure { coefficient, factors := factors.filter (·.2 != 0) }

/-- The entries of a physical metric on an object with `coordinates` read as
`quantities`: rows of elaborated monomials, or the scales of `normalized` in
coordinate order, each of its coordinate's own quantity. -/
private def elaborateEntries (span : Span) (env : Environment) (what : String) (object : DeclId)
    (coordinates : List String) (quantities : List DeclId) (source : PhysicalGram) (entries : Indexed.PhysicalGram) :
    Namespace.Result Indexed.PhysicalGram := do
  let n := coordinates.length
  match source, entries with
  | .gram sourceRows, .gram rows =>
    unless rows.length == n do
      dimensionProblem span <| s!"{what} on the {n}-dimensional object `{qualified object}` needs " ++
        s!"{countText n "row" "rows"} of {countText n "entry" "entries"}, but it has " ++
        countText rows.length "row" "rows"
    for (row, index) in rows.zipIdx do
      unless row.length == n do
        dimensionProblem span <| s!"{what} on the {n}-dimensional object `{qualified object}` needs " ++
          s!"{countText n "entry" "entries"} in each row, but row {index + 1} has {row.length}"
    let rows ← (sourceRows.zip rows).zipIdx.mapM fun ((sourceRow, row), i) =>
      (sourceRow.zip row).zipIdx.mapM fun ((sourceMonomial, monomial), j) =>
        elaborateMonomial span env what i j sourceMonomial monomial.factors
    pure (.gram rows)
  | .normalized named, .normalized scales =>
    let ordered ← byCoordinate span what object coordinates ((named.map (·.1)).zip scales)
    for ((coordinate, scale), quantity) in (coordinates.zip ordered).zip quantities do
      let some (kind, _) := scaleData? env scale
        | dimensionProblem span s!"{what} normalizes `{coordinate}` by `{qualified scale}`, which is not a scale"
      unless kind == quantity do
        dimensionProblem span <| s!"{what} normalizes `{coordinate}`, which its reading reads as " ++
          s!"`{qualified quantity}`, by the scale `{qualified scale}` of `{qualified kind}`; `normalized` needs " ++
          "a scale of the coordinate's own quantity, and an equal dimension is not enough"
    pure (.normalized ordered)
  | _, entries => pure entries

/-- The value and the dimension of every entry of a physical metric `what`
on an object with `coordinates` read as `quantities`, row by row, each
compared with the Gram entry of `metric` as soon as it is evaluated: the
first entry that differs is the error. An entry of `gram(…)` is evaluated by
`NatureDimension.scaleMonomialValue`, as the declaration audit evaluates it;
`euclidean` and `normalized` give diagonals of `NatureDimension.entryValues`. -/
private def evaluateEntries (span : Span) (env : Environment) (what : String) (metric : DeclId)
    (gram : SmoothRuntime.Matrix) (coordinates : List String) (quantities : List DeclId)
    (entries : Indexed.PhysicalGram) : Namespace.Result (List (List (Rat × DimensionVector))) := do
  let compare (i j : Nat) (entry : Rat × DimensionVector) : Namespace.Result (Rat × DimensionVector) := do
    let expected := SmoothDeclarations.entry gram i j
    unless entry.1 == expected do
      dimensionProblem span <| s!"{what} gives the {coordinates.getD i ""}·{coordinates.getD j ""} entry, " ++
        s!"in row {i + 1}, column {j + 1}, {magnitudeText entry.1}, but the metric `{qualified metric}` " ++
        s!"has {gramEntryText expected} there; the entries, evaluated with the magnitudes of their scales, equal " ++
        "its Gram matrix"
    pure entry
  match entries with
  | .gram rows =>
    rows.zipIdx.mapM fun (row, i) => row.zipIdx.mapM fun (monomial, j) => do
      let some entry := NatureDimension.scaleMonomialValue env monomial
        | dimensionProblem span s!"the entries of {what} are not well formed"
      compare i j entry
  | entries =>
    let some values := NatureDimension.entryValues env coordinates.length quantities entries
      | dimensionProblem span s!"the entries of {what} are not well formed"
    values.zipIdx.mapM fun (row, i) => row.zipIdx.mapM fun (entry, j) => compare i j entry

/-- A physical metric: its object, metric, reading, value and entries, the
entries evaluated against the Gram matrix of the metric, and one dimension of
the nonzero terms, within the exponent bound and equal to a declared value. -/
private def elaboratePhysical (span : Span) (env : Environment) (id family object metric reading : DeclId)
    (value : Option DimensionVector) (source : PhysicalGram) (entries : Indexed.PhysicalGram) :
    Namespace.Result Indexed.Declaration := do
  let what := s!"the physical metric `{qualified id}`"
  let coordinates ← natureObject span env what "physical_metric" (isPhysicalMetricFamily env family) family object
  let some (metricObject, _, gram) := metricData? env metric
    | dimensionProblem span s!"{what} interprets `{qualified metric}`, which is not a metric"
  unless metricObject == object do
    dimensionProblem span <| s!"{what} is on `{qualified object}`, but it interprets the metric " ++
      s!"`{qualified metric}` of `{qualified metricObject}`"
  let some (_, readingObject, quantities) := readingData? env reading
    | dimensionProblem span s!"{what} names `{qualified reading}` as its reading, which is not a reading"
  unless readingObject == object do
    dimensionProblem span <| s!"{what} is on `{qualified object}`, but its reading `{qualified reading}` is of " ++
      s!"`{qualified readingObject}`"
  let value ← value.mapM (elaborateDimension span env s!"the value of {what}")
  let entries ← elaborateEntries span env what object coordinates quantities source entries
  -- The reading was elaborated before, so each quantity has a dimension.
  let some dimensions := quantities.mapM (quantityDimension? env)
    | dimensionProblem span s!"{what} names the reading `{qualified reading}`, which is not valid"
  let values ← evaluateEntries span env what metric gram coordinates quantities entries
  let term (i j : Nat) : String := s!"{coordinates.getD i ""}·{coordinates.getD j ""}"
  match NatureDimension.nonzeroTerms dimensions values with
  | [] =>
    if value.isSome then
      dimensionProblem span <| s!"{what} has no nonzero term, so it has no value; a declared value names the " ++
        "dimension of its nonzero terms"
  | (i, j, first) :: rest =>
    if let some (k, l, other) := rest.find? fun (_, _, other) => !NatureDimension.sameDimension first other then
      dimensionProblem span <| s!"in {what}, the term {term i j} has dimension {dimensionText env first} and the " ++
        s!"term {term k l} has dimension {dimensionText env other}; every nonzero term of an interpreted metric " ++
        "has one dimension"
    if let some (base, exponent) := first.find? fun (_, exponent) => !NatureDimension.exponentBounded exponent then
      Namespace.problem span "E_LIMIT" <| s!"the nonzero terms of {what} have dimension " ++
        s!"{dimensionText env first}, which raises `{qualified base}` to the power {exponent}, beyond the limit of " ++
        s!"{Limits.dimensionExponent} in absolute value; the value of an interpreted metric is a dimension that a " ++
        "declaration can write"
    if let some declared := value then
      unless NatureDimension.sameDimension declared first do
        dimensionProblem span <| s!"{what} declares the value {dimensionText env declared}, but its nonzero " ++
          s!"terms have dimension {dimensionText env first}"
  pure (.physicalMetric family object metric reading value entries)

/-- Elaborate every nature declaration: the base dimensions, quantities,
readings and scales first, then the physical metrics, which read them. -/
def elaborateNature (sources : List (DeclId × Span × Body)) (env : Core.Declarations) :
    Namespace.Result Core.Declarations := do
  if let some extra := (NatureDimension.baseDimensions env.indexed)[Limits.dimensionBases]? then
    Namespace.problem (natureSpan sources extra) "E_LIMIT" <| s!"the base dimension `{qualified extra}` is " ++
      s!"base dimension {Limits.dimensionBases + 1} of the program, beyond the limit of {Limits.dimensionBases}"
  let declared ← env.indexed.mapM (elaborateDeclaration sources env.indexed)
  let indexed ← declared.mapM fun entry => do
    match entry.declaration, natureBody sources entry.id with
    | .physicalMetric family object metric reading value entries, some (.physicalMetric _ _ _ _ _ source) =>
      pure ⟨entry.id, ← elaboratePhysical (natureSpan sources entry.id) declared entry.id family object metric
        reading value source entries⟩
    | _, _ => pure entry
  pure { env with indexed }

end VastitasKernel.Indexed.Source
