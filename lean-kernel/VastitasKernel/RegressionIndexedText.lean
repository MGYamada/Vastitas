import Lean.Data.Json

set_option autoImplicit false

/-! Source spellings for the handwritten geometry and physics wire regressions.
These declarations accompany the raw requests submitted to the public checker. -/
namespace VastitasKernel.RegressionIndexedText
open Lean

private def field (j : Json) (key : String) := (j.getObjVal? key).toOption
private def str (j : Json) (key : String) := (j.getObjValAs? String key).toOption
private def path (j : Json) := (j.getObjValAs? (List String) "path").toOption.map (String.intercalate "::")
private def fields (j : Json) (key : String) := (j.getObjValAs? (List Json) key).toOption
private def names (j : Json) (key : String) := (j.getObjValAs? (List String) key).toOption
private def comma := String.intercalate ", "

private def poly : Nat → Json → Option String
  | 0, _ => none
  | fuel+1, j => do
    match ← str j "op" with
    | "natural" => str j "value"
    | "coordinate" => str j "name"
    | "fraction" => return "frac(" ++ (← str j "numerator") ++ ", " ++ (← str j "denominator") ++ ")"
    | "neg" => return "-(" ++ (← poly fuel (← field j "operand")) ++ ")"
    | "pow" => return "(" ++ (← poly fuel (← field j "base")) ++ ")^" ++ (← str j "exponent")
    | "sum" => return "(" ++ String.intercalate " + " (← (← fields j "terms").mapM (poly fuel)) ++ ")"
    | "product" => return "(" ++ String.intercalate " * " (← (← fields j "factors").mapM (poly fuel)) ++ ")"
    | _ => none

private def polynomial := poly 256
private def literal (j : Json) : Option String := do
  let negative := str j "op" == some "neg"
  let value ← if negative then field j "operand" else some j
  guard (["natural", "fraction"].contains (← str value "op"))
  return (if negative then "-" else "") ++ (← polynomial value)

private def matrix (j : Json) (key : String) (element : Json → Option String) : Option String := do
  let rows ← (← fields j key).mapM fun row => do
    let entries ← (fromJson? (α := List Json) row).toOption
    return "(" ++ comma (← entries.mapM element) ++ ")"
  return "(" ++ comma rows ++ ")"

private def columns (j : Json) : Option String := do
  match ← str j "kind" with
  | "coordinates" => return "coordinates"
  | "columns" => return "columns" ++ (← matrix j "columns" polynomial)
  | _ => none

private def metricGram (g : Json) : Option String := do
  match ← str g "kind" with
  | "euclidean" => return "euclidean"
  | "gram" => return "gram" ++ (← matrix g "rows" polynomial)
  | _ => none

def familyConstraint (j : Json) : Option String := do
  let kind ← str j "kind"
  let keys ← match kind with
    | "canonical" => some ["object"]
    | "same_object" | "same_base" => some ["left", "right"]
    | "structural" => some ["object", "base"]
    | "over" => some ["object", "marker"]
    | _ => none
  let slots ← keys.mapM fun key => (j.getObjValAs? Nat key).toOption
  return kind ++ "(" ++ comma (slots.map toString) ++ ")"

/-- The fixture owns one source line. Compute each reference span when writing
the path, including repeated occurrences of the same spelling. -/
private structure Line where
  text : String
  offset : Nat
  number : Nat

private abbrev Writer := StateT Line Option

private def emit (s : String) : Writer Unit := modify fun l => { l with text := l.text ++ s }

private def pathValue (j : Json) : Writer Json := do
  let spelling ← liftM (path j)
  let l ← get
  let start := l.offset + l.text.utf8ByteSize
  let span := Json.mkObj [("start", toJson start), ("end", toJson (start + spelling.utf8ByteSize)),
    ("line", toJson l.number), ("column", toJson (l.text.length + 1))]
  emit spelling
  return j.setObjVal! "span" span

private def writeField (j : Json) (key : String) (write : Json → Writer Json) : Writer Json := do
  let v ← liftM (field j key)
  return j.setObjVal! key (← write v)

private def each (separator : String) (write : Json → Writer Json) (items : Json) : Writer Json := do
  let items ← liftM items.getArr?.toOption
  let mut result := #[]
  for j in items do
    unless result.isEmpty do emit separator
    result := result.push (← write j)
  return .arr result

private def annotation (d : Json) : Writer Json := do
  emit ": "
  let d ← writeField d "family" pathValue
  emit "<"
  let d ← writeField d "indices" (each ", " pathValue)
  emit "> = "
  return d

private def power (key : String) (entry : Json) : Writer Json := do
  let entry ← writeField entry key pathValue
  emit ("^" ++ (← liftM (str entry "exponent")))
  return entry

private def dimension (v : Json) : Writer Json := do
  if v == .arr #[] then emit "1"
  each " * " (power "base") v

private def components (d : Json) (list key : String) : Writer Json := do
  emit "("
  let d ← writeField d list (each ", " fun entry => do
    emit ((← liftM (str entry "coordinate")) ++ ": ")
    writeField entry key pathValue)
  emit ")"
  return d

private def monomial (j : Json) : Writer Json := do
  let coeff ← liftM (field j "coefficient")
  let negative := str coeff "op" == some "neg"
  if negative then emit "-"
  let value ← if negative then liftM (field coeff "operand") else pure coeff
  let atoms ← if str value "op" == some "product" then liftM (fields value "factors") else pure [value]
  for (atom, i) in atoms.zipIdx do
    if i > 0 then emit " * "
    guard (["natural", "fraction"].contains (← liftM (str atom "op")))
    emit (← liftM (polynomial atom))
  if !(← liftM (fields j "factors")).isEmpty then emit " * "
  writeField j "factors" (each " * " (power "scale"))

private def physicalEntries (j : Json) : Writer Json := do
  match ← liftM (str j "kind") with
  | "euclidean" => emit "euclidean"; return j
  | "normalized" => emit "normalized"; components j "scales" "scale"
  | "gram" =>
    emit "gram("
    let j ← writeField j "rows" (each ", " fun row => do
      emit "("
      let r ← each ", " monomial row
      emit ")"
      return r)
    emit ")"
    return j
  | _ => failure

private def body (d : Json) (kind : String) : Writer Json := do
  match kind with
  | "marker" | "base_dimension" => return d
  | "convention" => emit (" = " ++ (← liftM (str d "value"))); return d
  | "calibration" =>
    let d ← annotation d
    let params ← liftM (fields d "parameters")
    let values ← liftM <| params.mapM fun j => do
      return (← str j "coordinate") ++ " = measured(" ++ (← literal (← field j "value")) ++
        ", u = " ++ (← literal (← field j "uncertainty")) ++ ")"
    let parts := values ++ ["method = " ++ (← liftM (str d "method")),
      "reference = " ++ (toJson (← liftM (str d "reference"))).compress,
      "revision = " ++ (toJson (← liftM (str d "revision"))).compress]
    emit ("calibrate(" ++ comma parts ++ ")")
    return d
  | "quantity" => emit " = "; writeField d "dimension" dimension
  | "scale" =>
    emit (" = " ++ (← liftM ((field d "magnitude").bind polynomial)) ++ " of ")
    writeField d "quantity" pathValue
  | "reading" => components (← annotation d) "quantities" "quantity"
  | "metric" =>
    let d ← annotation d
    emit (← liftM ((field d "gram").bind metricGram))
    return d
  | "physical_metric" =>
    let d ← annotation d
    emit "interpret("
    let d ← writeField d "metric" pathValue
    emit ", reading = "
    let d ← writeField d "reading" pathValue
    emit ", "
    let d ← writeField d "entries" physicalEntries
    let d ← if (← liftM (field d "value")) == .null then pure d else do
      emit ", value = "
      writeField d "value" dimension
    emit ")"
    return d
  | "frame" =>
    let d ← annotation d
    emit (← liftM ((field d "columns").bind columns))
    let inv ← liftM (field d "inverse")
    unless inv == .null do emit (" inverse = " ++ (← liftM (columns inv)))
    return d
  | "free_module" =>
    let d ← annotation d
    emit ("basis(" ++ comma (← liftM (names d "basis")) ++ ")")
    return d
  | "endomorphism" =>
    let d ← annotation d
    emit ("rows" ++ (← liftM (matrix d "rows" polynomial)) ++ " of ")
    let d ← writeField d "module" pathValue
    if ← liftM (d.getObjValAs? Bool "symmetric").toOption then emit " symmetric"
    return d
  | "spectrum" =>
    let d ← annotation d
    emit "eigen("
    let d ← writeField d "endomorphism" pathValue
    emit (", " ++ (← liftM (str d "fiber")) ++ ")")
    return d
  | "branch" =>
    let d ← annotation d
    emit "simple("
    let d ← writeField d "spectrum" pathValue
    emit (", localize = " ++ (← liftM ((field d "localize").bind polynomial)) ++
      ", witness = " ++ (← liftM ((field d "witness").bind polynomial)) ++
      ", exponent = " ++ (← liftM (str d "exponent")) ++ ")")
    return d
  | _ => failure

/-- Write the complete declaration and stamp every nested path while rendering.
Malformed raw negative controls can still exercise the independent wire decoder. -/
def syntaxOf (d : Json) (vis kind name : String) (offset line : Nat) : Option (String × Json) := do
  let keyword := if kind == "physical_metric" then "physical" else kind
  let head := vis ++ "indexed " ++ keyword ++ " " ++ name
  let (record, final) ← (body d kind).run ⟨head, offset, line⟩
  return (final.text ++ ";", record)

end VastitasKernel.RegressionIndexedText
