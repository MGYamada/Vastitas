import Lean.Data.Json

set_option autoImplicit false

/-! Source spellings for the handwritten geometry and physics wire regressions.
These declarations accompany the raw requests submitted to the public checker. -/
namespace VastitasKernel.RegressionIndexedText
open Lean

private def field (j : Json) (key : String) := (j.getObjVal? key).toOption
private def str (j : Json) (key : String) := (j.getObjValAs? String key).toOption
private def path (j : Json) := (j.getObjValAs? (List String) "path").toOption.map (String.intercalate "::")
private def ref (j : Json) (key : String) := (field j key).bind path
private def fields (j : Json) (key : String) := (j.getObjValAs? (List Json) key).toOption
private def names (j : Json) (key : String) := (j.getObjValAs? (List String) key).toOption
private def comma := String.intercalate ", "
private def paths (j : Json) (key : String) := do return comma (← (← fields j key).mapM path)

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
private def matrix (j : Json) (key : String) (element : Json → Option String) : Option String := do
  let rows ← (← fields j key).mapM fun row => do
    let entries ← (fromJson? (α := List Json) row).toOption
    return "(" ++ comma (← entries.mapM element) ++ ")"
  return "(" ++ comma rows ++ ")"

private def power (key : String) (f : Json) : Option String := do
  return (← ref f key) ++ "^" ++ (← str f "exponent")

private def dimension (j : Json) : Option String := do
  let factors ← (fromJson? (α := List Json) j).toOption
  let terms ← factors.mapM (power "base")
  return if terms.isEmpty then "1" else String.intercalate " * " terms

private def components (j : Json) (list key : String) : Option String := do
  let items ← (← fields j list).mapM fun item => do return (← str item "coordinate") ++ ": " ++ (← ref item key)
  return "(" ++ comma items ++ ")"

private def annotation (d : Json) : Option String := do
  return ": " ++ (← ref d "family") ++ "<" ++ (← paths d "indices") ++ "> = "

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

private def monomial (j : Json) : Option String := do
  let coeff ← field j "coefficient"
  let atom := fun (x : Json) => do
    match ← str x "op" with
    | "natural" | "fraction" => polynomial x
    | _ => none
  let value ← if (str coeff "op") == some "neg" then do return "-" ++ (← atom (← field coeff "operand"))
    else atom coeff
  return String.intercalate " * " (value :: (← (← fields j "factors").mapM (power "scale")))

private def physicalEntries (j : Json) : Option String := do
  match ← str j "kind" with
  | "euclidean" => return "euclidean"
  | "normalized" => return "normalized" ++ (← components j "scales" "scale")
  | "gram" => return "gram" ++ (← matrix j "rows" monomial)
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

/-- Print a declaration's source keyword and its suffix after the declared name.
Unsupported negative wire records have no invented source representation. -/
def syntaxOf (d : Json) : Option (String × String) := do
  let kind ← str d "kind"
  match kind with
  | "marker" | "base_dimension" => return (kind, "")
  | "convention" => return (kind, " = " ++ (← str d "value"))
  | "calibration" =>
    let values ← (← fields d "parameters").mapM fun j => do
      return (← str j "coordinate") ++ " = measured(" ++ (← polynomial (← field j "value")) ++
        ", u = " ++ (← polynomial (← field j "uncertainty")) ++ ")"
    let parts := values ++ ["method = " ++ (← str d "method"),
      "reference = " ++ (toJson (← str d "reference")).compress, "revision = " ++ (toJson (← str d "revision")).compress]
    return (kind, (← annotation d) ++ "calibrate(" ++ comma parts ++ ")")
  | "quantity" => return (kind, " = " ++ (← dimension (← field d "dimension")))
  | "scale" => return (kind, " = " ++ (← polynomial (← field d "magnitude")) ++ " of " ++ (← ref d "quantity"))
  | "reading" => return (kind, (← annotation d) ++ (← components d "quantities" "quantity"))
  | "metric" => return (kind, (← annotation d) ++ (← metricGram (← field d "gram")))
  | "physical_metric" =>
    let v ← field d "value"
    let value ← if v == .null then pure "" else do pure (", value = " ++ (← dimension v))
    return ("physical", (← annotation d) ++ "interpret(" ++ (← ref d "metric") ++ ", reading = " ++
      (← ref d "reading") ++ ", " ++ (← physicalEntries (← field d "entries")) ++ value ++ ")")
  | "frame" =>
    let inv ← field d "inverse"
    let tail ← if inv == .null then pure "" else do pure (" inverse = " ++ (← columns inv))
    return (kind, (← annotation d) ++ (← columns (← field d "columns")) ++ tail)
  | "free_module" => return (kind, (← annotation d) ++ "basis(" ++ comma (← names d "basis") ++ ")")
  | "endomorphism" =>
    let symmetric ← (d.getObjValAs? Bool "symmetric").toOption
    return (kind, (← annotation d) ++ "rows" ++ (← matrix d "rows" polynomial) ++ " of " ++
      (← ref d "module") ++ (if symmetric then " symmetric" else ""))
  | "spectrum" => return (kind, (← annotation d) ++ "eigen(" ++ (← ref d "endomorphism") ++ ", " ++ (← str d "fiber") ++ ")")
  | "branch" => return (kind, (← annotation d) ++ "simple(" ++ (← ref d "spectrum") ++ ", localize = " ++
      (← polynomial (← field d "localize")) ++ ", witness = " ++ (← polynomial (← field d "witness")) ++
      ", exponent = " ++ (← str d "exponent") ++ ")")
  | _ => none

end VastitasKernel.RegressionIndexedText
