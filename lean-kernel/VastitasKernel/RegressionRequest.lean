import VastitasKernel.RegressionIndexedText
import VastitasKernel.Protocol

set_option autoImplicit false

/-! Wire requests of the executable regressions. Neither `Main` nor a compiler
module imports this module, so the executable and its build identity do not
depend on it. Regressions pin the wire schema epoch through `currentProtocol`,
the kernel's one definition of it (`VastitasKernel.Protocol`). -/
namespace VastitasKernel.RegressionRequest
open Lean

/-- The wire schema epoch: the kernel's `currentProtocol`. -/
abbrev currentProtocol : Nat := VastitasKernel.currentProtocol

private def sourceSpan (start size line column : Nat) : Json :=
  Json.mkObj [("start", toJson start), ("end", toJson (start + size)),
    ("line", toJson line), ("column", toJson column)]

/-- Append a path to a single-line fixture and set its span as it is written. -/
private def appendPath (text : String) (path : Json) (offset line : Nat) : Option (String × Json) := do
  let spelling := String.intercalate "::" (← (path.getObjValAs? (List String) "path").toOption)
  let span := sourceSpan (offset + text.utf8ByteSize) spelling.utf8ByteSize line (text.length + 1)
  return (text ++ spelling, path.setObjVal! "span" span)

private def appendPaths (text : String) (paths : Array Json) (offset line : Nat) : Option (String × Json) := do
  let mut result := text
  let mut positioned := #[]
  for path in paths do
    let (next, p) ← appendPath (if positioned.isEmpty then result else result ++ ", ") path offset line
    result := next
    positioned := positioned.push p
  return (result, .arr positioned)

/-- Give each handwritten smooth space in the algebra and geometry regressions
a physical declaration and the spans that the public wire checker requires. -/
private def smoothLine (d : Json) (offset line : Nat) : Option (String × Json) := do
  guard ((← (d.getObjValAs? String "kind").toOption) == "smooth_affine")
  let name ← (d.getObjValAs? String "name").toOption
  let isPublic ← (d.getObjValAs? Bool "public").toOption
  let impl ← (d.getObjVal? "implementation").toOption
  let dimension ← (d.getObjValAs? String "dimension").toOption
  let coordinates ← (d.getObjValAs? (List String) "coordinates").toOption
  let visibility := if isPublic then "pub " else ""
  let head := visibility ++ "indexed affine " ++ name ++ "("
  let (throughImpl, impl) ← appendPath head impl offset line
  let text := throughImpl ++ ") = Affine(" ++ dimension ++ ")[" ++ String.intercalate ", " coordinates ++ "];"
  let declarationSpan := sourceSpan (offset + visibility.utf8ByteSize) (text.utf8ByteSize - visibility.utf8ByteSize)
    line (visibility.length + 1)
  return (text, (d.setObjVal! "span" declarationSpan).setObjVal! "implementation" impl)

private def familyLine (d : Json) (head : String) (offset line : Nat) : Option (String × Json) := do
  let mut text := head ++ "("
  let mut params := #[]
  for param in ← (d.getObjValAs? (Array Json) "parameters").toOption do
    if !params.isEmpty then text := text ++ ", "
    let kind ← (param.getObjValAs? String "kind").toOption
    match kind with
    | "object" | "frame" =>
      let key := if kind == "object" then "domain" else "family"
      let path ← (param.getObjVal? key).toOption
      let (next, ref) ← appendPath (text ++ kind ++ "(") path offset line
      text := next ++ ")"
      params := params.push (param.setObjVal! key ref)
    | "domain" | "marker" | "natural" =>
      text := text ++ kind
      params := params.push param
    | _ => failure
  let repr ← (d.getObjValAs? String "representation").toOption
  let rules ← (← (d.getObjValAs? (List Json) "constraints").toOption).mapM RegressionIndexedText.familyConstraint
  return (text ++ ") = " ++ repr ++ " constraints(" ++ String.intercalate ", " rules ++ ");",
    d.setObjVal! "parameters" (.arr params))

private def indexedLine (d : Json) (offset line : Nat) : Option (String × Json) := do
  if let some smooth := smoothLine d offset line then return smooth
  let name ← (d.getObjValAs? String "name").toOption
  let visible ← (d.getObjValAs? Bool "public").toOption
  let vis := if visible then "pub " else ""
  let kind ← (d.getObjValAs? String "kind").toOption
  let head := vis ++ "indexed " ++ kind ++ " " ++ name
  let (text, positioned) : String × Json ← match kind with
    | "family" => familyLine d head offset line
    | "implementation" => do
      let (start, marker) ← appendPath (head ++ "(") (← (d.getObjVal? "marker").toOption) offset line
      let repr ← (d.getObjValAs? String "representation").toOption
      let caps ← (d.getObjValAs? (List String) "capabilities").toOption
      let caps := caps.map fun c => if c == "dimension" then "dim" else c
      pure (start ++ ", " ++ repr ++ ") capabilities(" ++ String.intercalate ", " caps ++ ");",
        d.setObjVal! "marker" marker)
    | "classification" => do
      let (start, parents) ← appendPaths (head ++ " { parents(") (← (d.getObjValAs? (Array Json) "parents").toOption) offset line
      let (text, domain) ← appendPaths (start ++ "); domain(") (← (d.getObjValAs? (Array Json) "domain").toOption) offset line
      pure (text ++ "); };", (d.setObjVal! "parents" parents).setObjVal! "domain" domain)
    | _ => do
      let (keyword, suffix) ← RegressionIndexedText.syntaxOf d
      pure (vis ++ "indexed " ++ keyword ++ " " ++ name ++ suffix ++ ";", d)
  return (text, positioned.setObjVal! "span" (sourceSpan (offset + vis.utf8ByteSize)
    (text.utf8ByteSize - vis.utf8ByteSize) line (vis.length + 1)))

/-- Handwritten regression requests carry their physical manifest and source.
Malformed raw records still reach the wire decoder and semantic diagnostics. -/
def package (name : String) (modules : List Json) (version : Nat := currentProtocol)
    (packageVersion : String := "0.1.0") : Json := Id.run do
  let owner := s!"/{name}/Vastitas.toml"
  let file := s!"/{name}/{name}.vast"
  let manifest := s!"[package]\nname = '{name}'\nversion = '{packageVersion}'\nedition = '{currentEdition}'\nroot = '{name}.vast'\n"
  let offset := manifest.utf8ByteSize + 1
  let base := toJson offset
  let mut text := ""
  let mut line := 1
  let mut physical := #[]
  for m in modules do
    if (m.getObjVal? "path").toOption != some (.arr #[]) then
      physical := physical.push m
    else
      let mut root := m.setObjVal! "span" (sourceSpan offset 0 1 1)
      if let .ok ds := m.getObjValAs? (Array Json) "indexed_declarations" then
        let mut declarations := #[]
        for d in ds do
          if let some (source, positioned) := indexedLine d (offset + text.utf8ByteSize) line then
            text := text ++ source ++ "\n"
            line := line + 1
            declarations := declarations.push positioned
          else declarations := declarations.push d
        root := root.setObjVal! "indexed_declarations" (.arr declarations)
      physical := physical.push root
  let entry := Json.mkObj [("offset",base),("text",toJson text),("files",.arr #[
    Json.mkObj [("path",owner),("offset",toJson (0 : Nat)),("text",manifest)],
    Json.mkObj [("path",file),("offset",base)]])]
  return Json.mkObj [("version", toJson version), ("file", owner), ("root", owner), ("root_source", entry),
    ("packages", toJson [Json.mkObj [
      ("source", owner), ("name", name), ("version", packageVersion), ("edition", currentEdition),
      ("dependencies", toJson ([] : List Json)), ("modules", .arr physical)]])]

end VastitasKernel.RegressionRequest
