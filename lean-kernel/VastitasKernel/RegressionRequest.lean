import Lean.Data.Json
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

/-- Give each handwritten smooth space in the algebra and geometry regressions
a physical declaration and the spans that the public wire checker requires. -/
private def smoothLine (d : Json) (offset line : Nat) : Option (String × Json) := do
  guard ((← (d.getObjValAs? String "kind").toOption) == "smooth_affine")
  let name ← (d.getObjValAs? String "name").toOption
  let isPublic ← (d.getObjValAs? Bool "public").toOption
  let impl ← (d.getObjVal? "implementation").toOption
  let implName := String.intercalate "::" (← (impl.getObjValAs? (List String) "path").toOption)
  let dimension ← (d.getObjValAs? String "dimension").toOption
  let coordinates ← (d.getObjValAs? (List String) "coordinates").toOption
  let visibility := if isPublic then "pub " else ""
  let head := visibility ++ "indexed affine " ++ name ++ "("
  let text := head ++ implName ++ ") = Affine(" ++ dimension ++ ")[" ++ String.intercalate ", " coordinates ++ "];"
  let declarationSpan := sourceSpan (offset + visibility.utf8ByteSize) (text.utf8ByteSize - visibility.utf8ByteSize)
    line (visibility.length + 1)
  let implSpan := sourceSpan (offset + head.utf8ByteSize) implName.utf8ByteSize line (head.length + 1)
  return (text, (d.setObjVal! "span" declarationSpan).setObjVal! "implementation" (impl.setObjVal! "span" implSpan))

/-- Handwritten regression requests have a physical manifest. Root smooth
spaces also have source text; other raw inputs exercise their wire checks. -/
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
          if let some (source, positioned) := smoothLine d (offset + text.utf8ByteSize) line then
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
