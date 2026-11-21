import VastitasPublicTest.SingletonFixtures
import VastitasKernel.ResourceProtocol
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

/-! The package envelope of the indexed decoders (`Indexed.Wire.module` and
`Indexed.Wire.package`) through the public checker `ResourceSource.Wire.check`:
a request is accepted only with its exact fields, at the schema epoch, and
with every body checked. Each rejection is pinned by its code and message, so
that a case cannot pass for another reason. The decoders spell the op, the
capability and the `geometry_compat` slot of `dim` as `dim` (#778), which
decodes to the internal `.dimension`; the spelling `dimension` is rejected. -/
namespace VastitasKernel.Indexed.Wire.Regression
open Lean

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
  ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def withField (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key)))
private def expr : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson "42"), ("span", span)]
private def body (result := expr) : Json := Json.mkObj [
  ("statements", toJson ([] : List Json)), ("result", result), ("span", span)]
private def fn (name := "main") (result := expr) : Json := Json.mkObj [
  ("name", toJson name), ("params", toJson ([] : List Json)),
  ("return_type", Json.mkObj [("kind", toJson "named"), ("name", toJson "Int")]),
  ("body", body result), ("public", toJson false), ("span", span)]
private def marker : Json := Json.mkObj [
  ("kind", toJson "marker"), ("name", toJson "Marker"), ("public", toJson false), ("span", span)]
private def reference (name : String) : Json := Json.mkObj [("path", toJson [name]), ("span", span)]
/-- An implementation of `Marker` with `capabilities`. -/
private def implementation (capabilities : List String) : Json := Json.mkObj [
  ("kind", toJson "implementation"), ("name", toJson "Implementation"), ("public", toJson false),
  ("span", span), ("marker", reference "Marker"), ("representation", toJson "affine_descriptor"),
  ("capabilities", toJson capabilities)]
private def baseline := RegressionRequest.physical "wire"
private def mod : Json := RegressionRequest.rootModule baseline
private def input (m := mod) : Json := RegressionRequest.withRootModule baseline m

private def declarations (items : List Json) : Json := input (withField mod "indexed_declarations" (toJson items))

/-- The code and message of the rejection, or `none` for an acceptance. -/
private def answer (json : Json) (requireMain : Bool) : Option (String × String) :=
  match ResourceSource.Wire.check json requireMain with
  | .ok _ => none
  | .error d => some (d.code, d.message)

#eval show IO Unit from do
  let library := RegressionRequest.physical "wireLib"
  let tests : List (String × Json × Bool × Option (String × String)) := [
    ("actual acceptance", input, true, none),
    ("library", library, false, none),
    ("library needs main for emit", library, true,
      some ("E_MAIN", "entry point must have signature fn main() -> Int")),
    -- `Wire.check` checks the version itself, after `Main`'s own check.
    ("a retired version", withField input "version" (toJson (9 : Nat)), true,
      some ("E_PROTOCOL", s!"expected protocol {RegressionRequest.currentProtocol}")),
    ("an input field", withField input "input" (toJson "package"), true,
      some ("E_PROTOCOL", "unknown protocol field 'input'")),
    ("a flat module", withField (withField input "functions" (toJson [fn])) "packages" (toJson ([] : List Json)),
      true, some ("E_PROTOCOL", "unknown protocol field 'functions'")),
    ("checked core injection", withField input "checked_core" (toJson true), true,
      some ("E_PROTOCOL", "unknown protocol field 'checked_core'")),
    ("declaration owner injection", declarations [withField marker "owner" (toJson "trusted")], true,
      some ("E_PROTOCOL", "unknown protocol field 'owner'")),
    ("reserved declaration", declarations [withField marker "name" (toJson "Int")], true,
      some ("E_RESERVED", "'Int' is reserved")),
    ("the capabilities origin and dim of an implementation", RegressionRequest.physical "wireImplementation",
      true, none),
    ("the spelling dimension of the capability dim", declarations [marker, implementation ["dimension"]], true,
      some ("E_PROTOCOL", "unsupported implementation capability")),
    ("backend lifted reference", input (withField mod "functions"
      (toJson [fn "main" (Json.mkObj [("kind", toJson "lifted"), ("id", toJson (0 : Nat)), ("span", span)])])), true,
      some ("E_PROTOCOL", "unknown indexed expression kind")),
    ("unused body", input (withField mod "functions" (toJson [fn, fn "unused"
      (Json.mkObj [("kind", toJson "boolean"), ("value", toJson true), ("span", span)])])), true,
      some ("E_TYPE", "expected Int, found Bool")),
    ("foreign body field", input (withField mod "functions"
      (toJson [withField (fn) "body" (withField (body) "checked" (toJson true))])), true,
      some ("E_PROTOCOL", "unknown protocol field 'checked'"))]
  for (name, json, requireMain, expected) in tests do
    let actual := answer json requireMain
    unless actual == expected do
      throw (IO.userError s!"indexed wire regression: {name}: expected {repr expected}, got {repr actual}")
  IO.println s!"indexed wire: {tests.length} cases passed"

/-- The object type `D` with the marker `M`, as the wire writes it. -/
private def objectType : Json := Json.mkObj [("domain", reference "D"), ("marker", reference "M")]
/-- A `geometry_compat` setting whose slot of `dim` is spelled `slot`. -/
private def setting (slot : String) : Json := Json.mkObj ([
  ("domain", "D"), ("marker", "M"), ("base_object", "B"), ("affine", "A"), ("base", "b"),
  ("origin", "o"), ("identity", "i"), (slot, "dimensionOf")].map fun (key, value) => (key, toJson value))
private def check := RegressionSupport.check "indexed wire regression failed"

#eval check "the capability dim decodes to .dimension"
  (match capability (toJson "dim") with | .ok .dimension => true | _ => false)
#eval check "the capability spelled dimension is rejected"
  (match capability (toJson "dimension") with
    | .error message => message == "unsupported implementation capability" | .ok _ => false)
#eval check "the op dim decodes, and its family builds .dimension"
  (match primitive (Json.mkObj [("op", toJson "dim"), ("domain", objectType)]), primitiveFamily? "dim" with
    | .ok decoded, some family => decoded.op == "dim" &&
        (match family.build [.objectType default] with | .ok (.dimension _) => true | _ => false)
    | _, _ => false)
#eval check "the op spelled dimension is rejected, and no family has it"
  ((primitiveFamily? "dimension").isNone &&
    match primitive (Json.mkObj [("op", toJson "dimension"), ("domain", objectType)]) with
    | .error message => message == "unknown indexed primitive contract" | .ok _ => false)
#eval check "the geometry_compat slot dim is the setting's dimension"
  (match geometrySetting (setting "dim") with | .ok decoded => decoded.dimension.path == ["dimensionOf"] | _ => false)
#eval check "the geometry_compat slot spelled dimension is rejected"
  (match geometrySetting (setting "dimension") with
    | .error message => message == "unknown protocol field 'dimension'" | .ok _ => false)

end VastitasKernel.Indexed.Wire.Regression
