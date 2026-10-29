import VastitasKernel.IndexedAcceptance

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
private def mod : Json := Json.mkObj [
  ("path", toJson ([] : List String)), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson [fn]),
  ("indexed_declarations", toJson [marker])]
private def input (m := mod) : Json := Json.mkObj [
  ("version", toJson (7 : Nat)), ("input", toJson "package"), ("file", toJson "wire.vast"),
  ("root", toJson "/wire/Vastitas.toml"),
  ("packages", toJson [Json.mkObj [
    ("source", toJson "/wire/Vastitas.toml"), ("name", toJson "wire"), ("version", toJson "1.0.0"),
    ("dependencies", toJson ([] : List Json)), ("modules", toJson [m])]])]

#eval show IO Unit from do
  let tests : List (String × Json × Bool × Bool) := [
    ("actual acceptance", input, true, true),
    ("library", input (withField mod "functions" (toJson ([] : List Json))), false, true),
    ("library needs main for emit", input (withField mod "functions" (toJson ([] : List Json))), true, false),
    ("wrong envelope", withField input "version" (toJson (6 : Nat)), true, false),
    ("flat input", withField input "input" (toJson "flat"), true, false),
    ("checked core injection", withField input "checked_core" (toJson true), true, false),
    ("declaration owner injection", input (withField mod "indexed_declarations"
      (toJson [withField marker "owner" (toJson "trusted")])), true, false),
    ("reserved declaration", input (withField mod "indexed_declarations"
      (toJson [withField marker "name" (toJson "Int")])), true, false),
    ("unsupported capability", input (withField mod "indexed_declarations"
      (toJson [withField marker "capabilities" (toJson ["dimension"])])), true, false),
    ("backend lifted reference", input (withField mod "functions"
      (toJson [fn "main" (Json.mkObj [("kind", toJson "lifted"), ("id", toJson (0 : Nat)), ("span", span)])])), true, false),
    ("unused body", input (withField mod "functions" (toJson [fn, fn "unused"
      (Json.mkObj [("kind", toJson "boolean"), ("value", toJson true), ("span", span)])])), true, false),
    ("foreign body field", input (withField mod "functions"
      (toJson [withField (fn) "body" (withField (body) "checked" (toJson true))])), true, false)]
  for (name, json, requireMain, expected) in tests do
    let result := check json requireMain
    unless result.isOk == expected do
      throw (IO.userError s!"indexed wire regression: {name}: {result.toOption.isSome}")
  IO.println s!"indexed wire: {tests.length} cases passed"

end VastitasKernel.Indexed.Wire.Regression
