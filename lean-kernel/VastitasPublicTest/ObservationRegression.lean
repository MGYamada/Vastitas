import VastitasPublicTest.SingletonFixtures
import VastitasKernel.ResourceProtocol
import VastitasKernel.RegressionRequest

/-! The observations of `show!` on the wire and the entry point that native
generation writes (#836). The public decoder and checker accept observations
only on the entry point `main`, only on its
top-level `let` statements in order, and only of values that `show!` writes.
The entry point returns the exit status of `main` and writes each observed
value once, in the order of the statements. -/
namespace VastitasKernel.ResourceSource.Wire.ObservationRegression
open Lean

private def span : Json := Json.mkObj [
  ("start", toJson (0 : Nat)), ("end", toJson (1 : Nat)),
  ("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
private def withField (j : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: ((j.getObj?.toOption.getD {}).toArray.toList.filter (·.1 != key)))
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def integer (value : String) : Json := Json.mkObj [
  ("kind", toJson "integer"), ("value", toJson value), ("span", span)]
private def var (name : String) : Json := Json.mkObj [
  ("kind", toJson "variable"), ("name", toJson name), ("span", span)]
private def call (callee : String) (arguments : List Json) : Json := Json.mkObj [
  ("kind", toJson "call"), ("callee", toJson callee), ("args", toJson arguments), ("span", span)]
private def binary (op : String) (left right : Json) : Json := Json.mkObj [
  ("kind", toJson "binary"), ("op", toJson op), ("left", left), ("right", right), ("span", span)]
private def letE (name : String) (value : Json) (annotation : Json := Json.null) : Json := Json.mkObj [
  ("kind", toJson "let"), ("name", toJson name), ("annotation", annotation), ("value", value), ("span", span)]
private def fn (name : String) (statements : List Json) (result : Json)
    (observations : Option (List Json) := none) : Json :=
  let function := Json.mkObj [
    ("name", toJson name), ("params", toJson ([] : List Json)), ("return_type", named "Int"),
    ("body", Json.mkObj [("statements", toJson statements), ("result", result), ("span", span)]),
    ("public", toJson false), ("span", span)]
  match observations with
  | some observations => withField function "observations" (toJson observations)
  | none => function
private def observation (statement : Nat) (label : String) : Json := Json.mkObj [
  ("statement", toJson statement), ("label", toJson label)]
private def mod (functions : List Json) (path : List String := []) : Json := Json.mkObj [
  ("path", toJson path), ("public", toJson true), ("span", span),
  ("imports", toJson ([] : List Json)), ("generics", toJson ([] : List Json)),
  ("methods", toJson ([] : List Json)), ("functions", toJson functions)]
private def input (modules : List Json) (version : Nat := RegressionRequest.currentProtocol) : Json :=
  RegressionRequest.package "show" modules version "1.0.0"

/-- `let a = show!(20 + 22); let n: Nat = show!(7); let b = show!(a < 50);
let u = show!(()); let p = show!(pair(a, -3)); a - 342`. -/
private def statements : List Json := [
  letE "a" (binary "+" (integer "20") (integer "22")),
  letE "n" (integer "7") (named "Nat"),
  letE "b" (binary "<" (var "a") (integer "50")),
  letE "u" (Json.mkObj [("kind", toJson "unit"), ("span", span)]),
  letE "p" (call "pair" [var "a", Json.mkObj [
    ("kind", toJson "unary"), ("op", toJson "-"), ("operand", integer "3"), ("span", span)]])]
private def shown : List Json := [observation 0 "20 + 22", observation 1 "7",
  observation 2 "a < 50", observation 3 "()", observation 4 "pair(a, -3)"]
private def observed (observations : Option (List Json) := some shown) : Json :=
  fn "main" statements (binary "-" (var "a") (integer "342")) observations
private def helper : Json := fn "helper" [] (integer "1")

private def code {α : Type} (result : Except Diagnostic α) : String :=
  match result with | .ok _ => "ok" | .error diagnostic => diagnostic.code

/-- The positions of `parts` in `text`, which must occur in this order. -/
private def inOrder (text : String) (parts : List String) : Bool :=
  (parts.foldl (fun rest part => rest.bind fun rest =>
    match rest.splitOn part with
    | _ :: after :: more => some (String.intercalate part (after :: more))
    | _ => none) (some text)).isSome

#eval show IO Unit from do
  let rejected : List (String × Json × String) := [
    ("an observation outside main", input [mod [observed none,
      fn "helper" [letE "x" (integer "1") (named "Int")] (var "x") (some [observation 0 "1"])]], "E_UNSUPPORTED"),
    ("main of another module", input [mod [observed none], mod [observed] ["inner"]], "E_UNSUPPORTED"),
    ("no such statement", input [mod [observed (some [observation 5 "x"])]], "E_PROTOCOL"),
    ("statements out of order", input [mod [observed (some [observation 1 "7", observation 0 "20 + 22"])]], "E_PROTOCOL"),
    ("a statement twice", input [mod [observed (some [observation 0 "a", observation 0 "a"])]], "E_PROTOCOL"),
    ("an empty list", input [mod [observed (some [])]], "E_PROTOCOL"),
    ("a foreign observation field", input [mod [observed (some [withField (observation 0 "a") "type" (toJson "Int")])]],
      "E_PROTOCOL"),
    ("a function value", input [mod [helper, fn "main" [letE "f" (var "helper")] (integer "0")
      (some [observation 0 "helper"])]], "E_TYPE")]
  for (name, json, expected) in rejected do
    for requireMain in [false, true] do
      let actual := code (check json requireMain)
      unless actual == expected do
        throw (IO.userError s!"observation regression: {name}: expected {expected}, got {actual}")
  -- `vastitas check` accepts what `build` accepts, and both see the observations.
  let .ok accepted := check (RegressionRequest.physical "observed") false
    | throw (IO.userError "observation regression: the observed program is rejected")
  unless accepted.checked.observations.map (·.statement) == [0, 1, 2, 3, 4] do
    throw (IO.userError "observation regression: the checked observations differ from the wire")
  let .ok generated := emit (RegressionRequest.physical "observed")
    | throw (IO.userError "observation regression: the observed program is not generated")
  let text := generated.source
  unless inOrder text ["def main : IO UInt32 := do\n",
      "IO.eprintln (\"20 + 22\" ++ \" = \" ++ (toString ", "IO.eprintln (\"7\" ++ \" = \" ++ (toString ",
      "IO.eprintln (\"a < 50\" ++ \" = \" ++ (if ", "IO.eprintln (\"()\" ++ \" = \" ++ \"()\")",
      "IO.eprintln (\"pair(a, -3)\" ++ \" = \" ++ (\"(\" ++ toString ",
      "pure (UInt32.ofNat (Int.toNat (Int.emod ("] do
    throw (IO.userError s!"observation regression: the entry point differs:\n{text}")
  unless (text.splitOn "IO.eprintln").length == 6 do
    throw (IO.userError "observation regression: a value is written more than once")
  -- The lines go to standard error; standard output stays the program's (#840).
  unless (text.splitOn "IO.println").length == 1 do
    throw (IO.userError "observation regression: an observed value is written on standard output")
  -- A label is data: it reaches the program only as a quoted string literal.
  let sample := RegressionRequest.physical "quoted"
  let m := RegressionRequest.rootModule sample
  let .ok functions := m.getObjValAs? (Array Json) "functions" | throw (IO.userError "missing observed main")
  let changed := functions[0]!.setObjVal! "observations" (toJson [observation 0 "\"); IO.Process.exit 9; (\"\\"])
  let .ok quoted := emit (RegressionRequest.withRootModule sample (m.setObjVal! "functions" (.arr #[changed])))
    | throw (IO.userError "observation regression: a label changed acceptance")
  unless inOrder quoted.source ["IO.eprintln (\"\\\"); IO.Process.exit 9; (\\\"\\\\\" ++ \" = \""] do
    throw (IO.userError s!"observation regression: a label is not quoted:\n{quoted.source}")
  -- Without observations the entry point returns the exit status and writes nothing.
  let .ok plain := emit (RegressionRequest.physical "plain")
    | throw (IO.userError "observation regression: the plain program is not generated")
  unless inOrder plain.source ["\ndef main : IO UInt32 :=\n  pure (UInt32.ofNat (Int.toNat (Int.emod VastitasGenerated.f_"]
      && (plain.source.splitOn "IO.println").length == 1 && (plain.source.splitOn "IO.eprintln").length == 1 do
    throw (IO.userError s!"observation regression: the plain entry point differs:\n{plain.source}")
  IO.println s!"observations: {rejected.length * 2 + 4} wire and entry-point cases passed"

end VastitasKernel.ResourceSource.Wire.ObservationRegression
