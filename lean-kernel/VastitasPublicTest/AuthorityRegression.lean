import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedCodegen
import VastitasKernel.ResourceProtocol

/-! Actual public authority composition, starting from frontend JSON captured by
`tests/edit_authority.rs`. These executable regressions supplement the retained
Edit/Authority/Namespace tests; they do not use their retired top-level checkers.
The fixture library is not an ordinary compiler/runtime dependency. -/
namespace VastitasPublicTest.AuthorityRegression
open Lean VastitasKernel Indexed.Core Indexed.Core.Semantics

open AssemblySource (Item) in
#eval show IO Unit from do
  let preamble := "// β } assemble hidden {}\r\n" ++
    "pub mod assemble { fn assemble() -> Int { 0 } } use a::assemble;\n" ++
    "indexed test = assume(\"escaped \\\" } assemble hidden {} ;\");\n"
  let source := preamble ++ "　assemble a :: f {\n  borrow b as parent { delegate g { apply c,d::v; } }\n}\n"
  let base := 111
  let span (lo hi line col : Nat) : Span :=
    ⟨base + preamble.utf8ByteSize + lo, base + preamble.utf8ByteSize + hi, line, col⟩
  let wanted : List Item := [
    .family ["a", "f"] (span 3 20 4 2),
    .borrow ["b"] (some "parent") (span 23 43 5 3),
    .delegate ["g"] none (span 44 56 5 24),
    .apply [["c"], ["d", "v"]] (span 57 70 5 37),
    .close (span 71 72 5 51), .close (span 73 74 5 53), .close (span 75 76 6 1)]
  unless (AssemblyText.parse source base).toOption == some wanted do
    throw (IO.userError "wrong source words, UTF-8 offsets, scalar columns or closing braces")
  for input in ["{ assemble hidden {}", "} assemble f {}", "pub assemble f {}",
      "assembly {}", "pub assembly {}", "pub mod a { mod b { assemble f {} } }",
      "assemble f { apply x : : y; }", "assemble f { apply x,; }",
      "assemble f { borrow b { transfer t; } }", "assemble f { delegate d {} }",
      "assemble f { apply c;", "// source\u2028assemble f {}", "/* comment */ assemble f {}"] do
    if (AssemblyText.parse input 0).isOk then
      throw (IO.userError s!"incorrectly accepted source: {repr input}")
  IO.println "assembly source: command operands, UTF-8 positions, contextual names and malformed scopes passed"

private def fixture : Json :=
  (Json.parse (include_str "../../tests/fixtures/edit-recipients.json")).toOption.getD .null
private def get (j : Json) (key : String) : Json := (j.getObjVal? key).toOption.getD .null
private def values (j : Json) (key : String) : Array Json :=
  (j.getObjValAs? (Array Json) key).toOption.getD #[]
private def dropField (j : Json) (key : String) : Json :=
  Json.mkObj ((j.getObj?).toOption.getD {} |>.toArray.toList.filter (·.1 != key))
private def editAt (j : Json) (field : String) (index : Nat) (edit : Json → Json) : Json :=
  j.setObjVal! field (toJson ((values j field).modify index edit))
private def editModule (j : Json) (pkg : String) (path : List String) (edit : Json → Json) : Json :=
  j.setObjVal! "packages" (toJson ((values j "packages").map fun p =>
    if get p "name" != toJson pkg then p else
      p.setObjVal! "modules" (toJson ((values p "modules").map fun m =>
        if get m "path" == toJson path then edit m else m))))
private def rootModule : Json :=
  ((values fixture "packages").find? (get · "name" == toJson "app") |>.map (values · "modules")
    |>.bind (·[0]?)).getD .null
private def originalEvents : Array Json := values (get rootModule "assembly") "events"
private def events (xs : Array Json) : Json :=
  editModule fixture "app" [] fun m =>
    m.setObjVal! "assembly" ((get m "assembly").setObjVal! "events" (toJson xs))
private def originalSource : Array Json := values (get rootModule "assembly") "source"
private def withSource (j : Json) (items : Array Json) : Json :=
  editModule j "app" [] fun m =>
    m.setObjVal! "assembly" ((get m "assembly").setObjVal! "source" (toJson items))
private def editText (j : Json) (edit : Nat → String → String) : Json :=
  let file := get j "root_source"
  let base := (get file "offset").getNat?.toOption.getD 0
  let text := (get file "text").getStr?.toOption.getD ""
  j.setObjVal! "root_source" (file.setObjVal! "text" (toJson (edit base text)))

/-- Replace selected single-line ASCII commands with spaces, preserving every
surviving coordinate and the later main function in the physical fixture. -/
private def omitCommands (indices : List Nat) (base : Nat) (text : String) : String :=
  indices.foldl (fun text i =>
    let span := get originalSource[i]! "span"
    let lo := (get span "start").getNat?.toOption.getD 0 - base
    let hi := (get span "end").getNat?.toOption.getD 0 - base
    String.Pos.Raw.extract text 0 ⟨lo⟩ ++ String.ofList (List.replicate (hi - lo) ' ') ++
      String.Pos.Raw.extract text ⟨hi⟩ text.rawEndPos) text
private def event (index : Nat) (edit : Json → Json) : Json := events (originalEvents.modify index edit)
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def contributionMethod (j : Json) (pkg : String) (path : List String) (edit : Json → Json) : Json :=
  editModule j pkg path fun m => editAt m "contributions" 0 fun c => editAt c "methods" 0 edit

private def acceptedCore (input : Json) : Except Diagnostic (Typing.CheckedModule true) := do
  let accepted ← ResourceSource.Wire.check input true
  if entry : accepted.input.entry = none then
    return (by simpa [entry] using accepted.checked.pureProgram.executable.core)
  else throw {code := "E_TEST", message := "authority fixture unexpectedly has a resource entry"}

private def checkGood (name : String) (input : Json) (expected : Int) : IO Unit := do
  let .ok checked := acceptedCore input
    | throw (IO.userError s!"public authority {name}: unexpectedly rejected")
  let some main := checked.module.functions.find? (fun f => some f.id == checked.module.main)
    | throw (IO.userError s!"public authority {name}: missing main")
  unless eval checked.module 512 (fun _ => none) main.body == some (.integer expected) do
    throw (IO.userError s!"public authority {name}: wrong executable Core result")
  unless (Codegen.generate checked).isOk do
    throw (IO.userError s!"public authority {name}: exact returned Core cannot be emitted")

private def checkBad (name : String) (input : Json) (code : String) : IO Unit := do
  -- Check and emit use different main policies. Neither may accept a forgery.
  for requireMain in [false, true] do
    match (ResourceSource.Wire.check input requireMain).map fun _ => () with
    | .ok _ => throw (IO.userError s!"public authority {name}: forgery accepted")
    | .error diagnostic => unless diagnostic.code == code do
        throw (IO.userError s!"public authority {name}: expected {code}, got {diagnostic.code}: {diagnostic.message}")

private def cases : List (String × Json × String) := [
  ("claimed transfer issuer", editModule fixture "base" [] (fun m =>
    editAt m "transfers" 0 (·.setObjVal! "issuer" (toJson "trusted"))), "E_PROTOCOL"),
  ("claimed authorized event", event 1 (·.setObjVal! "authorized" (toJson true)), "E_PROTOCOL"),
  ("nondelegable parent", editModule fixture "base" [] (fun m =>
    editAt m "grants" 0 (·.setObjVal! "delegable" (toJson false))), "E_OWNER"),
  ("child widens parent region", editModule fixture "addon" [] (fun m =>
    editAt m "delegations" 0 (·.setObjVal! "region" (toJson [["Int", "Int"], ["Nat", "Nat"]]))), "E_OWNER"),
  ("delegation to wrong module", editModule fixture "addon" [] (fun m =>
    editAt m "delegations" 0 (·.setObjVal! "grantee_path" (toJson ([] : List String)))), "E_OWNER"),
  ("suspended parent editing", event 2 (·.setObjVal! "loan" (toJson "parent")), "E_BORROW"),
  ("outside-in return", events (originalEvents.set! 3 originalEvents[4]!), "E_BORROW"),
  ("transfer during a loan", events (#[originalEvents[0]!, originalEvents[5]!] ++ originalEvents.extract 1 8), "E_BORROW"),
  ("old owner after transfer", event 6 (·.setObjVal! "contribution" (toJson ["base", "old"])), "E_OWNER"),
  ("incomplete assembly", events (originalEvents.pop), "E_ASSEMBLY"),
  ("empty child winning footprint", editModule fixture "addon" [] (fun m =>
    editAt m "delegations" 0 (·.setObjVal! "region" (toJson ([] : List Json)))), "E_IMPACT"),
  ("unapplied body still checked", contributionMethod fixture "base" []
    (·.setObjVal! "return_type" (named "Bool")), "E_TYPE"),
  ("applied body still checked", contributionMethod fixture "addon" ["ops"]
    (·.setObjVal! "return_type" (named "Bool")), "E_TYPE"),
  ("losing and out-of-domain ordinary body", editModule fixture "base" [] (fun m =>
    editAt m "methods" 0 (·.setObjVal! "return_type" (named "Bool"))), "E_TYPE"),
  ("unapplied body claimed Core", contributionMethod fixture "base" []
    (·.setObjVal! "checked" (toJson true)), "E_PROTOCOL"),
  ("unresolved contribution provenance", event 2
    (·.setObjVal! "contribution" (toJson ["missing", "ops", "sum"])), "E_NAME"),
  ("private contribution cannot cross modules", editModule fixture "addon" ["ops"] (fun m =>
    editAt m "contributions" 0 (·.setObjVal! "public" (toJson false))), "E_VISIBILITY"),
  ("namespace dependency cannot be forged", editModule fixture "app" [] (·.setObjVal! "owner" (toJson "trusted")), "E_PROTOCOL")]

#eval show IO Unit from do
  checkGood "the frontend fixture" fixture 44
  let alias := event 2 (·.setObjVal! "contribution" (toJson ["alias", "ops", "sum"]))
  checkBad "the valid alias trace differs from its source operand" alias "E_ASSEMBLY"
  let alias := withSource alias (originalSource.modify 3
    (·.setObjVal! "contributions" (toJson [["alias", "ops", "sum"]])))
  checkBad "matching items and events differ from the original bytes" alias "E_ASSEMBLY"
  checkGood "an alias preserves identity" (editText alias (fun _ s => s.replace "addon::ops::sum" "alias::ops::sum")) 44
  for (name, input, code) in cases do
    checkBad name input code
  -- A direct exclusive edit, without delegations, transfers and their events,
  -- passes through the same authority/body composition.
  let direct := events #[originalEvents[0]!,
    originalEvents[2]!.setObjVal! "loan" (toJson "parent"), originalEvents[4]!, originalEvents[7]!]
  let direct := withSource direct #[originalSource[0]!, originalSource[1]!, originalSource[3]!,
    originalSource[5]!, originalSource[8]!]
  let direct := editText direct (omitCommands [2,4,6,7])
  let direct := editModule direct "base" [] fun m => editAt (dropField m "transfers") "grants" 0 fun grant =>
    (dropField grant "delegable").setObjVal! "grantee_path" (toJson ["ops"])
  let direct := editModule direct "addon" [] (fun m => dropField m "delegations")
  checkBad "removed declarations still occur in the physical dependencies" direct "E_ASSEMBLY"
  let files := get direct "root_source"
  let rows := (values files "files").map fun row => Id.run do
    let .ok text := (get row "text").getStr? | return row
    let text := text.replace "addon delegable" "addon::ops     "
    let lines := (text.splitOn "\n").map fun line =>
      if line.startsWith "pub transfer " || line.startsWith "pub delegation " then
        String.ofList (List.replicate line.length ' ')
      else line
    return row.setObjVal! "text" (toJson (String.intercalate "\n" lines))
  let direct := direct.setObjVal! "root_source" (files.setObjVal! "files" (toJson rows))
  checkGood "a direct exclusive edit" direct 42
  checkBad "a direct edit's unapplied body" (contributionMethod direct "base" []
    (·.setObjVal! "return_type" (named "Bool"))) "E_TYPE"
  IO.println s!"public authority: three accepted/executable cases, {cases.length + 4} rejected inputs under both check/emit policies passed"

end VastitasPublicTest.AuthorityRegression
