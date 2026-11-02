import VastitasKernel.LegacySource
import VastitasKernel.IndexedProtocol
import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedCodegen

/-! Actual public authority composition, starting from frontend JSON captured by
`tests/edit_authority.rs`. These executable regressions supplement the retained
Edit/Authority/Namespace tests; they do not use their retired top-level checkers.
The fixture library is not an ordinary compiler/runtime dependency. -/
namespace VastitasPublicTest.AuthorityRegression
open Lean VastitasKernel Indexed.Core Indexed.Core.Semantics

private def fixture : Json :=
  (Json.parse (include_str "../../tests/fixtures/edit-authority.json")).toOption.getD .null
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
  (values (values fixture "packages")[2]! "modules")[0]!
private def originalEvents : Array Json := values (get rootModule "assembly") "events"
private def events (xs : Array Json) : Json :=
  editModule fixture "app" [] fun m =>
    m.setObjVal! "assembly" ((get m "assembly").setObjVal! "events" (toJson xs))
private def event (index : Nat) (edit : Json → Json) : Json := events (originalEvents.modify index edit)
private def named (name : String) : Json := Json.mkObj [("kind", toJson "named"), ("name", toJson name)]
private def contributionMethod (j : Json) (pkg : String) (path : List String) (edit : Json → Json) : Json :=
  editModule j pkg path fun m => editAt m "contributions" 0 fun c => editAt c "methods" 0 edit

private def acceptedCore (input : Json) : Except Diagnostic (Typing.CheckedModule true) := do
  if get input "version" == toJson (7 : Nat) then
    return (← Indexed.Wire.check input true).checked.executable.core
  return (← Indexed.LegacySource.check input true).checked.executable.core

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
    let result := if get input "version" == toJson (7 : Nat) then
      (Indexed.Wire.check input requireMain).map fun _ => ()
    else (Indexed.LegacySource.check input requireMain).map fun _ => ()
    match result with
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
  for version in [6, 7] do
    checkGood s!"protocol {version} nested loans and transfer" (fixture.setObjVal! "version" (toJson version)) 44
    checkGood s!"protocol {version} alias preserves identity"
      ((event 2 (·.setObjVal! "contribution" (toJson ["alias", "ops", "sum"]))).setObjVal! "version" (toJson version)) 44
    for (name, input, code) in cases do
      checkBad s!"protocol {version}: {name}" (input.setObjVal! "version" (toJson version)) code
  -- A real protocol-5 edit still passes through the common authority/body
  -- composition after removing the protocol-6-only declarations and events.
  let five := (events #[originalEvents[0]!,
    originalEvents[2]!.setObjVal! "loan" (toJson "parent"), originalEvents[4]!, originalEvents[7]!]).setObjVal! "version" (toJson (5 : Nat))
  let five := editModule five "base" [] fun m => editAt (dropField m "transfers") "grants" 0 fun grant =>
    (dropField grant "delegable").setObjVal! "grantee_path" (toJson ["ops"])
  let five := editModule five "addon" [] (fun m => dropField m "delegations")
  checkGood "protocol 5 direct exclusive edit" five 42
  checkBad "protocol 5 unapplied body" (contributionMethod five "base" []
    (·.setObjVal! "return_type" (named "Bool"))) "E_TYPE"
  for version in [2, 3, 4, 5] do
    checkBad s!"authority metadata cannot downgrade to {version}"
      (fixture.setObjVal! "version" (toJson version)) "E_PROTOCOL"
  IO.println s!"public authority: five accepted/executable cases, {cases.length * 2 + 5} rejected inputs under both check/emit policies passed"

end VastitasPublicTest.AuthorityRegression
