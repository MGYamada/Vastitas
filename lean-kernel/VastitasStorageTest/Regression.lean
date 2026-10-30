import VastitasKernel.StorageProtocol

namespace VastitasKernel.Storage.Wire.Regression
open Lean

private def mutateAction (input : Json) (index : Nat) (change : Json → Json) : Json :=
  let items := ((input.getObjVal? "statements").bind Json.getArr?).toOption.getD #[]
  let item := items[index]!
  let changed := item.setObjVal! "action" (change ((item.getObjVal? "action").toOption.getD .null))
  input.setObjVal! "statements" (.arr (items.set! index changed))

private def removeStatement (input : Json) (index : Nat) : Json :=
  let items := ((input.getObjVal? "statements").bind Json.getArr?).toOption.getD #[]
  input.setObjVal! "statements" (toJson (items.toList.take index ++ items.toList.drop (index + 1)))

#eval show IO Unit from do
  let .ok fixture := Json.parse (include_str "../../tests/fixtures/storage.json")
    | throw (IO.userError "invalid shared storage fixture")
  let .ok checked := check fixture | throw (IO.userError "shared Rust storage fixture rejected")
  unless checked.input.length == 30 do throw (IO.userError "shared fixture statement coverage changed")
  let tests : List (String × Json × String) := [
    ("checked state injection", fixture.setObjVal! "checked_state" (.mkObj []), "E_PROTOCOL"),
    ("version injection is not public acceptance", fixture.setObjVal! "version" (toJson (8 : Nat)), "E_PROTOCOL"),
    ("unknown action metadata", mutateAction fixture 0 (·.setObjVal! "initialized" (toJson true)), "E_PROTOCOL"),
    ("allocation identity injection", mutateAction fixture 0 (·.setObjVal! "allocation" (toJson (5 : Nat))), "E_PROTOCOL"),
    ("symbol overflow", mutateAction fixture 0 (·.setObjVal! "owner" (toJson (2^32 : Nat))), "E_PROTOCOL"),
    ("unsigned size overflow", mutateAction fixture 0 (·.setObjVal! "elements" (toJson (2^64 : Nat))), "E_PROTOCOL"),
    ("negative size", mutateAction fixture 0 (·.setObjVal! "elements" (toJson (-1 : Int))), "E_PROTOCOL"),
    ("native allocation overflow", mutateAction fixture 0 (·.setObjVal! "elements" (toJson (2^63 : Nat))), "E_RESOURCE_OVERFLOW"),
    ("literal payload overflow", mutateAction fixture 2 (fun a => a.setObjVal! "value"
      (.mkObj [("kind", toJson "f64"), ("bits", toJson (2^64 : Nat))])), "E_PROTOCOL"),
    ("obsolete owner", mutateAction fixture 9 (·.setObjVal! "owner" (toJson (0 : Nat))), "E_RESOURCE_MOVE"),
    ("uninitialized raw plan", removeStatement fixture 2, "E_RESOURCE_INIT"),
    ("escaped owner", removeStatement fixture 9, "E_RESOURCE_ESCAPE"),
    ("invalid stride", mutateAction fixture 1 (fun a => a.setObjVal! "layout"
      (((a.getObjVal? "layout").toOption.getD .null).setObjVal! "leading" (toJson (1 : Nat)))), "E_RESOURCE_LAYOUT"),
    ("false alias evidence", mutateAction fixture 1 (fun a => a.setObjVal! "layout"
      (((a.getObjVal? "layout").toOption.getD .null).setObjVal! "disjoint" (toJson true))), "E_PROTOCOL"),
    ("wrong scalar", mutateAction fixture 2 (fun a => a.setObjVal! "value"
      (.mkObj [("kind", toJson "complex_f64"), ("real", toJson (0 : Nat)), ("imaginary", toJson (0 : Nat))])), "E_RESOURCE_TYPE")]
  for (name, input, expected) in tests do
    match check input with
    | .ok _ => throw (IO.userError s!"storage wire accepted: {name}")
    | .error diagnostic => unless diagnostic.code == expected do
      throw (IO.userError s!"storage wire {name}: expected {expected}, got {diagnostic.code}")
  IO.println s!"storage component schema: shared fixture and {tests.length} mutations passed"

end VastitasKernel.Storage.Wire.Regression
