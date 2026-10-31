import VastitasKernel.StorageFunctionProtocol

namespace VastitasKernel.Storage.Functions.Regression

private def changed (program : Program) (id : Nat) (transform : Function → Function) : Program :=
  {program with functions := program.functions.map fun function =>
    if function.id == id then transform function else function}

private def checkError (name : String) (program : Program) (expected : String) : IO Unit := do
  match check program with
  | .ok _ => throw (IO.userError s!"resource function accepted invalid program: {name}")
  | .error error => unless error.code == expected do
    throw (IO.userError s!"{name}: expected {expected}, got {error.code}: {error.message}")

private def full : Layout := ⟨0,2,2,2,false⟩
private def owned : OwnedType := ⟨.f64,8,[]⟩
private def value : Literal := .f64 0x4008000000000000

#eval show IO Unit from do
  let .ok json := Lean.Json.parse (include_str "../../tests/fixtures/storage-functions.json")
    | throw (IO.userError "invalid shared resource-function fixture")
  let .ok wire := Wire.check json | throw (IO.userError "resource function fixture rejected")
  let program := wire.input
  let .ok native := Native.compile wire.checked.statements | throw (IO.userError "function native lowering failed")
  unless (native.instructions.filter fun instruction => match instruction with | .allocate .. => true | _ => false).length == 4 do
    throw (IO.userError "probe allocations leaked into executable expansion")
  unless (check {program with functions := program.functions.reverse}).isOk do
    throw (IO.userError "declaration order changed resource acceptance")
  let cases : List (String × Program × String) := [
    ("unused invalid body", changed program 6 (fun f => {f with body := [.action (.drop 99)]}), "E_RESOURCE_NAME"),
    ("unused recursion", changed program 6 (fun f => {f with body := [.call 6 [] []]}), "E_RESOURCE_RECURSION"),
    ("missing callee", changed program 6 (fun f => {f with body := [.call 999 [] []]}), "E_RESOURCE_FUNCTION"),
    ("caller capture", changed program 2 (fun f => {f with body := [.action (.drop 10)]}), "E_RESOURCE_NAME"),
    ("parameter shadow", changed program 2 (fun f => {f with body := [.action (.allocate 0 .f64 8)]}), "E_RESOURCE_NAME"),
    ("read parameter writes", changed program 2 (fun f => {f with body := [.action (.fill 0 value)]}), "E_RESOURCE_ACCESS"),
    ("write parameter reads", changed program 2 (fun f => {f with body := [.action (.expect 1 0 0 value)]}), "E_RESOURCE_ACCESS"),
    ("missing initialized-output guarantee", changed program 2 (fun f => {f with body := []}), "E_RESOURCE_INIT"),
    ("partial initialized-output guarantee", changed program 2 (fun f => {f with body := [.action (.store 1 0 0 value)]}), "E_RESOURCE_INIT"),
    ("early parameter release", changed program 2 (fun f => {f with body := [.action (.copy 0 1), .action (.release 0)]}), "E_RESOURCE_LOAN"),
    ("local child escape", changed program 3 (fun f => {f with body := [.action (.borrow 9 (.loan 0) ⟨0,1,1,1,false⟩ .read)]}), "E_RESOURCE_LOAN"),
    ("borrowed result escape", changed program 4 (fun f => {f with results := [(0, .owned owned)]}), "E_RESOURCE_TYPE"),
    ("unreturned owner", changed program 6 (fun f => {f with body := [.action (.allocate 0 .f64 8)]}), "E_RESOURCE_ESCAPE"),
    ("owner result with live loan", changed program 1 (fun f => {f with body := f.body.take 3}), "E_RESOURCE_ESCAPE"),
    ("duplicated owned result", changed program 1 (fun f => {f with results := f.results ++ f.results}), "E_RESOURCE_TYPE"),
    ("uninitialized padding in result contract", changed program 1 (fun f =>
      {f with results := [(0, .owned ⟨.f64,8,[⟨0,8,1,8,false⟩]⟩)]}), "E_RESOURCE_TYPE"),
    ("wrong result arity", changed program 0 (fun f => {f with body := [.call 1 [] []]}), "E_RESOURCE_ARITY"),
    ("wrong argument arity", changed program 0 (fun f => {f with body := [.call 5 [] [10]]}), "E_RESOURCE_ARITY"),
    ("moved caller owner is unusable", changed program 0 (fun f =>
      {f with body := [.call 1 [] [10], .call 5 [10] [30], .action (.drop 10), .action (.drop 30)]}), "E_RESOURCE_MOVE"),
    ("returned binder shadows caller", changed program 0 (fun f =>
      {f with body := [.call 1 [] [10], .call 5 [10] [10], .action (.drop 10)]}), "E_RESOURCE_NAME"),
    ("call arguments do not imply disjointness", changed program 0 (fun f =>
      {f with body := [.call 1 [] [10], .action (.borrow 11 (.owner 10) ⟨8,2,2,4,false⟩ .readWrite),
        .call 2 [11,11] [], .action (.release 11), .action (.drop 10)]}), "E_RESOURCE_ALIAS"),
    ("both branch arms checked", changed program 6 (fun f =>
      {f with body := [.branch false [.action (.drop 99)] []]}), "E_RESOURCE_NAME"),
    -- The synthetic contiguous probe accepts this child, but the actual shifted,
    -- padded caller view does not. Real-call reconstruction must reject it.
    ("probe layout cannot authorize a caller", changed program 2 (fun f =>
      {f with body := [.action (.borrow 9 (.loan 0) full .read), .action (.release 9), .action (.copy 0 1)]}), "E_RESOURCE_REGION")]
  for (name, input, expected) in cases do checkError name input expected
  let duplicate : Function := ⟨7, [.owned 0 owned, .owned 1 owned], [],
    [.action (.drop 0), .action (.drop 1)]⟩
  let duplicateCall := changed {program with functions := duplicate :: program.functions} 0 fun f =>
    {f with body := [.call 1 [] [10], .call 7 [10,10] []]}
  checkError "one owner cannot be consumed twice" duplicateCall "E_RESOURCE_TYPE"
  let badShape := changed program 0 fun f => {f with body := [.call 1 [] [10],
    .action (.borrow 11 (.owner 10) ⟨8,1,1,1,false⟩ .read), .call 4 [11,11] [],
    .action (.release 11), .action (.drop 10)]}
  checkError "actual view shape must match" badShape "E_RESOURCE_TYPE"
  let explosion : Program := ⟨(List.range 16).map (fun id =>
    ⟨id, [], [], if id == 0 then [] else [.call (id-1) [] [], .call (id-1) [] []]⟩), 15⟩
  checkError "exponential call DAG has a global budget" explosion "E_RESOURCE_LIMIT"
  let injected := json.setObjVal! "checked" (Lean.toJson true)
  if (Wire.check injected).isOk then throw (IO.userError "forged function certificate accepted")
  IO.println s!"resource functions: shared Rust fixture, all-body probes, native expansion and {cases.length+4} negative cases passed"

end VastitasKernel.Storage.Functions.Regression
