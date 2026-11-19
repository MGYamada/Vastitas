import VastitasKernel.IndexedFunctionState

namespace VastitasKernel.Indexed.FunctionSource.Compiler

private def unifyIndex (span : Span) (slots : Array (Option StaticIndex)) (i : Nat) (value : StaticIndex) :
    M (Array (Option StaticIndex)) := do
  let some previous := slots[i]? | error span "E_TYPE" "unknown finite binder slot"
  if let some expected := previous then
    unless expected == value do error span "E_TYPE" "inconsistent category or object index in finite call"
  return slots.setIfInBounds i (some value)

private def explicitKey (input : Input) (scope : Namespace.Scope) (template : FiniteTemplate)
    (paths : List Source.Path) (span : Span) : M (List StaticIndex) := do
  unless paths.length == template.binders.length do error span "E_ARITY" "wrong number of static indices"
  let env := input.body.declarations.indexed
  let named (p : Source.Path) := do
    let hit ← body (Source.Bodies.lookupPath input.body.index scope p)
    unless hit.kind == .indexedDeclaration do error p.span "E_TYPE" "expected a named finite model"
    modify fun s => {s with body := {s.body with references := ⟨scope,p,hit⟩ :: s.body.references}}
    return hit.owner
  let mut key : Array StaticIndex := #[]
  for (binder,path) in template.binders.zip paths do
    let value ← match binder with
      | .category _ => do
        if let some (base, _, category) := Source.projectedMonadCategory? input.body.index scope env path then
          let _ ← named base
          pure (.category category)
        else
          pure (.category (← named path))
      | .monad _ => do
        let visible ← named path
        let some owner := FiniteSort.monadOwner? env visible
          | error path.span "E_TYPE" "expected a named finite Monad or Kleisli view"
        pure (.monad owner)
      | .object c | .monadObject c => do
        let owner ← match binder, key[c]? with
          | .object _, some (.category id) => pure id
          | .monadObject _, some (.monad id) => do
            let some (.finiteMonad _ s) := lookup env id | error path.span "E_TYPE" "expected a named finite Monad"
            pure s.category
          | _, _ => error path.span "E_TYPE" "object index requires its earlier model"
        let some (_,g) := FiniteSort.selected env owner
          | error path.span "E_TYPE" "expected a finite category instance"
        let (tag,refs) ← result ((Source.homEndpoint input.body.index scope path input.body.declarations.indexed g).run [])
        for ref in refs do
          let hit ← body (Source.Bodies.lookupPath input.body.index ref.scope ref.path)
          unless hit == ref.target do error path.span "E_OWNER" "finite object index changed owner"
        modify fun s => {s with body := {s.body with references := refs ++ s.body.references}}
        pure (.object owner tag)
    key := key.push value
  return key.toList

/-- Only actual arguments supply inference constraints. Expected result types and
import order never choose an instance. Explicit indices are checked by the same equations. -/
def finiteCallKey (input : Input) (scope : Namespace.Scope) (template : FiniteTemplate)
    (explicit : Option (List Source.Path)) (types : List Core.DataType) (span : Span) : M (List StaticIndex) := do
  unless types.length == template.inputs.length do error span "E_ARITY" "wrong number of finite function arguments"
  let mut slots ← match explicit with
    | some paths => do pure (((← explicitKey input scope template paths span).map some).toArray)
    | none => pure (Array.replicate template.binders.length none)
  for (formal,type) in template.inputs.zip types do
    match formal, type with
    | .hom c x y, .finite (.hom owner source target) =>
      slots ← unifyIndex span slots c (.category owner)
      slots ← unifyIndex span slots x (.object owner source)
      slots ← unifyIndex span slots y (.object owner target)
    | .monadHom _ x y, .finite (.hom owner source target) =>
      -- A Hom identifies its category. Neither the Monad nor a preimage under
      -- its possibly noninjective T can be recovered from that fact.
      if let .slot i := x then slots ← unifyIndex span slots i (.object owner source)
      if let .slot i := y then slots ← unifyIndex span slots i (.object owner target)
    | .bool, .pure .bool => pure ()
    | _, _ => error span "E_TYPE" "argument does not match the finite function parameter"
  let some key := slots.toList.mapM id | error span "E_TYPE" "finite index cannot be inferred; supply explicit indices"
  let env := input.body.declarations.indexed
  unless template.validKey env key do error span "E_TYPE" "invalid category or Monad schema or object index"
  unless (template.inputs.mapM (·.realize key env)) == some types do
    error span "E_TYPE" "finite arguments do not realize the selected signature"
  return key

end VastitasKernel.Indexed.FunctionSource.Compiler
