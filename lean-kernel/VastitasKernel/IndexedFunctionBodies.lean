import VastitasKernel.FiniteFunctionCall

namespace VastitasKernel.Indexed.FunctionSource.Compiler

/-- Classify only canonical arithmetic in contextual literal trees. A
local function called `sub` (or a Fn parameter shadowing a use) is an
ordinary call. Qualified and imported operators have the same literal rules
as their glyphs, including inside a comparison or branch. -/
private abbrev OperatorLookup := Source.Path → M (Option String)

private def literalLike (lookup : OperatorLookup) : Expr → M Bool
  | .integer .. => pure true
  | .unary "-" value _ => literalLike lookup value
  | .binary op left right _ => do
    unless ["+", "-", "*"].contains op do return false
    unless ← literalLike lookup left do return false
    literalLike lookup right
  | .call path [a] _ => do
    unless ← literalLike lookup a do return false
    return (← lookup path) == some "neg"
  | .call path [a,b] _ => do
    unless ← literalLike lookup a do return false
    unless ← literalLike lookup b do return false
    return (← lookup path).any (["add","sub","mul"].contains ·)
  | _ => pure false

private def literalOperator (input : Input) (scope : Namespace.Scope) (ctx : Context)
    (path : Source.Path) : M (Option String) := do
  if let [name] := path.path then
    if let some binding := ctx.find? (·.source.name == name) then
      return binding.family.bind fun ref =>
        if ref.target.owner.scope == Namespace.operatorScope then some ref.target.owner.name else none
    if !Namespace.operatorName name && !(Namespace.moduleLookupAt input.body.index scope).any (·.imports.contains name) then return none
  -- Price both classification and the actual call using the same cache and
  -- program-wide work limit. Leave missing/invalid paths to call diagnostics.
  body do
    let before ← get
    let session := before.queries.getD {index := input.body.index}
    match session.query scope path.path path.span with
    | .error d => if d.code == "E_LIMIT" then throw d else pure none
    | .ok (target, after) =>
      set {before with queries := some after}
      return if target.owner.scope == Namespace.operatorScope && target.kind == .generic then some target.owner.name else none

private def inferFromRight (lookup : OperatorLookup) (left right : Expr) (hint : Option Core.DataType) : M Bool := do
  if hint.isSome then return false
  unless ← literalLike lookup left do return false
  return !(← literalLike lookup right)

private def blockLiteralLike (lookup : OperatorLookup) : Block → M Bool
  | .mk statements value _ => literalLike (fun p => do
      if let [name] := p.path then
        for statement in statements do
          match statement with
          | .letE n .. => if name == n then return none
          | .unpack _ witness fields _ => if name == witness || fields.contains name then return none
      lookup p) value

private def inferFromElse (lookup : OperatorLookup) (yes no : Block) (expected : Option Core.DataType) : M Bool := do
  if expected.isSome then return false
  unless ← blockLiteralLike lookup yes do return false
  return !(← blockLiteralLike lookup no)

/-- Every argument is evaluated once and in source order, including erased Fn
arguments. This also keeps nominal allocation nodes out of duplicate uses. -/
def freeze (values : List Value) : M (List (Nat × Core.Term) × List Value) := do
  let mut bindings := []
  let mut frozen := []
  for value in values do
    let symbol ← fresh
    bindings := bindings ++ [(symbol, value.term)]
    frozen := frozen ++ [{ value with term := .variable symbol value.term.result }]
  return (bindings, frozen)

def wrap (bindings : List (Nat × Core.Term)) (value : Value) : Value :=
  { value with term := bindings.foldr (fun (symbol, term) rest => .letE symbol term rest) value.term }

/-- Select an associated slot through its visible category owner. A direct path
must resolve to a table. A composability-restricted table is only callable via
the projection, which also supplies the nominal category of the Hom fibers. -/
private def lookupTable (input : Input) (scope : Namespace.Scope) (path : Source.Path) :
    M (DeclId × Option DeclId) := do
  let index := input.body.index
  let env := input.body.declarations.indexed
  let record (p : Source.Path) := do
    let hit ← body (Source.Bodies.lookupPath index scope p)
    modify fun state => { state with body := {state.body with references := ⟨scope, p, hit⟩ :: state.body.references} }
    return hit
  if let field :: head :: rest := path.path.reverse then
    let base : Source.Path := ⟨(head :: rest).reverse, path.span⟩
    let authority? := do
      if let some (view, target, cat) := Source.projectedMonadCategory? index scope env base then
        return (view, target, cat)
      let target ← (Namespace.resolve index scope base.path base.span).toOption
      return (base, target, target.owner)
    if let some (visible, target, owner) := authority? then
      if target.kind == .indexedDeclaration then
        match Indexed.lookup env owner with
        | some (.finiteCategory _ graph) =>
          let _ ← record visible
          match field with
          | "source" => return (graph.src, none)
          | "target" => return (graph.dst, none)
          | "identities" => return (graph.ids, none)
          | "composition" => return (graph.comp, some owner)
          | _ => error path.span "E_CATEGORY" "expected a finite category table projection"
        | some (.finiteMonad ..) | some (.finiteKleisli ..) =>
          let _ ← record visible
          let some monad := FiniteSort.monadOwner? env owner
            | error path.span "E_MONAD" "expected the selected finite Monad"
          let some (.finiteMonad _ m) := Indexed.lookup env monad
            | error path.span "E_MONAD" "expected a finite Monad instance"
          if field == "arrows" then
            let some (.finiteFunctor _ maps) := Indexed.lookup env m.functor
              | error path.span "E_MONAD" "expected the selected finite endofunctor"
            return (maps.arrows, some monad)
          let transformation ← match field with
            | "unit" => pure m.unit
            | "multiplication" => pure m.multiplication
            | _ => error path.span "E_MONAD" "expected the unit or multiplication projection"
          let some (.finiteNatTrans _ n) := Indexed.lookup env transformation
            | error path.span "E_MONAD" "expected a finite natural transformation"
          return (n.components, none)
        | some (.finiteIso _ i) =>
          let _ ← record base
          match field with
          | "forward" => return (i.forward, some owner)
          | "inverse" => return (i.inverse, some owner)
          | "source" => return (i.source, none)
          | "target" => return (i.target, none)
          | _ => error path.span "E_ISO" "expected a finite isomorphism projection"
        | some (.finiteNatTrans _ n) =>
          let _ ← record base
          unless field == "components" do error path.span "E_NAT_TRANS" "expected the components projection"
          return (n.components, none)
        | some (.finiteFunctor _ maps) =>
          let _ ← record base
          match field with
          | "objects" => return (maps.objects, none)
          | "arrows" => return (maps.arrows, none)
          | _ => error path.span "E_FUNCTOR" "expected a finite functor map projection"
        | _ => pure ()
  let hit ← record path
  unless hit.kind == .indexedDeclaration do error path.span "E_FINITE_TABLE" "expected a total finite table"
  return (hit.owner, none)

private def finiteCall (input : Input) (scope : Namespace.Scope) (path : Source.Path)
    (args : List Expr) (visit : Expr → M Value) : M Value := do
  let (table, category) ← lookupTable input scope path
  let env := input.body.declarations.indexed
  let arity ← match category, Indexed.lookup env table with
    | none, some (.finiteTable inputs _ _) => pure inputs.length
    | some _, some (.composableTable ..) => pure 2
    | some _, some (.finiteTable [] _ _) => pure 0
    | some _, some (.finiteTable [_] _ _) => pure 1
    | _, _ => error path.span "E_FINITE_TABLE" "expected a total finite table or a checked instance projection"
  unless args.length == arity do error path.span "E_ARITY" "wrong number of finite table arguments"
  let values ← args.mapM fun arg => do return Value.mk (← data (← visit arg) arg.span) none none
  let inputs ← (values.zip args).mapM fun (v, arg) => do
    let .finite sort := v.term.result.type | error arg.span "E_TYPE" "table argument requires a nominal finite value"
    return sort
  let some (output, _) := FiniteLookup.signature env table category inputs
    | error path.span "E_TYPE" "table arguments do not match the declared carriers or Hom endpoints"
  let (bindings, _) ← freeze values
  return wrap bindings {term := .finiteLookup ⟨table, category, inputs, output⟩ (bindings.map Prod.fst)}

private def producerType (value : Value) (span : Span) : M Core.DataType := do
  if let some selected := value.target then
    let .function .nil (.data ty@(.finite (.hom ..))) := selected.signature
      | error span "E_TYPE" "finite forwarding requires a nullary Fn returning the selected Hom"
    return ty
  return (← data value span).result.type

private def forceProducer (input : Input) (value : Value) (span : Span) : M Value := do
  let some selected := value.target | return value
  recordTarget selected selected.signature
  match selected.name with
  | .concrete id => emitCall input id [] [] [] span selected.selected
  | .probe _ =>
    unless (← get).audit do error span "E_INTERNAL_FUNCTION" "executable finite forwarding contains a probe"
    return ⟨← probeVariable input (← producerType value span) span, none, none⟩

private def invokeFinite (input : Input) (scope : Namespace.Scope) (path : Source.Path)
    (target : Namespace.Target) (template : FiniteTemplate) (indices : Option (List Source.Path))
    (args : List Expr) (visit : Expr → M Value) : M Value := do
  unless target.kind == .function do error path.span "E_TYPE" "expected a named finite function"
  let work ← result (WorkBudget.charge (← get).elaborationWork
    (1 + template.binders.length + template.inputs.length) path.span)
  modify fun s => {s with elaborationWork := work}
  let values ← args.mapM visit
  let targets := values.map (·.target)
  let mask := targets.map Option.isSome
  let method ← if mask.contains true then do
    let some method := input.forwardMethods[(target.owner,mask)]?
      | error path.span "E_TYPE" "this finite family has no callable method for these arguments"
    pure (some method)
  else pure none
  let types ← (values.zip args).mapM fun (v,a) => producerType v a.span
  let key ← finiteCallKey input scope template indices types path.span
  -- Evaluate *all* call-site expressions first, including values erased to
  -- Unit. Inside the checked forwarder, invoke each producer in body order.
  let (outer,values) ← if method.isSome then do
    let (bindings,frozen) ← freeze values
    let forced ← (frozen.zip args).mapM fun (v,a) => forceProducer input v a.span
    pure (bindings,forced)
  else pure ([],values)
  let site := (target.owner,key)
  if input.discovering then
    -- Provisional calls use the checked template's concrete signature. Keeping
    -- a call here gives nested callers the same let cost as final lowering.
    let id ← match (← get).discoveryIds[site]? with
      | some id => pure id
      | none => do
        let n := (← get).finiteCalls.size
        if n ≥ Limits.specializations then error path.span "E_LIMIT" "finite fn specialization limit exceeded"
        let id := input.prepared.size + Limits.specializations + n
        modify fun s => {s with discoveryIds := s.discoveryIds.insert site id, finiteCalls := s.finiteCalls.push site}
        pure id
    let (bindings,frozen) ← freeze values
    let some (params,output) := template.signature key (bindings.map Prod.fst) input.body.declarations.indexed
      | error path.span "E_TYPE" "finite key has no concrete signature"
    unless params.map (·.result) == frozen.map (·.term.result) do
      error path.span "E_TYPE" "finite arguments do not realize the selected signature"
    return wrap outer (wrap bindings {term := .call id (frozen.map (·.term)) [] ⟨output,none⟩})
  let some id := input.finiteInstances[site]? | error path.span "E_INTERNAL_FUNCTION" "unprepared finite function instance"
  modify fun s => { s with calls := ⟨scope,path,target,id⟩ :: s.calls }
  if let some method := method then
    let some caller := (← get).active.head? | error path.span "E_INTERNAL_FUNCTION" "missing finite call origin"
    let some (first,_) := outer.head? | error path.span "E_INTERNAL_FUNCTION" "missing finite forwarding arguments"
    modify fun s => {s with
      calls := ⟨target.owner.scope,method.callee,target,id⟩ :: s.calls
      forwardUses := ⟨caller,target.owner,key,id,method.span,path.span,first,targets⟩ :: s.forwardUses}
  return wrap outer (← emitCall input id [] values [] path.span)

private def probeResult (input : Input) (type : Signature) (span : Span) : M Value := do
  match type with
  | .function .. => return ⟨.unit, some (← probe type), none⟩
  | .data (.pure .nat) => return ⟨.natural 0, none, none⟩
  | .data (.pure .int) => return ⟨.integer 0, none, none⟩
  | .data (.pure .bool) => return ⟨.boolean false, none, none⟩
  | .data (.pure .unit) => return ⟨.unit, none, none⟩
  | .data ty@(.finite (.hom ..)) => return ⟨← probeVariable input ty span, none, none⟩
  | _ => error span "E_INTERNAL_FUNCTION" "invalid signature probe result"

/-- Exact scalar methods are closed, pure and keyed by the operands. The
shared elaborator is used by the glyph, its qualified name and import aliases.
Only division embeds a Nat operand when a pair has mixed integer types. -/
private def exactOperator (lookup : OperatorLookup) (op : String) (args : List Expr) (span : Span)
    (expected : Option Core.DataType) (visit : Expr → Option Core.DataType → M Value) : M Value := do
  if op == "neg" then
    let [arg] := args | error span "E_ARITY" "std::operator::neg expects one argument"
    let v ← data (← visit arg (some (.pure .int))) span
    return ⟨.unary .neg v ⟨.pure .int, none⟩, none, none⟩
  let [a, b] := args | error span "E_ARITY" s!"std::operator::{op} expects two arguments"
  let operator ← match op with
    | "add" => pure BinaryOp.add | "sub" => pure .sub | "mul" => pure .mul | "div" => pure .div
    | _ => error span "E_OPERATOR" "unknown exact operator family"
  let hint := expected.filter Source.Bodies.integerType
  let (l, r) ← if operator == .div then do
    -- Key the method on independently elaborated operands, without using
    -- the caller's return type to choose Nat division versus Int.ediv.
    let l ← data (← visit a none) span
    let r ← data (← visit b none) span
    pure (l, r)
  else if ← inferFromRight lookup a b hint then do
    let r ← data (← visit b none) span
    let l ← data (← visit a (some r.result.type)) span
    pure (l, r)
  else do
    let l ← data (← visit a hint) span
    let r ← data (← visit b (some l.result.type)) span
    pure (l, r)
  let output := if operator == .div && r.result.type == .pure .int then .pure .int else l.result.type
  unless Core.Typing.BinaryTyping operator l.result.type r.result.type output do
    error span "E_OPERATOR" (Core.Typing.operandMessage operator l.result.type r.result.type)
  return ⟨.binary operator l r ⟨output, none⟩, none, none⟩

mutual
  def expression : Nat → Input → Namespace.Scope → Context → Expr → Option Core.DataType → M Value
    | 0, _, _, _, expr, _ => checkingBudgetExceeded expr.span
    | fuel + 1, input, scope, ctx, expr, expected => do
      let span := expr.span
      let value ← match expr with
      | .integer value _ => do
          let term ← body (do
            let term ← Source.Bodies.integerLiteral value span expected
            Source.Bodies.expect input.body expected term span)
          pure ⟨term, none, none⟩
      | .boolean value _ => pure ⟨.boolean value, none, none⟩
      | .unit _ => pure ⟨.unit, none, none⟩
      | .variable name _ => do
          if let some binding := ctx.find? (fun binding => binding.source.name == name) then
            checkOperatorOwner ⟨[name], span⟩ binding.operatorOwner?
            if binding.target.isSome || binding.family.isSome then pure ⟨.unit, binding.target, binding.family⟩
            else pure ⟨.variable binding.source.parameter.symbol binding.source.parameter.result, none, none⟩
          else resolveValue input scope ⟨[name], span⟩
      | .functionValue path _ => resolveValue input scope path
      | .lifted id _ => do
          let definition ← prepared input id span
          unless definition.definition.isLambda do error span "E_INTERNAL_FUNCTION" "lifted reference does not name a lambda"
          pure ⟨.unit, some (← concrete input id span), none⟩
      | .lambda .. => error span "E_INTERNAL_FUNCTION" "lambda was not lifted"
      | .finiteLookup table args _ => finiteCall input scope table args (fun arg => expression fuel input scope ctx arg none)
      | .finiteCall path indices args _ => do
          if let [name] := path.path then
            if ctx.any (·.source.name == name) then error path.span "E_TYPE" "local values take no finite static indices"
          let target ← body (Source.Bodies.lookupPath input.body.index scope path)
          checkOperatorOwner path target.owner
          let some (_, template) := input.templates[target.owner]? | error path.span "E_TYPE" "function has no static finite binders"
          invokeFinite input scope path target template (some indices) args (fun arg => expression fuel input scope ctx arg none)
      | .call path arguments _ => call fuel input scope ctx path arguments span expected
      | .invoke callee arguments _ => do
          let callee ← expression fuel input scope ctx callee none
          let value ← match callee.family with
            | some ref => invokeFamily fuel input scope ctx ref arguments span expected
            | none => do invokeTarget fuel input scope ctx (← target callee span) arguments span
          let symbol ← fresh
          pure (wrap [(symbol, callee.term)] value)
      | .unary "-" operand _ => exactOperator (literalOperator input scope ctx) "neg" [operand] span expected (expression fuel input scope ctx)
      | .unary "!" operand _ => do
          let value ← data (← expression fuel input scope ctx operand (some (.pure .bool))) span
          pure ⟨.unary .not value ⟨.pure .bool, none⟩, none, none⟩
      | .unary _ _ _ => error span "E_OPERATOR" "unsupported unary operator"
      | .binary "+" l r _ => exactOperator (literalOperator input scope ctx) "add" [l,r] span expected (expression fuel input scope ctx)
      | .binary "-" l r _ => exactOperator (literalOperator input scope ctx) "sub" [l,r] span expected (expression fuel input scope ctx)
      | .binary "*" l r _ => exactOperator (literalOperator input scope ctx) "mul" [l,r] span expected (expression fuel input scope ctx)
      | .binary "/" l r _ => exactOperator (literalOperator input scope ctx) "div" [l,r] span expected (expression fuel input scope ctx)
      | .binary operator left right _ => do
          let some operator := BinaryOp.ofString? operator | error span "E_OPERATOR" "unsupported binary operator"
          let boolean := operator == .and || operator == .or
          let hint := if boolean then some (Core.DataType.pure .bool) else none
          let (left, right) ← if ← inferFromRight (literalOperator input scope ctx) left right hint then do
            let right ← data (← expression fuel input scope ctx right none) span
            let left ← data (← expression fuel input scope ctx left (some right.result.type)) span
            pure (left, right)
          else do
            let left ← data (← expression fuel input scope ctx left hint) span
            let right ← data (← expression fuel input scope ctx right (some left.result.type)) span
            pure (left, right)
          let output := Core.DataType.pure .bool
          unless Core.Typing.BinaryTyping operator left.result.type right.result.type output do
            error span "E_OPERATOR" (Core.Typing.operandMessage operator left.result.type right.result.type)
          pure ⟨.binary operator left right ⟨output, none⟩, none, none⟩
      | .branch condition yes no _ => do
          let condition ← data (← expression fuel input scope ctx condition (some (.pure .bool))) span
          let (yes, no) ← if ← inferFromElse (literalOperator input scope ctx) yes no expected then do
            let no ← block fuel input scope ctx no none
            let yes ← block fuel input scope ctx yes (if no.target.isSome || no.family.isSome then none else some no.term.result.type)
            pure (yes, no)
          else do
            let yes ← block fuel input scope ctx yes expected
            let no ← block fuel input scope ctx no (if yes.target.isSome || yes.family.isSome then none else expected.or (some yes.term.result.type))
            pure (yes, no)
          let family ← match yes.family, no.family with
            | none, none => pure none
            | some left, some right => do
                unless left.target == right.target do
                  error span "E_STATIC_CALL" "function-valued branches must resolve to the same static family"
                pure (some left)
            | _, _ => error span "E_TYPE" "branches require the same static function family"
          let selected ← match yes.target, no.target with
            | none, none => pure none
            | some a, some b => do
                sameSignature a.signature b.signature span
                if a.name == b.name then pure (some a)
                else if (← get).audit && (match a.name, b.name with | .probe _, _ | _, .probe _ => true | _, _ => false) then
                  some <$> probe a.signature
                else error span "E_STATIC_CALL" "function-valued branches must resolve to the same static target"
            | _, _ => error span "E_TYPE" "branches must both return data or the same Fn type"
          let yes := match expected with | some type => Core.Term.ascribe type yes.term | none => yes.term
          let no := match expected with | some type => Core.Term.ascribe type no.term | none => no.term
          unless yes.result.type == no.result.type do error span "E_TYPE" "branches require the same data type"
          let reference ← match yes.result.type with
            | .object type =>
              if yes.result.reference == no.result.reference then pure yes.result.reference
              else some <$> body (Source.Bodies.freshObject type span "if merge of distinct objects")
            | _ => pure none
          pure ⟨.branch condition yes no ⟨yes.result.type, reference⟩, selected, family⟩
      | .block value _ => block fuel input scope ctx value expected
      | .pack annotation witness fields _ => do
          let (application, witness) ← match annotation with
            | .inferredPackage => do
              let witness ← data (← expression fuel input scope ctx witness none) span
              pure (← body (Source.Bodies.legacyPackage input.body witness span), witness)
            | _ => do
              let .package application ← body (Source.Bodies.type input.body scope ctx.data annotation span)
                | error span "E_TYPE" "pack annotation must name an existential package"
              let some shape := input.body.declarations.package? application | error span "E_TYPE" "unknown package case"
              pure (application, ← data (← expression fuel input scope ctx witness (some (.object shape.witnessType))) span)
          let fields ← fields.mapM fun field => do data (← expression fuel input scope ctx field none) span
          unless Core.Typing.PackageTyping input.body.declarations application witness.result (fields.map Core.Term.result) do
            body (Source.Bodies.endpointFailure input.body (witness.result :: fields.map Core.Term.result) span
              "package fields do not match the exact witness and ordered field contract")
          pure ⟨.pack application witness fields, none, none⟩
      expect input expected value span

  def call : Nat → Input → Namespace.Scope → Context → Source.Path → List Expr → Span → Option Core.DataType → M Value
    | 0, _, _, _, _, _, span, _ => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, path, arguments, span, expected => do
      if path.path == ["int"] then
        let [argument] := arguments | error span "E_ARITY" s!"int expects 1 argument, found {arguments.length}"
        return ⟨.natToInt (← data (← expression fuel input scope ctx argument (some (.pure .nat))) span), none, none⟩
      if path.path == ["pair"] then
        let [first, second] := arguments | error span "E_ARITY" "pair expects two arguments"
        let first ← data (← expression fuel input scope ctx first none) span
        let second ← data (← expression fuel input scope ctx second none) span
        let element ← match first.result.type, second.result.type with
          | .pure .nat, .pure .nat => pure PairElem.nat
          | .pure .int, .pure .int => pure PairElem.int
          | _, _ => error span "E_TYPE" "pair operands must independently infer the same Nat or Int type"
        return ⟨.pair element first second, none, none⟩
      if path.path == ["pair_first"] || path.path == ["pair_second"] then
        let [argument] := arguments | error span "E_ARITY" "pair projection expects one argument"
        let value ← data (← expression fuel input scope ctx argument none) span
        let .pure (.pair element) := value.result.type | error span "E_TYPE" "pair projection requires a homogeneous Pair"
        return ⟨.project element (path.path == ["pair_first"]) value, none, none⟩
      if let [name] := path.path then
        if let some binding := ctx.find? (fun binding => binding.source.name == name) then
          checkOperatorOwner path binding.operatorOwner?
          if let some ref := binding.family then return ← invokeFamily fuel input scope ctx ref arguments span expected
          let some selected := binding.target | error span "E_TYPE" "a data value is not callable"
          return ← invokeTarget fuel input scope ctx selected arguments span
      if Source.Bodies.legacyFallback input.body scope path then
        let name := path.path.head!
        let (base, arguments) ← if name == "Affine" || name == "Base" then do
          let .variable marker _ :: rest := arguments | error span "E_RING" "Affine/Base requires an explicit coefficient marker"
          pure (some (← body (Source.Bodies.legacyMarker marker span)), rest)
        else pure (none, arguments)
        let hint := if name == "Affine" then some (Core.DataType.pure .nat) else none
        let values ← arguments.mapM fun argument => do data (← expression fuel input scope ctx argument hint) span
        return ⟨← body (Source.Bodies.emitLegacy input.body ctx.data name base values span), none, none⟩
      let resolved ← body (Source.Bodies.lookupPath input.body.index scope path fun diagnostic =>
        Source.Bodies.retiredCall path <|
        if path.path == ["nat_to_int"] && diagnostic.code == "E_NAME" then
          { diagnostic with notes := diagnostic.notes ++ [
            { span := path.span, message := "help: nat_to_int is defined by the arithmetic standard library; include and import that library, or use the builtin conversion int(...)" }] }
        else diagnostic)
      checkOperatorOwner path resolved.owner
      if let some (_, template) := input.templates[resolved.owner]? then
        return ← invokeFinite input scope path resolved template none arguments (fun arg => expression fuel input scope ctx arg none)
      if resolved.owner.scope == Namespace.operatorScope && resolved.kind == .generic then
        return ← exactOperator (literalOperator input scope ctx) resolved.owner.name arguments span expected (expression fuel input scope ctx)
      if resolved.kind == .generic then
        return ← invokeFamily fuel input scope ctx (← familyRef scope path resolved) arguments span expected
      if resolved.kind == .indexedDeclaration then
        let some binding := input.body.declarations.primitive? resolved.owner | error span "E_TYPE" "declaration is not a primitive"
        let arity := binding.arity input.body.declarations.indexed
        unless arguments.length == arity do error span "E_ARITY" "wrong primitive argument count"
        let values ← arguments.zipIdx.mapM fun (argument, position) => do
          data (← expression fuel input scope ctx argument (binding.argumentHint position)) span
        modify fun state => { state with body := { state.body with references := ⟨scope, path, resolved⟩ :: state.body.references } }
        return ⟨← body (Source.Bodies.emitPrimitive input.body ctx.data resolved.owner values span), none, none⟩
      -- Charge the named-call lookup separately from path classification, as
      -- the program-wide namespace work contract requires.
      let named ← body (Source.Bodies.lookupPath input.body.index scope path)
      let id ← resolveOrdinary input scope path named
      invokeDefinition fuel input scope ctx id arguments span none

  def invokeFamily : Nat → Input → Namespace.Scope → Context → FamilyRef → List Expr → Span → Option Core.DataType → M Value
    | 0, _, _, _, _, _, span, _ => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, ref, arguments, span, expected => do
      let some family := input.dispatch.families[ref.target.owner]?
        | error span "E_STAGE" "function has no checked finite dispatch environment"
      unless arguments.length == family.raw.params.length do error span "E_ARITY" "wrong generic argument count"
      let values ← if ref.target.owner.scope == Namespace.operatorScope then do
        let op ← exactOperator (literalOperator input scope ctx) ref.target.owner.name arguments span expected
          (expression fuel input scope ctx)
        match op.term with
        | .unary _ a _ => pure [Value.mk a none none]
        | .binary _ a b _ => pure [Value.mk a none none, Value.mk b none none]
        | _ => error span "E_INTERNAL_FUNCTION" "invalid exact operator application"
      else arguments.mapM fun argument => expression fuel input scope ctx argument none
      let key ← values.mapM fun value => do
        match (← data value span).result.type with
        | .pure .nat => pure 0 | .pure .int => pure 1
        | .pure .bool => pure 2 | .pure .unit => pure 3
        | _ => error span "E_TYPE" "dispatch keys require Nat, Int, Bool or Unit"
      let selected ← selectFamily input ref key span
      emitCall input selected.definition [] values [] span (some selected)

  def invokeDefinition : Nat → Input → Namespace.Scope → Context → Nat → List Expr → Span → Option DispatchSelection → M Value
    | 0, _, _, _, _, _, span, _ => error span "E_LIMIT"
        s!"too many function arguments for the remaining checking budget of {Limits.bodyChecking} units along one checking path"
    | fuel + 1, input, scope, ctx, id, arguments, span, selection => do
      let definition ← prepared input id span
      let parameters := definition.paramTypes.zip definition.context
      unless parameters.length == arguments.length do error span "E_ARITY" "wrong function argument count"
      let (values, targets, substitution) ← argumentsFor fuel input scope ctx parameters arguments [] span
      emitCall input id targets values substitution span selection

  def argumentsFor : Nat → Input → Namespace.Scope → Context → List (Signature × Source.Binding) → List Expr →
      List (ObjectRef × ObjectRef) → Span → M (List Value × List Target × List (ObjectRef × ObjectRef))
    | 0, _, _, _, _, _, _, span => checkingBudgetExceeded span
    | _ + 1, _, _, _, [], [], substitution, _ => pure ([], [], substitution)
    | fuel + 1, input, scope, ctx, (parameter, formal) :: parameters, argument :: arguments, substitution, span => do
        let expected := (Signature.dataHint parameter).map (·.rename substitution)
        let value ← expression fuel input scope ctx argument expected
        let value ← coerceAnnotation input parameter value span
        let selected ← match parameter with
          | .data _ => pure []
          | .function .. => do
              let selected ← target value span
              recordTarget selected parameter
              pure [selected]
        let substitution ← match formal.parameter.result.reference, value.term.result.reference with
          | none, _ => pure substitution
          | some formal, some actual => pure ((formal, actual) :: substitution)
          | _, _ => error span "E_TYPE" "dependent object argument has no nominal reference"
        let (values, targets, final) ← argumentsFor fuel input scope ctx parameters arguments substitution span
        return (value :: values, selected ++ targets, final)
    | _, _, _, _, _, _, _, span => error span "E_ARITY" "wrong function argument count"

  def invokeTarget : Nat → Input → Namespace.Scope → Context → Target → List Expr → Span → M Value
    | 0, _, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, selected, arguments, span => do
      recordTarget selected selected.signature
      match selected.name with
      | .concrete id => invokeDefinition fuel input scope ctx id arguments span selected.selected
      | .probe _ => do
          unless (← get).audit do error span "E_INTERNAL_FUNCTION" "signature probe escaped into executable specialization"
          let .function parameters resultType := selected.signature | error span "E_TYPE" "invalid Fn target"
          unless parameters.toList.length == arguments.length do error span "E_ARITY" "wrong Fn argument count"
          let values ← (parameters.toList.zip arguments).mapM fun (parameter, argument) => do
            let raw ← expression fuel input scope ctx argument (Signature.dataHint parameter)
            let value ← if parameter.isFunction then do
              let value ← coerceAnnotation input parameter raw span
              let actual ← target value span
              sameSignature parameter actual.signature span
              recordTarget actual parameter
              pure value
            else pure raw
            return value
          let (bindings, _) ← freeze values
          return wrap bindings (← probeResult input resultType span)

  def block : Nat → Input → Namespace.Scope → Context → Block → Option Core.DataType → M Value
    | 0, _, _, _, .mk _ _ span, _ => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, .mk statements result span, expected => do
        let value ← statementsThen fuel input scope ctx statements result expected span
        body (Source.Bodies.checkEscape input.body ctx.data value.term.result.type span)
        return { value with term := .scope value.term }

  def statementsThen : Nat → Input → Namespace.Scope → Context → List Stmt → Expr → Option Core.DataType → Span → M Value
    | 0, _, _, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, [], result, expected, _ => expression fuel input scope ctx result expected
    | fuel + 1, input, scope, ctx, .letE name type value span :: rest, output, expected, blockSpan => do
        body (Source.Bodies.bindName input.body scope ctx.data name span)
        let resolved ← type.mapM fun t => body (resolveType input.body scope ctx.data t span)
        let hint := resolved.bind Signature.dataHint
        let value ← expression fuel input scope ctx value hint
        let value ← match resolved with | some t => coerceAnnotation input t value span | none => pure value
        let term := match hint with | some type => Core.Term.ascribe type value.term | none => value.term
        let symbol ← fresh
        if let some selected := value.target then
          let label := selected.signature.formatAt (Source.Diagnostics.typeLabel input.body.declarations input.body.geometry {}) Limits.typeNesting
          modify fun state => { state with functionLets := (symbol, label) :: state.functionLets }
        if let some ref := value.family then
          modify fun state => { state with functionLets := (symbol, s!"fn family {ref.target.owner.qualified}") :: state.functionLets }
        body (Source.Bodies.nameObject term.result.reference name)
        let inner := ctx ++ [⟨⟨name, ⟨symbol, term.result⟩, span⟩, value.target, value.family⟩]
        let value ← statementsThen fuel input scope inner rest output expected blockSpan
        return { value with term := .letE symbol term value.term }
    | fuel + 1, input, scope, ctx, .unpack value witness fields span :: rest, output, expected, blockSpan => do
        let value ← data (← expression fuel input scope ctx value none) span
        let .package application := value.result.type | error span "E_TYPE" "unpack requires an existential package"
        let some shape := input.body.declarations.package? application | error span "E_TYPE" "unknown package case"
        unless fields.length == shape.fields.length do error span "E_ARITY" "unpack field count does not match its declaration"
        body (Source.Bodies.bindName input.body scope ctx.data witness span)
        let symbol ← fresh
        let reference := ObjectRef.local shape.witnessType symbol
        body (Source.Bodies.rememberObject reference span "unpack" (some witness))
        let mut inner : Context := ctx ++ [⟨⟨witness, ⟨symbol, ⟨.object shape.witnessType, some reference⟩⟩, span⟩, none, none⟩]
        let mut symbols := []
        for (name, application) in fields.zip (shape.instantiate reference) do
          body (Source.Bodies.bindName input.body scope inner.data name span)
          let field ← fresh
          symbols := symbols ++ [field]
          inner := inner ++ [⟨⟨name, ⟨field, ⟨.indexed application, none⟩⟩, span⟩, none, none⟩]
        let valueBody ← statementsThen fuel input scope inner rest output expected blockSpan
        body (Source.Bodies.checkEscape input.body ctx.data valueBody.term.result.type span)
        return { valueBody with term := .unpack symbol symbols value valueBody.term }
end

end VastitasKernel.Indexed.FunctionSource.Compiler
