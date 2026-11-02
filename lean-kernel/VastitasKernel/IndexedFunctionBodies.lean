import VastitasKernel.IndexedFunctionState

namespace VastitasKernel.Indexed.FunctionSource.Compiler

private def literalLike : Expr → Bool
  | .integer .. => true
  | .unary "-" value _ => literalLike value
  | .binary op left right _ => ["+", "-", "*"].contains op && literalLike left && literalLike right
  | _ => false

private def blockLiteralLike : Block → Bool
  | .mk _ result _ => literalLike result

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

private def probeResult (type : Surface.TypeExpr) (span : Span) : M Value := do
  match type with
  | .function .. => return ⟨.unit, some (← probe type)⟩
  | .data (.named "Nat") => return ⟨.natural 0, none⟩
  | .data (.named "Int") => return ⟨.integer 0, none⟩
  | .data (.named "Bool") => return ⟨.boolean false, none⟩
  | .data (.named "Unit") => return ⟨.unit, none⟩
  | _ => error span "E_INTERNAL_FUNCTION" "invalid signature probe result"

private def callableData (type : Surface.TypeExpr) (span : Span) : M (Option Core.DataType) :=
  match type with
  | .function .. => pure none
  | .data (.named "Nat") => pure (some (.pure .nat))
  | .data (.named "Int") => pure (some (.pure .int))
  | .data (.named "Bool") => pure (some (.pure .bool))
  | .data (.named "Unit") => pure (some (.pure .unit))
  | _ => error span "E_TYPE" "Fn arguments require scalar/recursive-Fn types"

mutual
  def expression : Nat → Input → Namespace.Scope → Context → Expr → Option Core.DataType → M Value
    | 0, _, _, _, expr, _ => checkingBudgetExceeded expr.span
    | fuel + 1, input, scope, ctx, expr, expected => do
      let span := expr.span
      let value ← match expr with
      | .integer value _ => do
          let term ← body (Source.Bodies.expression 1 input.body scope ctx.data (.integer value span) expected)
          pure ⟨term, none⟩
      | .boolean value _ => pure ⟨.boolean value, none⟩
      | .unit _ => pure ⟨.unit, none⟩
      | .variable name _ => do
          if let some binding := ctx.find? (fun binding => binding.source.name == name) then
            if let some target := binding.target then pure ⟨.unit, some target⟩
            else pure ⟨.variable binding.source.parameter.symbol binding.source.parameter.result, none⟩
          else pure ⟨.unit, some (← concrete input (← resolve input scope ⟨[name], span⟩) span)⟩
      | .functionValue path _ => pure ⟨.unit, some (← concrete input (← resolve input scope path) span)⟩
      | .lifted id _ => do
          let definition ← prepared input id span
          unless definition.definition.isLambda do error span "E_INTERNAL_FUNCTION" "lifted reference does not name a lambda"
          pure ⟨.unit, some (← concrete input id span)⟩
      | .lambda .. => error span "E_INTERNAL_FUNCTION" "lambda was not lifted"
      | .call path arguments _ => call fuel input scope ctx path arguments span
      | .invoke callee arguments _ => do
          let callee ← expression fuel input scope ctx callee none
          let selected ← target callee span
          let value ← invokeTarget fuel input scope ctx selected arguments span
          let symbol ← fresh
          pure (wrap [(symbol, callee.term)] value)
      | .unary operator operand _ => do
          let (operator, type) ← match operator with
            | "-" => pure (UnaryOp.neg, Core.DataType.pure .int)
            | "!" => pure (UnaryOp.not, Core.DataType.pure .bool)
            | _ => error span "E_OPERATOR" "unsupported unary operator"
          let value ← data (← expression fuel input scope ctx operand (some type)) span
          pure ⟨.unary operator value ⟨type, none⟩, none⟩
      | .binary operator left right _ => do
          let some operator := BinaryOp.ofString? operator | error span "E_OPERATOR" "unsupported binary operator"
          let arithmetic := [BinaryOp.add, .sub, .mul].contains operator
          let boolean := operator == .and || operator == .or
          let hint := if boolean then some (Core.DataType.pure .bool)
            else if arithmetic then expected.filter Source.Bodies.integerType else none
          let (left, right) ← if literalLike left && !literalLike right && hint.isNone then do
            let right ← data (← expression fuel input scope ctx right none) span
            let left ← data (← expression fuel input scope ctx left (some right.result.type)) span
            pure (left, right)
          else do
            let left ← data (← expression fuel input scope ctx left hint) span
            let right ← data (← expression fuel input scope ctx right (some left.result.type)) span
            pure (left, right)
          let output := if arithmetic then left.result.type else .pure .bool
          unless Core.Typing.BinaryTyping operator left.result.type right.result.type output do
            error span "E_OPERATOR" "operator requires compatible scalar operands"
          pure ⟨.binary operator left right ⟨output, none⟩, none⟩
      | .branch condition yes no _ => do
          let condition ← data (← expression fuel input scope ctx condition (some (.pure .bool))) span
          let (yes, no) ← if expected.isNone && blockLiteralLike yes && !blockLiteralLike no then do
            let no ← block fuel input scope ctx no none
            let yes ← block fuel input scope ctx yes (if no.target.isSome then none else some no.term.result.type)
            pure (yes, no)
          else do
            let yes ← block fuel input scope ctx yes expected
            let no ← block fuel input scope ctx no (if yes.target.isSome then none else expected.or (some yes.term.result.type))
            pure (yes, no)
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
          pure ⟨.branch condition yes no ⟨yes.result.type, reference⟩, selected⟩
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
          pure ⟨.pack application witness fields, none⟩
      expect input expected value span

  def call : Nat → Input → Namespace.Scope → Context → Source.Path → List Expr → Span → M Value
    | 0, _, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, path, arguments, span => do
      if path.path == ["int"] then
        let [argument] := arguments | error span "E_ARITY" s!"int expects 1 argument, found {arguments.length}"
        return ⟨.natToInt (← data (← expression fuel input scope ctx argument (some (.pure .nat))) span), none⟩
      if path.path == ["pair"] then
        let [first, second] := arguments | error span "E_ARITY" "pair expects two arguments"
        let first ← data (← expression fuel input scope ctx first none) span
        let second ← data (← expression fuel input scope ctx second none) span
        let element ← match first.result.type, second.result.type with
          | .pure .nat, .pure .nat => pure PairElem.nat
          | .pure .int, .pure .int => pure PairElem.int
          | _, _ => error span "E_TYPE" "pair operands must independently infer the same Nat or Int type"
        return ⟨.pair element first second, none⟩
      if path.path == ["pair_first"] || path.path == ["pair_second"] then
        let [argument] := arguments | error span "E_ARITY" "pair projection expects one argument"
        let value ← data (← expression fuel input scope ctx argument none) span
        let .pure (.pair element) := value.result.type | error span "E_TYPE" "pair projection requires a homogeneous Pair"
        return ⟨.project element (path.path == ["pair_first"]) value, none⟩
      if let [name] := path.path then
        if let some binding := ctx.find? (fun binding => binding.source.name == name) then
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
        return ⟨← body (Source.Bodies.emitLegacy input.body ctx.data name base values span), none⟩
      let resolved ← result ((Namespace.resolve input.body.index scope path.path path.span).mapError fun diagnostic =>
        if path.path == ["nat_to_int"] && diagnostic.code == "E_NAME" then
          { diagnostic with notes := diagnostic.notes ++ [
            { span := path.span, message := "help: nat_to_int is defined by the arithmetic standard library; include and import that library, or use the builtin conversion int(...)" }] }
        else diagnostic)
      if resolved.kind == .generic then
        let some family := input.dispatch.families[resolved.owner]?
          | error span "E_STAGE" "generic has no checked finite dispatch environment"
        unless arguments.length == family.raw.params.length do error span "E_ARITY" "wrong generic argument count"
        let values ← arguments.mapM fun argument => expression fuel input scope ctx argument none
        let key ← values.mapM fun value => do
          let term ← data value span
          match term.result.type with
          | .pure .nat => pure 0 | .pure .int => pure 1
          | .pure .bool => pure 2 | .pure .unit => pure 3
          | _ => error span "E_TYPE" "dispatch keys require Nat, Int, Bool or Unit"
        let selected ← result (((DispatchChecker.selectTarget family key span).run {}).map Prod.fst)
        let some definition := input.dispatch.definitions[(selected.method, key)]?
          | error span "E_INTERNAL_DISPATCH" "winner has no checked source specialization"
        modify fun state => { state with dispatchCalls :=
          ⟨scope, path, resolved, key, selected.method, definition⟩ :: state.dispatchCalls }
        return ← emitCall input definition [] values [] span
      if resolved.kind == .indexedDeclaration then
        let some binding := input.body.declarations.primitive? resolved.owner | error span "E_TYPE" "declaration is not a primitive"
        let arity := match binding with | .global _ => 0 | .compose _ | .apply .. => 2 | _ => 1
        unless arguments.length == arity do error span "E_ARITY" "wrong primitive argument count"
        let hint := match binding with | .descriptor _ => some (Core.DataType.pure .nat) | _ => none
        let values ← arguments.mapM fun argument => do data (← expression fuel input scope ctx argument hint) span
        modify fun state => { state with body := { state.body with references := ⟨scope, path, resolved⟩ :: state.body.references } }
        return ⟨← body (Source.Bodies.emitPrimitive input.body ctx.data resolved.owner values span), none⟩
      let id ← resolve input scope path
      invokeDefinition fuel input scope ctx id arguments span

  def invokeDefinition : Nat → Input → Namespace.Scope → Context → Nat → List Expr → Span → M Value
    | 0, _, _, _, _, _, span => error span "E_LIMIT"
        s!"too many function arguments for the remaining checking budget of {Limits.bodyChecking} units (statements, nesting, and call arguments)"
    | fuel + 1, input, scope, ctx, id, arguments, span => do
      let definition ← prepared input id span
      let parameters := definition.definition.function.params.zip definition.context
      unless parameters.length == arguments.length do error span "E_ARITY" "wrong function argument count"
      let (values, targets, substitution) ← argumentsFor fuel input scope ctx parameters arguments [] span
      emitCall input id targets values substitution span

  def argumentsFor : Nat → Input → Namespace.Scope → Context → List (Param × Source.Binding) → List Expr →
      List (ObjectRef × ObjectRef) → Span → M (List Value × List Target × List (ObjectRef × ObjectRef))
    | 0, _, _, _, _, _, _, span => checkingBudgetExceeded span
    | _ + 1, _, _, _, [], [], substitution, _ => pure ([], [], substitution)
    | fuel + 1, input, scope, ctx, (parameter, formal) :: parameters, argument :: arguments, substitution, span => do
        let expected := match parameter.type with | .data _ => some (formal.parameter.result.type.rename substitution) | .function _ => none
        let value ← expression fuel input scope ctx argument expected
        checkAnnotation parameter.type value span
        let selected ← match parameter.type with
          | .data _ => pure []
          | .function signature => do
              let selected ← target value span
              recordTarget selected signature
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
      | .concrete id => invokeDefinition fuel input scope ctx id arguments span
      | .probe _ => do
          unless (← get).audit do error span "E_INTERNAL_FUNCTION" "signature probe escaped into executable specialization"
          let .function parameters resultType := selected.signature | error span "E_TYPE" "invalid Fn target"
          unless parameters.toList.length == arguments.length do error span "E_ARITY" "wrong Fn argument count"
          let values ← (parameters.toList.zip arguments).mapM fun (parameter, argument) => do
            let value ← expression fuel input scope ctx argument (← callableData parameter span)
            if parameter.isFunction then
              let actual ← target value span
              sameSignature parameter actual.signature span
              recordTarget actual parameter
            return value
          let (bindings, _) ← freeze values
          return wrap bindings (← probeResult resultType span)

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
        let hint ← match type with | none => pure none | some type => annotation input scope ctx type span
        let value ← expression fuel input scope ctx value hint
        if let some type := type then checkAnnotation type value span
        let term := match hint with | some type => Core.Term.ascribe type value.term | none => value.term
        let symbol ← fresh
        body (Source.Bodies.nameObject term.result.reference name)
        let inner := ctx ++ [⟨⟨name, ⟨symbol, term.result⟩, span⟩, value.target⟩]
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
        let mut inner : Context := ctx ++ [⟨⟨witness, ⟨symbol, ⟨.object shape.witnessType, some reference⟩⟩, span⟩, none⟩]
        let mut symbols := []
        for (name, application) in fields.zip (shape.instantiate reference) do
          body (Source.Bodies.bindName input.body scope inner.data name span)
          let field ← fresh
          symbols := symbols ++ [field]
          inner := inner ++ [⟨⟨name, ⟨field, ⟨.indexed application, none⟩⟩, span⟩, none⟩]
        let valueBody ← statementsThen fuel input scope inner rest output expected blockSpan
        body (Source.Bodies.checkEscape input.body ctx.data valueBody.term.result.type span)
        return { valueBody with term := .unpack symbol symbols value valueBody.term }
end

end VastitasKernel.Indexed.FunctionSource.Compiler
