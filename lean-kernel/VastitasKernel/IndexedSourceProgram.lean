import VastitasKernel.IndexedSourceBodies
import VastitasKernel.Checker

namespace VastitasKernel.Indexed.Source.Bodies

def prepareSignature (input : Input) (owner : DeclId) (source : Source.Function) (id : Nat) : M Signature := do
  let mut context : TypeContext := []
  for parameter in source.params do
    bindName input owner.scope context parameter.name parameter.span
    let type ← type input owner.scope context parameter.type parameter.span
    let symbol ← fresh
    let reference := match type with | .object type => some (.local type symbol) | _ => none
    if let some reference := reference then rememberObject reference parameter.span "parameter" (some parameter.name)
    context := context ++ [⟨parameter.name, ⟨symbol, ⟨type, reference⟩⟩, parameter.span⟩]
  let result ← type input owner.scope context source.result source.span
  return ⟨id, owner, source, context, result⟩

mutual
  def expression : Nat → Input → Namespace.Scope → TypeContext → Source.Expr → Option Core.DataType → M Core.Term
    | 0, _, _, _, expr, _ => checkingBudgetExceeded expr.span
    | fuel + 1, input, scope, ctx, expr, expected => do
      let span := expr.span
      let value ← match expr with
      | .integer value _ => integerLiteral value span expected
      | .boolean value _ => pure (.boolean value)
      | .unit _ => pure .unit
      | .variable name _ => do
          let some binding := ctx.lookup name | fail span "E_NAME" s!"unbound value '{name}'"
          pure (.variable binding.symbol binding.result)
      | .unary operator operand _ => do
          let (operator, type) ← match operator with
            | "-" => pure (UnaryOp.neg, Core.DataType.pure .int)
            | "!" => pure (UnaryOp.not, Core.DataType.pure .bool)
            | _ => fail span "E_OPERATOR" "unsupported unary operator"
          let value ← expression fuel input scope ctx operand (some type)
          pure (.unary operator value ⟨type, none⟩)
      | .binary operator left right _ => do
          let some operator := BinaryOp.ofString? operator | fail span "E_OPERATOR" "unsupported binary operator"
          let arithmetic := [BinaryOp.add, .sub, .mul].contains operator
          let boolean := operator == .and || operator == .or
          let hint := if boolean then some (Core.DataType.pure .bool)
            else if arithmetic then expected.filter integerType else none
          let (left, right) ← if literalLike left && !literalLike right && hint.isNone then do
            let right ← expression fuel input scope ctx right none
            let left ← expression fuel input scope ctx left (some right.result.type)
            pure (left, right)
          else do
            let left ← expression fuel input scope ctx left hint
            let right ← expression fuel input scope ctx right (some left.result.type)
            pure (left, right)
          let result := if arithmetic then left.result.type else .pure .bool
          unless Core.Typing.BinaryTyping operator left.result.type right.result.type result do
            fail span "E_OPERATOR" "operator requires compatible scalar operands"
          pure (.binary operator left right ⟨result, none⟩)
      | .branch condition yes no _ => do
          let condition ← expression fuel input scope ctx condition (some (.pure .bool))
          let (yes, no) ← if expected.isNone && blockLiteralLike yes && !blockLiteralLike no then do
            let no ← block fuel input scope ctx no none
            let yes ← block fuel input scope ctx yes (some no.result.type)
            pure (yes, no)
          else do
            let yes ← block fuel input scope ctx yes expected
            let no ← block fuel input scope ctx no (expected.or (some yes.result.type))
            pure (yes, no)
          let yes := match expected with | some type => Core.Term.ascribe type yes | none => yes
          let no := match expected with | some type => Core.Term.ascribe type no | none => no
          unless yes.result.type == no.result.type do fail span "E_TYPE" "branches require the same data type"
          let reference ← match yes.result.type with
            | .object type =>
              if yes.result.reference == no.result.reference then pure yes.result.reference
              else some <$> freshObject type span "if merge of distinct objects"
            | _ => pure none
          pure (.branch condition yes no ⟨yes.result.type, reference⟩)
      | .block body _ => block fuel input scope ctx body expected
      | .pack annotation witness fields _ => do
          let (application, witness) ← match annotation with
            | .inferredPackage => do
              let witness ← expression fuel input scope ctx witness none
              pure (← legacyPackage input witness span, witness)
            | _ => do
              let .package application ← type input scope ctx annotation span
                | fail span "E_TYPE" "pack annotation must name an existential package"
              let some shape := input.declarations.package? application | fail span "E_TYPE" "unknown package case"
              pure (application, ← expression fuel input scope ctx witness (some (.object shape.witnessType)))
          let fields ← fields.mapM fun field => expression fuel input scope ctx field none
          unless Core.Typing.PackageTyping input.declarations application witness.result (fields.map Core.Term.result) do
            endpointFailure input (witness.result :: fields.map Core.Term.result) span "package fields do not match the exact witness and ordered field contract"
          pure (.pack application witness fields)
      | .call callee arguments _ => call fuel input scope ctx callee arguments span
      expect input expected value span

  def call : Nat → Input → Namespace.Scope → TypeContext → Path → List Source.Expr → Span → M Core.Term
    | 0, _, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, callee, arguments, span => do
      if callee.path == ["int"] then
        let [argument] := arguments | fail span "E_ARITY" s!"int expects 1 argument, found {arguments.length}"
        return .natToInt (← expression fuel input scope ctx argument (some (.pure .nat)))
      if callee.path == ["pair"] then
        let [first, second] := arguments | fail span "E_ARITY" "pair expects two arguments"
        let first ← expression fuel input scope ctx first none
        let second ← expression fuel input scope ctx second none
        let element ← match first.result.type, second.result.type with
          | .pure .nat, .pure .nat => pure PairElem.nat
          | .pure .int, .pure .int => pure PairElem.int
          | _, _ => fail span "E_TYPE" "pair operands must independently infer the same Nat or Int type"
        return .pair element first second
      if callee.path == ["pair_first"] || callee.path == ["pair_second"] then
        let [argument] := arguments | fail span "E_ARITY" "pair projection expects one argument"
        let value ← expression fuel input scope ctx argument none
        let .pure (.pair element) := value.result.type | fail span "E_TYPE" "pair projection requires a homogeneous Pair"
        return .project element (callee.path == ["pair_first"]) value
      if let [name] := callee.path then
        if (ctx.lookup name).isSome then fail span "E_TYPE" "a data value is not callable"
      if legacyFallback input scope callee then
        let name := callee.path.head!
        let (base, arguments) ← if name == "Affine" || name == "Base" then do
          let .variable marker _ :: rest := arguments | fail span "E_RING" "Affine/Base requires an explicit coefficient marker"
          pure (some (← legacyMarker marker span), rest)
        else pure (none, arguments)
        let hint := if name == "Affine" then some (Core.DataType.pure .nat) else none
        let values ← arguments.mapM fun argument => expression fuel input scope ctx argument hint
        return ← emitLegacy input ctx name base values span
      let target ← lookupPath input.index scope callee
      if target.kind == .indexedDeclaration then
        let some binding := input.declarations.primitive? target.owner
          | fail span "E_TYPE" "this indexed declaration is not a primitive function"
        modify fun state => { state with references := ⟨scope, callee, target⟩ :: state.references }
        let arity := binding.arity input.declarations.indexed
        unless arguments.length == arity do fail span "E_ARITY" s!"primitive expects {arity} arguments"
        let values ← arguments.zipIdx.mapM fun (argument, position) =>
          expression fuel input scope ctx argument (binding.argumentHint position)
        return ← emitPrimitive input ctx target.owner values span
      unless target.kind == .function do fail span "E_TYPE" "expected an ordinary function or declared primitive"
      let some signature := input.signatures[target.owner]? | fail span "E_NAME" "function has no source signature"
      unless signature.context.length == arguments.length do fail span "E_ARITY" "wrong function argument count"
      let (values, substitution) ← argumentsFor fuel input scope ctx signature.context arguments [] span
      let resultType := signature.result.rename substitution
      let reference ← match resultType with
        | .object type => some <$> freshObject type span s!"function call '{callee.name}'"
        | _ => pure none
      modify fun state => { state with calls := ⟨scope, callee, target, signature.id⟩ :: state.calls }
      return .call signature.id values substitution ⟨resultType, reference⟩

  def argumentsFor : Nat → Input → Namespace.Scope → TypeContext → TypeContext → List Source.Expr →
      List (ObjectRef × ObjectRef) → Span → M (List Core.Term × List (ObjectRef × ObjectRef))
    | 0, _, _, _, _, _, _, span => checkingBudgetExceeded span
    | _ + 1, _, _, _, [], [], substitution, _ => pure ([], substitution)
    | fuel + 1, input, scope, ctx, formal :: formals, argument :: arguments, substitution, span => do
        let value ← expression fuel input scope ctx argument (some (formal.parameter.result.type.rename substitution))
        let substitution ← match formal.parameter.result.reference, value.result.reference with
          | none, _ => pure substitution
          | some formal, some actual => pure ((formal, actual) :: substitution)
          | _, _ => fail span "E_TYPE" "dependent object argument has no nominal reference"
        let (rest, final) ← argumentsFor fuel input scope ctx formals arguments substitution span
        return (value :: rest, final)
    | _, _, _, _, _, _, _, span => fail span "E_ARITY" "wrong function argument count"

  def block : Nat → Input → Namespace.Scope → TypeContext → Source.Block → Option Core.DataType → M Core.Term
    | 0, _, _, _, .mk _ _ span, _ => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, .mk statements result span, expected => do
        let body ← statementsThen fuel input scope ctx statements result expected span
        checkEscape input ctx body.result.type span
        return .scope body

  def statementsThen : Nat → Input → Namespace.Scope → TypeContext → List Source.Stmt → Source.Expr →
      Option Core.DataType → Span → M Core.Term
    | 0, _, _, _, _, _, _, span => checkingBudgetExceeded span
    | fuel + 1, input, scope, ctx, [], result, expected, _ => expression fuel input scope ctx result expected
    | fuel + 1, input, scope, ctx, .letE name annotation value span :: rest, result, expected, blockSpan => do
        bindName input scope ctx name span
        let annotation ← annotation.mapM fun annotation => type input scope ctx annotation span
        let value ← expression fuel input scope ctx value annotation
        let value := match annotation with | some type => Core.Term.ascribe type value | none => value
        let symbol ← fresh
        nameObject value.result.reference name
        let inner := ctx ++ [⟨name, ⟨symbol, value.result⟩, span⟩]
        return .letE symbol value (← statementsThen fuel input scope inner rest result expected blockSpan)
    | fuel + 1, input, scope, ctx, .unpack value witness fields span :: rest, result, expected, blockSpan => do
        let value ← expression fuel input scope ctx value none
        let .package application := value.result.type | fail span "E_TYPE" "unpack requires an existential package"
        let some shape := input.declarations.package? application | fail span "E_TYPE" "unknown package case"
        unless fields.length == shape.fields.length do fail span "E_ARITY" "unpack field count does not match its declaration"
        bindName input scope ctx witness span
        let symbol ← fresh
        let reference := ObjectRef.local shape.witnessType symbol
        rememberObject reference span "unpack" (some witness)
        let mut inner := ctx ++ [⟨witness, ⟨symbol, ⟨.object shape.witnessType, some reference⟩⟩, span⟩]
        let mut fieldSymbols := []
        for (name, application) in fields.zip (shape.instantiate reference) do
          bindName input scope inner name span
          let field ← fresh
          fieldSymbols := fieldSymbols ++ [field]
          inner := inner ++ [⟨name, ⟨field, ⟨.indexed application, none⟩⟩, span⟩]
        let body ← statementsThen fuel input scope inner rest result expected blockSpan
        checkEscape input ctx body.result.type span
        return .unpack symbol fieldSymbols value body
end

/-- Stable Kahn ordering uses only actual Core calls. Its output is independently
checked for ordering and exact source identity/count before acceptance. -/
def sortFunctions (input : List Core.Function) : Namespace.Result (List Core.Function) := do
  let functions := input.toArray
  let mut positions : Std.HashMap Nat Nat := {}
  for i in [:functions.size] do
    if positions.contains functions[i]!.id then Namespace.problem functions[i]!.span "E_DUPLICATE" "duplicate function ID"
    positions := positions.insert functions[i]!.id i
  let mut dependencies : Array (Array Nat) := Array.replicate functions.size #[]
  let mut dependents : Array (Array Nat) := Array.replicate functions.size #[]
  let mut waiting := Array.replicate functions.size 0
  for i in [:functions.size] do
    let mut seen : Std.HashSet Nat := {}
    for id in functions[i]!.body.callIds do
      let some dependency := positions[id]?
        | Namespace.problem functions[i]!.span "E_NAME" "unknown function in emitted call graph"
      unless seen.contains dependency do
        seen := seen.insert dependency
        dependencies := dependencies.modify i (·.push dependency)
        dependents := dependents.modify dependency (·.push i)
    waiting := waiting.set! i dependencies[i]!.size
  let mut ready : Array Nat := #[]
  for i in [:functions.size] do
    if waiting[i]! == 0 then ready := ready.push i
  let mut cursor := 0
  let mut sorted : Array Nat := #[]
  while cursor < ready.size do
    let i := ready[cursor]!
    cursor := cursor + 1
    sorted := sorted.push i
    for dependent in dependents[i]! do
      waiting := waiting.modify dependent (· - 1)
      if waiting[dependent]! == 0 then ready := ready.push dependent
  if sorted.size != functions.size then
    let some start := (List.range functions.size).find? (fun i => waiting[i]! > 0)
      | Namespace.problem {} "E_INTERNAL_GRAPH" "missing unresolved function"
    let (cycle, _) ← (Checker.Internal.dependencyCycle dependencies waiting start).run {}
    let names := cycle.map fun i =>
      let owner := functions[i]!.definition
      "`" ++ owner.qualified ++ "`"
    Namespace.problem functions[start]!.span "E_RECURSION" s!"recursive call cycle {String.intercalate " → " names} is not supported"
  sorted.toList.mapM fun index =>
    match functions[index]? with
    | some function => pure function
    | none => Namespace.problem {} "E_INTERNAL_GRAPH" "invalid function permutation"

structure Lowered where
  module : Core.Module
  references : List Source.Reference
  calls : List CallReference
  deriving Repr, Inhabited

def lower (program : Source.Program) (declarations : Core.Declarations) : Namespace.Result Lowered := do
  dataOnly program
  let (geometry, references) ← (resolveGeometry program declarations).run []
  let input : Input := { index := program.indexed, declarations, geometry }
  let action : M (List Core.Function) := do
    let signatures ← program.functions.zipIdx.mapM fun ((owner, source), id) =>
      prepareSignature input owner source id
    let input := { input with signatures := signatures.foldl (fun table signature => table.insert signature.owner signature) {} }
    signatures.mapM fun signature => do
      let body ← block Limits.bodyChecking input signature.owner.scope signature.context signature.source.body (some signature.result)
      if generatedLets body > Limits.generatedLets then
        fail signature.source.span "E_LIMIT" s!"function exceeds the {Limits.generatedLets}-unit generated-let budget"
      return {
        id := signature.id, definition := signature.owner, parameters := signature.context.core,
        returnType := signature.result, body, span := signature.source.span }
  let (functions, state) ← action.run { references }
  let functions ← sortFunctions functions
  let main := (functions.find? fun f => f.definition.name == "main" && f.definition.scope.path.isEmpty &&
    f.definition.scope.package.source == program.root).map (·.id)
  return ⟨⟨declarations, functions, main⟩, state.references.reverse, state.calls.reverse⟩

/-- Array lookup is an independent audit of the numeric ID's source position.
Together with equal counts and Core's unique IDs it prevents dropping bodies. -/
def FunctionOriginsValid (program : Source.Program) (module : Core.Module) : Prop :=
  module.functions.length = program.functions.length ∧
    ∀ function ∈ module.functions,
      (program.functions.toArray[function.id]?).map Prod.fst = some function.definition

def validFunctionOrigins (program : Source.Program) (module : Core.Module) : Bool :=
  let sources := program.functions.toArray
  decide (module.functions.length = program.functions.length) && module.functions.all fun function =>
    (sources[function.id]?).map Prod.fst == some function.definition

theorem validFunctionOrigins_iff (program : Source.Program) (module : Core.Module) :
    validFunctionOrigins program module = true ↔ FunctionOriginsValid program module := by
  simp [validFunctionOrigins, FunctionOriginsValid, List.all_eq_true]

instance (program : Source.Program) (module : Core.Module) : Decidable (FunctionOriginsValid program module) :=
  decidable_of_iff (validFunctionOrigins program module = true) (validFunctionOrigins_iff program module)

def CallReference.Valid (index : Namespace.Indexed) (functions : Std.HashMap Nat DeclId) (reference : CallReference) : Prop :=
  reference.scope ∈ index.scopes ∧ reference.target.kind = .function ∧
    (Namespace.resolve index reference.scope reference.path.path reference.path.span).toOption = some reference.target ∧
    functions[reference.id]? = some reference.target.owner

instance (index : Namespace.Indexed) (functions : Std.HashMap Nat DeclId) (reference : CallReference) :
    Decidable (reference.Valid index functions) := by
  unfold CallReference.Valid
  infer_instance

def functionOwners (module : Core.Module) : Std.HashMap Nat DeclId :=
  module.functions.foldr (fun function table => table.insert function.id function.definition) {}

def CallsValid (index : Namespace.Indexed) (lowered : Lowered) : Prop :=
  ∀ reference ∈ lowered.calls, reference.Valid index (functionOwners lowered.module)

def validCalls (index : Namespace.Indexed) (lowered : Lowered) : Bool :=
  let owners := functionOwners lowered.module
  lowered.calls.all fun reference => decide (reference.Valid index owners)

theorem validCalls_iff (index : Namespace.Indexed) (lowered : Lowered) :
    validCalls index lowered = true ↔ CallsValid index lowered := by
  simp [validCalls, CallsValid, List.all_eq_true]

instance (index : Namespace.Indexed) (lowered : Lowered) : Decidable (CallsValid index lowered) :=
  decidable_of_iff (validCalls index lowered = true) (validCalls_iff index lowered)

structure CheckedProgram (program : Source.Program) (requireMain : Bool) where
  declarations : CheckedDeclarations program
  lowered : Lowered
  reconstructed : lower program declarations.resolved.declarations = .ok lowered
  core : Core.Typing.CheckedModule requireMain
  coreInput : core.module = lowered.module
  origins : FunctionOriginsValid program lowered.module
  references : ∀ reference ∈ lowered.references, reference.Valid program.indexed
  calls : CallsValid program.indexed lowered

def checkProgram (program : Source.Program) (requireMain : Bool := false) :
    Except Diagnostic (CheckedProgram program requireMain) := do
  dataOnly program
  let declarations ← checkDeclarations program
  match reconstructed : lower program declarations.resolved.declarations with
  | .error error => .error error
  | .ok lowered =>
    if origins : FunctionOriginsValid program lowered.module then
      if references : ∀ reference ∈ lowered.references, reference.Valid program.indexed then
        if calls : CallsValid program.indexed lowered then
          match audited : Core.Typing.checkModule lowered.module requireMain with
          | .error error => .error error
          | .ok core =>
            have exactInput : core.module = lowered.module := by
              unfold Core.Typing.checkModule at audited
              split at audited
              · split at audited
                · split at audited
                  · cases audited; rfl
                  · contradiction
                · contradiction
              · contradiction
            return ⟨declarations, lowered, reconstructed, core, exactInput, origins, references, calls⟩
        else Namespace.problem {} "E_OWNER" "source call target audit failed"
      else Namespace.problem {} "E_OWNER" "source declaration reference audit failed"
    else Namespace.problem {} "E_OWNER" "source function identity/coverage audit failed"

end VastitasKernel.Indexed.Source.Bodies
