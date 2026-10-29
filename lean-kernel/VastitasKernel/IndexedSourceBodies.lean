import VastitasKernel.IndexedSourceTypes

/-! Internal data-function elaboration. The public protocol-7 entry point must
also compose Fn specialization, finite dispatch and edit authority. This adapter
rejects those unsupported envelopes instead of silently dropping their bodies. -/
namespace VastitasKernel.Indexed.Source.Bodies

structure Signature where
  id : Nat
  owner : DeclId
  source : Source.Function
  context : TypeContext
  result : Core.DataType
  deriving Repr, Inhabited

structure CallReference where
  scope : Namespace.Scope
  path : Path
  target : Namespace.Target
  id : Nat
  deriving Repr, Inhabited

structure State where
  nextSymbol : Nat := 1
  references : List Source.Reference := []
  calls : List CallReference := []
  deriving Inhabited

abbrev M := StateT State Namespace.Result

structure Input where
  index : Namespace.Indexed
  declarations : Core.Declarations
  signatures : Std.HashMap DeclId Signature := {}

def fail (span : Span) (code message : String) : M α :=
  throw { code, message, span }

def fresh : M Nat := do
  let symbol := (← get).nextSymbol
  modify fun state => { state with nextSymbol := symbol + 1 }
  return symbol

def bindName (input : Input) (scope : Namespace.Scope) (ctx : TypeContext)
    (name : String) (span : Span) : M Unit := do
  let _ ← Namespace.binder input.index scope name span
  if (ctx.lookup name).isSome then fail span "E_DUPLICATE" s!"binding '{name}' is already in scope"

/-- Reuse the actual type elaborator with the once-built namespace index. The
contexts here are built by parameter/let/unpack elaboration, not wire metadata. -/
def type (input : Input) (scope : Namespace.Scope) (ctx : TypeContext)
    (raw : Source.DataType) (span : Span) : M Core.DataType := do
  let (type, references) ← (elaborateDataType input.index input.declarations scope ctx raw).run []
  unless type.Valid input.declarations do fail span "E_TYPE" "invalid indexed annotation"
  unless type.Scoped (Core.Typing.contextRefs ctx.core) do fail span "E_SCOPE" "annotation contains a local object outside its scope"
  modify fun state => { state with references := references ++ state.references }
  return type

def expect (input : Input) (expected : Option Core.DataType) (value : Core.Term) (span : Span) : M Core.Term := do
  if let some expected := expected then
    unless Core.Typing.Compatible input.declarations value.result.type expected do
      fail span "E_TYPE" "value does not satisfy the expected type; no implicit scalar or object-identity conversion"
  return value

def literalLike : Source.Expr → Bool
  | .integer .. => true
  | .unary "-" value _ => literalLike value
  | .binary op left right _ => ["+", "-", "*"].contains op && literalLike left && literalLike right
  | _ => false

def blockLiteralLike : Source.Block → Bool
  | .mk _ result _ => literalLike result

def integerType : Core.DataType → Bool
  | .pure .nat | .pure .int => true
  | _ => false

def primitiveResult : ValueType → Core.Result
  | .natural => ⟨.pure .nat, none⟩
  | .object type reference => ⟨.object type, some reference⟩
  | .indexed application => ⟨.indexed application, none⟩

def prepareSignature (input : Input) (owner : DeclId) (source : Source.Function) (id : Nat) : M Signature := do
  let mut context : TypeContext := []
  for parameter in source.params do
    bindName input owner.scope context parameter.name parameter.span
    let type ← type input owner.scope context parameter.type parameter.span
    let symbol ← fresh
    let reference := match type with | .object type => some (.local type symbol) | _ => none
    context := context ++ [⟨parameter.name, ⟨symbol, ⟨type, reference⟩⟩, parameter.span⟩]
  let result ← type input owner.scope context source.result source.span
  return ⟨id, owner, source, context, result⟩

mutual
  def expression : Nat → Input → Namespace.Scope → TypeContext → Source.Expr → Option Core.DataType → M Core.Term
    | 0, _, _, _, expr, _ => fail expr.span "E_LIMIT" s!"function exceeds the {Limits.bodyChecking}-unit checking budget"
    | fuel + 1, input, scope, ctx, expr, expected => do
      let span := expr.span
      let value ← match expr with
      | .integer value _ => do
          unless !value.isEmpty && value.toList.all (fun c => c >= '0' && c <= '9') do
            fail span "E_LITERAL" "integer literal must contain only decimal digits"
          let some value := value.toNat? | fail span "E_LITERAL" "invalid decimal integer"
          pure (if expected == some (.pure .nat) then .natural value else .integer (Int.ofNat value))
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
              else pure (some (.local type (← fresh)))
            | _ => pure none
          pure (.branch condition yes no ⟨yes.result.type, reference⟩)
      | .block body _ => block fuel input scope ctx body expected
      | .pack annotation witness fields _ => do
          let .package application ← type input scope ctx annotation span
            | fail span "E_TYPE" "pack annotation must name an existential package"
          let some shape := input.declarations.package? application | fail span "E_TYPE" "unknown package case"
          let witness ← expression fuel input scope ctx witness (some (.object shape.witnessType))
          let fields ← fields.mapM fun field => expression fuel input scope ctx field none
          unless Core.Typing.PackageTyping input.declarations application witness.result (fields.map Core.Term.result) do
            fail span "E_ENDPOINT" "package fields do not match the exact witness and ordered field contract"
          pure (.pack application witness fields)
      | .call callee arguments _ => call fuel input scope ctx callee arguments span
      expect input expected value span

  def call : Nat → Input → Namespace.Scope → TypeContext → Path → List Source.Expr → Span → M Core.Term
    | 0, _, _, _, _, _, span => fail span "E_LIMIT" "call exceeds the checking budget"
    | fuel + 1, input, scope, ctx, callee, arguments, span => do
      if callee.path == ["int"] then
        let [argument] := arguments | fail span "E_ARITY" "int expects one argument"
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
      let target ← Namespace.resolve input.index scope callee.path callee.span
      if target.kind == .indexedDeclaration then
        let some binding := input.declarations.primitive? target.owner
          | fail span "E_TYPE" "this indexed declaration is not a primitive function"
        modify fun state => { state with references := ⟨scope, callee, target⟩ :: state.references }
        let arity := match binding with | .global _ => 0 | .compose _ | .apply .. => 2 | _ => 1
        unless arguments.length == arity do fail span "E_ARITY" s!"primitive expects {arity} arguments"
        let hint := match binding with | .descriptor _ => some (Core.DataType.pure .nat) | _ => none
        let values ← arguments.mapM fun argument => expression fuel input scope ctx argument hint
        let some operands := (values.map Core.Term.result).mapM Core.Result.primitiveType?
          | fail span "E_TYPE" "primitive operand shape mismatch"
        let brand ← match binding with | .descriptor _ => fresh | _ => pure 0
        let some result := inferPrimitiveResult input.declarations.indexed binding brand operands
          | fail span "E_TYPE" "primitive operand shape mismatch"
        unless validPrimitive input.declarations.indexed binding (Core.Typing.contextRefs ctx.core) brand operands result do
          fail span "E_ENDPOINT" "primitive capability, endpoint or coefficient contract failed"
        return .primitive target.owner values (primitiveResult result)
      unless target.kind == .function do fail span "E_TYPE" "expected an ordinary function or declared primitive"
      let some signature := input.signatures[target.owner]? | fail span "E_NAME" "function has no source signature"
      unless signature.context.length == arguments.length do fail span "E_ARITY" "wrong function argument count"
      let (values, substitution) ← argumentsFor fuel input scope ctx signature.context arguments [] span
      let resultType := signature.result.rename substitution
      let reference ← match resultType with
        | .object type => pure (some (.local type (← fresh)))
        | _ => pure none
      modify fun state => { state with calls := ⟨scope, callee, target, signature.id⟩ :: state.calls }
      return .call signature.id values substitution ⟨resultType, reference⟩

  def argumentsFor : Nat → Input → Namespace.Scope → TypeContext → TypeContext → List Source.Expr →
      List (ObjectRef × ObjectRef) → Span → M (List Core.Term × List (ObjectRef × ObjectRef))
    | 0, _, _, _, _, _, _, span => fail span "E_LIMIT" "arguments exceed the checking budget"
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
    | 0, _, _, _, .mk _ _ span, _ => fail span "E_LIMIT" "block exceeds the checking budget"
    | fuel + 1, input, scope, ctx, .mk statements result span, expected => do
        let body ← statementsThen fuel input scope ctx statements result expected span
        unless body.result.type.Scoped (Core.Typing.contextRefs ctx.core) do
          fail span "E_ESCAPE" "block result contains a local object index; package the witness with its fields"
        return .scope body

  def statementsThen : Nat → Input → Namespace.Scope → TypeContext → List Source.Stmt → Source.Expr →
      Option Core.DataType → Span → M Core.Term
    | 0, _, _, _, _, _, _, span => fail span "E_LIMIT" "statements exceed the checking budget"
    | fuel + 1, input, scope, ctx, [], result, expected, _ => expression fuel input scope ctx result expected
    | fuel + 1, input, scope, ctx, .letE name annotation value span :: rest, result, expected, blockSpan => do
        bindName input scope ctx name span
        let annotation ← annotation.mapM fun annotation => type input scope ctx annotation span
        let value ← expression fuel input scope ctx value annotation
        let value := match annotation with | some type => Core.Term.ascribe type value | none => value
        let symbol ← fresh
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
        let mut inner := ctx ++ [⟨witness, ⟨symbol, ⟨.object shape.witnessType, some reference⟩⟩, span⟩]
        let mut fieldSymbols := []
        for (name, application) in fields.zip (shape.instantiate reference) do
          bindName input scope inner name span
          let field ← fresh
          fieldSymbols := fieldSymbols ++ [field]
          inner := inner ++ [⟨name, ⟨field, ⟨.indexed application, none⟩⟩, span⟩]
        let body ← statementsThen fuel input scope inner rest result expected blockSpan
        unless body.result.type.Scoped (Core.Typing.contextRefs ctx.core) do
          fail span "E_ESCAPE" "unpack result contains the opened local witness; repack it before returning"
        return .unpack symbol fieldSymbols value body
end

end VastitasKernel.Indexed.Source.Bodies
