import VastitasKernel.IndexedFunctionSource
import VastitasKernel.NamespaceChecker

namespace VastitasKernel.Indexed.FunctionSource

private def unbound (names : List String) (path : Source.Path) : List Source.Path :=
  if let [name] := path.path then if names.contains name then [] else [path] else [path]

def dataTypeUses (bound : List String) : Source.DataType → List Source.Path
  | .pure _ => []
  | .object type => unbound bound type.domain ++ unbound bound type.marker
  | .application family arguments => unbound bound family ++ arguments.flatMap fun argument =>
      match argument with | .natural _ => [] | .name path => unbound bound path

def typeUses (bound : List String) : FnType → List Source.Path
  | .data type => dataTypeUses bound type
  | .function _ => [] -- valid Fn signatures contain only scalar/Fn types

def signatureUses : List String → List Param → FnType → List Source.Path
  | bound, [], result => typeUses bound result
  | bound, parameter :: rest, result =>
      typeUses bound parameter.type ++ signatureUses (parameter.name :: bound) rest result

/- Lexical free-name traversal includes indexed annotations and all package
fields. Nested independent lambdas are audited as separate scopes. -/
mutual
  def freeExpr : List String → Expr → List Source.Path
    | bound, .variable name span => unbound bound ⟨[name], span⟩
    | bound, .functionValue path _ => unbound bound path
    | bound, .call path arguments _ => unbound bound path ++ arguments.flatMap (freeExpr bound)
    | bound, .invoke callee arguments _ => freeExpr bound callee ++ arguments.flatMap (freeExpr bound)
    | _, .lambda .. => []
    | bound, .unary _ value _ => freeExpr bound value
    | bound, .binary _ left right _ => freeExpr bound left ++ freeExpr bound right
    | bound, .branch condition yes no _ => freeExpr bound condition ++ freeBlock bound yes ++ freeBlock bound no
    | bound, .block body _ => freeBlock bound body
    | bound, .pack type witness fields _ => dataTypeUses bound type ++ freeExpr bound witness ++ fields.flatMap (freeExpr bound)
    | _, _ => []
  termination_by _ expr => (sizeOf expr, 0)
  def freeBlock (bound : List String) : Block → List Source.Path
    | .mk statements result _ => freeStatements bound statements result
  termination_by block => (sizeOf block, 0)
  def freeStatements (bound : List String) : List Stmt → Expr → List Source.Path
    | [], result => freeExpr bound result
    | .letE name annotation value _ :: rest, result =>
      annotation.toList.flatMap (typeUses bound) ++ freeExpr bound value ++ freeStatements (name :: bound) rest result
    | .unpack value witness fields _ :: rest, result =>
      freeExpr bound value ++ freeStatements (fields ++ witness :: bound) rest result
  termination_by statements result => (sizeOf statements + sizeOf result, 1)
end

structure LambdaScope where
  free : List Source.Path
  outer : List String
  bindings : List (String × Span)
  function : Function
  deriving Repr, Inhabited

/- All binders belonging to this lambda's own lexical blocks. Binders of
nested lambdas are checked against their own complete enclosing context. -/
mutual
  def exprBindings : Expr → List (String × Span)
    | .lambda .. => []
    | .call _ arguments _ => arguments.flatMap exprBindings
    | .invoke callee arguments _ => exprBindings callee ++ arguments.flatMap exprBindings
    | .unary _ value _ => exprBindings value
    | .binary _ left right _ => exprBindings left ++ exprBindings right
    | .branch condition yes no _ => exprBindings condition ++ blockBindings yes ++ blockBindings no
    | .block body _ => blockBindings body
    | .pack _ witness fields _ => exprBindings witness ++ fields.flatMap exprBindings
    | _ => []
  def blockBindings : Block → List (String × Span)
    | .mk statements result _ => statements.flatMap stmtBindings ++ exprBindings result
  def stmtBindings : Stmt → List (String × Span)
    | .letE name _ value span => (name, span) :: exprBindings value
    | .unpack value witness fields span => ((witness :: fields).map (·, span)) ++ exprBindings value
end

mutual
  def lambdaScopes : List String → Expr → List LambdaScope
    | outer, .lambda params result body span =>
      { free := signatureUses [] params result ++ freeBlock (params.map (·.name)) body,
        outer, bindings := params.map (fun p => (p.name, p.span)) ++ blockBindings body,
        function := ⟨"", params, result, body, false, span⟩ } :: blockScopes (params.map (·.name) ++ outer) body
    | outer, .call _ arguments _ => arguments.flatMap (lambdaScopes outer)
    | outer, .invoke callee arguments _ => lambdaScopes outer callee ++ arguments.flatMap (lambdaScopes outer)
    | outer, .unary _ value _ => lambdaScopes outer value
    | outer, .binary _ left right _ => lambdaScopes outer left ++ lambdaScopes outer right
    | outer, .branch condition yes no _ => lambdaScopes outer condition ++ blockScopes outer yes ++ blockScopes outer no
    | outer, .block body _ => blockScopes outer body
    | outer, .pack _ witness fields _ => lambdaScopes outer witness ++ fields.flatMap (lambdaScopes outer)
    | _, _ => []
  termination_by _ expr => (sizeOf expr, 0)
  def blockScopes (outer : List String) : Block → List LambdaScope
    | .mk statements result _ => statementScopes outer statements result
  termination_by block => (sizeOf block, 0)
  def statementScopes (outer : List String) : List Stmt → Expr → List LambdaScope
    | [], result => lambdaScopes outer result
    | .letE name _ value _ :: rest, result => lambdaScopes outer value ++ statementScopes (name :: outer) rest result
    | .unpack value witness fields _ :: rest, result =>
      lambdaScopes outer value ++ statementScopes (fields ++ witness :: outer) rest result
  termination_by statements result => (sizeOf statements + sizeOf result, 1)
end

def Program.lambdaScopes (program : Program) : List (Namespace.Scope × LambdaScope) :=
  program.functions.flatMap fun (owner, function) =>
    (blockScopes (function.params.map (·.name)) function.body).map (owner.scope, ·)

def available (index : Namespace.Indexed) (scope : Namespace.Scope) (path : Source.Path) : Bool :=
  if [["int"], ["pair"], ["pair_first"], ["pair_second"]].contains path.path then true
  else (Namespace.resolve index scope path.path path.span).isOk

/-- These conditions are recomputed from the actual input, not accepted from
a frontend free-name or binding certificate. Body typing is a separate audit. -/
def ScopeSafe (index : Namespace.Indexed) (scope : Namespace.Scope) (lambda : LambdaScope) : Prop :=
  lambda.function.callable.isSome = true ∧
    (∀ use ∈ lambda.free, available index scope use = true) ∧
    ∀ binding ∈ lambda.bindings, binding.1 ∉ lambda.outer

instance (index : Namespace.Indexed) (scope : Namespace.Scope) (lambda : LambdaScope) :
    Decidable (ScopeSafe index scope lambda) := by
  unfold ScopeSafe
  infer_instance

def ScopesSafe (program : Program) : Prop :=
  ∀ entry ∈ program.lambdaScopes, ScopeSafe program.headers.indexed entry.1 entry.2

def scopesSafe (program : Program) : Bool :=
  let index := program.headers.indexed
  program.lambdaScopes.all fun entry => decide (ScopeSafe index entry.1 entry.2)

theorem scopesSafe_iff (program : Program) : scopesSafe program = true ↔ ScopesSafe program := by
  simp [scopesSafe, ScopesSafe, List.all_eq_true]

instance (program : Program) : Decidable (ScopesSafe program) :=
  decidable_of_iff (scopesSafe program = true) (scopesSafe_iff program)

/-- Diagnostic selection is not the acceptance test. -/
def scopeDiagnostic (program : Program) : Diagnostic := Id.run do
  let index := program.headers.indexed
  for (scope, lambda) in program.lambdaScopes do
    if lambda.function.callable.isNone then
      return { code := "E_TYPE", message := "lambda signatures require scalar/Fn types", span := lambda.function.span }
    for (name, span) in lambda.bindings do
      if lambda.outer.contains name then
        return { code := "E_SHADOW", message := s!"lambda binding '{name}' shadows an enclosing binding", span }
    for use in lambda.free do
      unless available index scope use do
        let name := String.intercalate "::" use.path
        let captured := match use.path with | [name] => lambda.outer.contains name | _ => false
        return {
          code := if captured then "E_CAPTURE" else "E_NAME"
          span := use.span
          message := s!"independent lambda cannot access '{name}'; use an explicit parameter or a visible global declaration" }
  return { code := "E_SCOPE", message := "lambda scope audit failed" }

end VastitasKernel.Indexed.FunctionSource
