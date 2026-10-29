import VastitasKernel.IndexedFunctionScope

namespace VastitasKernel.Indexed.FunctionSource

/-- Source IDs and lambda IDs are assigned by the backend traversal. A lambda
retains its containing function's canonical owner, not a name based on a span. -/
structure Definition where
  id : Nat
  origin : Nat
  owner : DeclId
  function : Function
  isLambda : Bool := false
  bodyScope : Namespace.Scope := owner.scope
  deriving Repr, Inhabited

structure Lifted where
  definitions : Array Definition
  namedCount : Nat
  deriving Repr, Inhabited

abbrev LiftM := StateT (Array Definition) Namespace.Result

mutual
  def liftExpr : Nat → Nat → Nat → DeclId → Namespace.Scope → Expr → LiftM Expr
    | 0, _, _, _, _, expr => throw { code := "E_LIMIT", message := "lambda lifting exceeds the source nesting limit", span := expr.span }
    | fuel + 1, namedCount, origin, owner, scope, expr => do
      match expr with
      | .lifted _ span => throw { code := "E_RESERVED", message := "lifted function references are backend-only", span }
      | .lambda params result body span =>
        let body ← liftBlock fuel namedCount origin owner scope body
        let function : Function := ⟨"", params, result, body, false, span⟩
        unless function.callable.isSome do throw { code := "E_TYPE", message := "lambda signatures require scalar/Fn types", span }
        let id := namedCount + (← get).size
        modify (·.push ⟨id, origin, owner, function, true, scope⟩)
        return .lifted id span
      | .call path arguments span => return .call path (← arguments.mapM (liftExpr fuel namedCount origin owner scope)) span
      | .invoke callee arguments span => return .invoke (← liftExpr fuel namedCount origin owner scope callee) (← arguments.mapM (liftExpr fuel namedCount origin owner scope)) span
      | .unary op value span => return .unary op (← liftExpr fuel namedCount origin owner scope value) span
      | .binary op left right span => return .binary op (← liftExpr fuel namedCount origin owner scope left) (← liftExpr fuel namedCount origin owner scope right) span
      | .branch condition yes no span => return .branch (← liftExpr fuel namedCount origin owner scope condition) (← liftBlock fuel namedCount origin owner scope yes) (← liftBlock fuel namedCount origin owner scope no) span
      | .block body span => return .block (← liftBlock fuel namedCount origin owner scope body) span
      | .pack type witness fields span => return .pack type (← liftExpr fuel namedCount origin owner scope witness) (← fields.mapM (liftExpr fuel namedCount origin owner scope)) span
      | _ => return expr
  def liftBlock : Nat → Nat → Nat → DeclId → Namespace.Scope → Block → LiftM Block
    | 0, _, _, _, _, .mk _ _ span => throw { code := "E_LIMIT", message := "lambda lifting exceeds the source nesting limit", span }
    | fuel + 1, namedCount, origin, owner, scope, .mk statements result span => do
      let statements ← statements.mapM fun statement => do
        match statement with
        | .letE name type value span => return .letE name type (← liftExpr fuel namedCount origin owner scope value) span
        | .unpack value witness fields span => return .unpack (← liftExpr fuel namedCount origin owner scope value) witness fields span
      return .mk statements (← liftExpr fuel namedCount origin owner scope result) span
end

def liftDefinitions (functions : List (DeclId × Function)) : Namespace.Result Lifted := do
  let action : LiftM (List Definition) := functions.zipIdx.mapM fun ((owner, function), id) => do
    let body ← liftBlock Limits.sourceNesting functions.length id owner owner.scope function.body
    return ⟨id, id, owner, { function with body }, false, owner.scope⟩
  let (named, lambdas) ← action.run #[]
  return ⟨named.toArray ++ lambdas, named.length⟩

def liftProgram (program : Program) : Namespace.Result Lifted := liftDefinitions program.functions

end VastitasKernel.Indexed.FunctionSource
