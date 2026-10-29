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
  deriving Repr, Inhabited

structure Lifted where
  definitions : Array Definition
  namedCount : Nat
  deriving Repr, Inhabited

abbrev LiftM := StateT (Array Definition) Namespace.Result

mutual
  def liftExpr : Nat → Nat → Nat → DeclId → Expr → LiftM Expr
    | 0, _, _, _, expr => throw { code := "E_LIMIT", message := "lambda lifting exceeds the source nesting limit", span := expr.span }
    | fuel + 1, namedCount, origin, owner, expr => do
      match expr with
      | .lifted _ span => throw { code := "E_RESERVED", message := "lifted function references are backend-only", span }
      | .lambda params result body span =>
        let body ← liftBlock fuel namedCount origin owner body
        let function : Function := ⟨"", params, result, body, false, span⟩
        unless function.callable.isSome do throw { code := "E_TYPE", message := "lambda signatures require scalar/Fn types", span }
        let id := namedCount + (← get).size
        modify (·.push ⟨id, origin, owner, function, true⟩)
        return .lifted id span
      | .call path arguments span => return .call path (← arguments.mapM (liftExpr fuel namedCount origin owner)) span
      | .invoke callee arguments span => return .invoke (← liftExpr fuel namedCount origin owner callee) (← arguments.mapM (liftExpr fuel namedCount origin owner)) span
      | .unary op value span => return .unary op (← liftExpr fuel namedCount origin owner value) span
      | .binary op left right span => return .binary op (← liftExpr fuel namedCount origin owner left) (← liftExpr fuel namedCount origin owner right) span
      | .branch condition yes no span => return .branch (← liftExpr fuel namedCount origin owner condition) (← liftBlock fuel namedCount origin owner yes) (← liftBlock fuel namedCount origin owner no) span
      | .block body span => return .block (← liftBlock fuel namedCount origin owner body) span
      | .pack type witness fields span => return .pack type (← liftExpr fuel namedCount origin owner witness) (← fields.mapM (liftExpr fuel namedCount origin owner)) span
      | _ => return expr
  def liftBlock : Nat → Nat → Nat → DeclId → Block → LiftM Block
    | 0, _, _, _, .mk _ _ span => throw { code := "E_LIMIT", message := "lambda lifting exceeds the source nesting limit", span }
    | fuel + 1, namedCount, origin, owner, .mk statements result span => do
      let statements ← statements.mapM fun statement => do
        match statement with
        | .letE name type value span => return .letE name type (← liftExpr fuel namedCount origin owner value) span
        | .unpack value witness fields span => return .unpack (← liftExpr fuel namedCount origin owner value) witness fields span
      return .mk statements (← liftExpr fuel namedCount origin owner result) span
end

def liftProgram (program : Program) : Namespace.Result Lifted := do
  let functions := program.functions
  let action : LiftM (List Definition) := functions.zipIdx.mapM fun ((owner, function), id) => do
    let body ← liftBlock Limits.sourceNesting functions.length id owner function.body
    return ⟨id, id, owner, { function with body }, false⟩
  let (named, lambdas) ← action.run #[]
  return ⟨named.toArray ++ lambdas, named.length⟩

end VastitasKernel.Indexed.FunctionSource
