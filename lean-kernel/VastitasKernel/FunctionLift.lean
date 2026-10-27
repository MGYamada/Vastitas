import VastitasKernel.FunctionScope

namespace VastitasKernel.Surface

abbrev LiftM := StateT (Array Function) (Except Diagnostic)

-- IDs come from traversal, never diagnostic spans or frontend-supplied metadata.
mutual
  def liftExpr : Nat → Expr → LiftM Expr
    | 0, expr => throw { code := "E_LIMIT", message := "lambda lifting exceeds the supported nesting limit", span := expr.span }
    | fuel + 1, expr => do
      match expr with
      | .lambda params result body span =>
        let body ← liftBlock fuel body
        let id := (← get).size
        let name := s!"__vastitas_l{id}"
        unless (TypeExpr.function (params.map (·.ty)) result).callableData do
          throw { code := "E_TYPE", message := "lambda signatures require scalar/Fn types", span }
        modify (·.push { name, params, result, body, span })
        pure (.reference name span)
      | .reference _ span => throw { code := "E_RESERVED", message := "lifted references are internal, not source syntax", span }
      | .call name args span => pure (.call name (← args.mapM (liftExpr fuel)) span)
      | .invoke callee args span => pure (.invoke (← liftExpr fuel callee) (← args.mapM (liftExpr fuel)) span)
      | .unary op value span => pure (.unary op (← liftExpr fuel value) span)
      | .binary op left right span => pure (.binary op (← liftExpr fuel left) (← liftExpr fuel right) span)
      | .ite condition yes no span => pure (.ite (← liftExpr fuel condition) (← liftBlock fuel yes) (← liftBlock fuel no) span)
      | .block body span => pure (.block (← liftBlock fuel body) span)
      | .pack scheme point span => pure (.pack (← liftExpr fuel scheme) (← liftExpr fuel point) span)
      | _ => pure expr
  def liftBlock : Nat → Block → LiftM Block
    | 0, .mk _ _ span => throw { code := "E_LIMIT", message := "lambda lifting exceeds the supported nesting limit", span }
    | fuel + 1, .mk statements result span => do
      let statements ← statements.mapM fun statement => do
        match statement with
        | .letE name annotation value span => pure (.letE name annotation (← liftExpr fuel value) span)
        | .unpack value scheme point span => pure (.unpack (← liftExpr fuel value) scheme point span)
      pure (.mk statements (← liftExpr fuel result) span)
end

def liftProgram (p : Program) : Except Diagnostic (Program × List Function) := do
  let action : LiftM Program := do
    let functions ← p.functions.mapM fun f => do pure { f with body := ← liftBlock 512 f.body }
    let methods ← p.methods.mapM fun m => do pure { m with body := ← liftBlock 512 m.body }
    pure { p with functions, methods }
  let (p, lambdas) ← action.run #[]
  pure (p, lambdas.toList)

end VastitasKernel.Surface
