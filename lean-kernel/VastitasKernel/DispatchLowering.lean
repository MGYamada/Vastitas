import VastitasKernel.DispatchChecker
import VastitasKernel.Checker

/-! The lowering section of the dispatch checker. Only the retained Surface checker
(`FunctionChecker.lean`) uses it, and it runs the retained Core checker
(`Checker.lean`). -/
namespace VastitasKernel.DispatchChecker
open Checker.Internal

/-- Lowering metadata is never sent to the final core checker. In particular,
integer expressions remain unresolved until their actual expected type is known.
ResultType retains nominal object references, not just the coarse Ty. -/
structure LoweredExpr where
  raw : RawExpr
  known : Option ResultType := none
  deriving Inhabited

def LoweredExpr.infer (value : LoweredExpr) (signatures : Signatures) (ctx : Context)
    (expected : Option Ty := none) : CheckM ResultType := do
  match value.known with
  | some info =>
    let _ ← expectedResult ctx expected ⟨.var 0 info⟩ value.raw.span
    return info
  | none => return (← checkExpr Limits.bodyChecking signatures ctx value.raw expected).term.resultType

def LoweredExpr.atom (raw : RawExpr) (ctx : Context) : LoweredExpr :=
  { raw, known := match raw with
    | .boolean .. => some ⟨.bool, none⟩
    | .unit .. => some ⟨.unit, none⟩
    | .variable name _ => (ctx.find? (·.name == name)).map (·.resultType)
    | _ => none }

def scalarKey (value : ResultType) (span : Span) : CheckM Nat :=
  match value.ty with
  | .nat => pure 0 | .int => pure 1 | .bool => pure 2 | .unit => pure 3
  | ty => fail span "E_TYPE" s!"generic dispatch requires concrete scalar arguments; found {ty.label}"

def independentData : Ty → Bool
  | .nat | .int | .bool | .unit | .pair _ => true
  | _ => false

/-- Calls have an expected-type-independent result. Scalar/Pair signatures reuse
already inferred operands; geometric calls keep the core's dependent argument
substitution and fresh-object construction. Both paths retain their ResultType. -/
def lowerCall (signatures : Signatures) (ctx : Context) (name : String)
    (args : List LoweredExpr) (span : Span) : CheckM LoweredExpr := do
  let raw := RawExpr.call name (args.map (·.raw)) span
  if let some signature := signatures[name]? then
    if signature.params.all (fun p => independentData p.ty) && independentData signature.result then
      arity name (args.map (·.raw)) signature.params.length span
      for (param, arg) in signature.params.zip args do
        let _ ← arg.infer signatures ctx (some param.ty)
      return { raw, known := some ⟨signature.result, none⟩ }
  let info := (← checkExpr Limits.bodyChecking signatures ctx raw none).term.resultType
  return { raw, known := some info }

/-- Reusing a result across a block still checks its original escape boundary.
The original statements are preserved for the final independent core check. -/
def lowerBlockResult (ctx : Context) (statements : List RawStmt) (result : LoweredExpr)
    (span : Span) : CheckM LoweredExpr := do
  if let some info := result.known then checkEscape ctx ⟨.var 0 info⟩ span
  return { result with raw := .block (.mk statements result.raw span) span }

end VastitasKernel.DispatchChecker
