import VastitasKernel.IndexedFunctionSource
import VastitasKernel.NamespaceChecker

/-! A program-wide admission policy for the common source-function compiler.
Units count syntax and binding slots, not elapsed time or native instructions.
Every applicable method instance, including nonwinners and unapplied bodies,
is charged before elaboration; exceeding the policy rejects the whole input. -/
namespace VastitasKernel.Indexed.FunctionSource.WorkBudget

mutual
  def expression : Expr → Nat
    | .call _ arguments _ => 1 + (arguments.map expression).sum
    | .invoke callee arguments _ => 1 + expression callee + (arguments.map expression).sum
    | .lambda params _ body _ => 1 + params.length + block body
    | .unary _ value _ => 1 + expression value
    | .binary _ left right _ => 1 + expression left + expression right
    | .branch condition yes no _ => 1 + expression condition + block yes + block no
    | .block body _ => 1 + block body
    | .pack _ witness fields _ => 1 + expression witness + (fields.map expression).sum
    | _ => 1
  def statement : Stmt → Nat
    | .letE _ _ value _ => 1 + expression value
    | .unpack value _ fields _ => 2 + fields.length + expression value
  def block : Block → Nat
    | .mk statements result _ => 1 + (statements.map statement).sum + expression result
end

def function (source : Function) : Nat := 1 + source.params.length + block source.body

def charge (used amount : Nat) (span : Span) : Namespace.Result Nat :=
  if used + amount > Limits.elaborationWork then
    Namespace.problem span "E_LIMIT"
      s!"program-wide elaboration exceeds the {Limits.elaborationWork}-unit budget (expanded bodies and binding slots)"
  else .ok (used + amount)

/-- Success retains the exact accumulated work; the check never wraps or
silently drops the current instance's charge. -/
theorem charge_exact {used amount next : Nat} {span : Span}
    (accepted : charge used amount span = .ok next) :
    next = used + amount ∧ next ≤ Limits.elaborationWork := by
  unfold charge at accepted
  split at accepted
  · contradiction
  · cases accepted
    constructor
    · rfl
    · omega

def check (functions : List Function) : Namespace.Result Unit := do
  let mut used := 0
  for source in functions do
    used ← charge used (function source) source.span

end VastitasKernel.Indexed.FunctionSource.WorkBudget
