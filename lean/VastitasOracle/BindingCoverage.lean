import VastitasKernel.MidIR.Lower
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- Interpret the symbol context against any partial SSA store. -/
def readBinding (ctx : List (Nat × Ref)) (slots : Ref → Option Value) : Values :=
  fun symbol => (ctx.lookup symbol).bind slots

/-- The very reference returned by the builder denotes the Core variable,
including absent names and unreadable slots. -/
theorem variable_constructor_coverage (module : Core.Module) (fuel symbol : Nat)
    (annotation : Core.Result) (ctx : List (Nat × Ref)) (slots : Ref → Option Value) :
    ReadsVariable symbol annotation ∧
    (ctx.lookup symbol).bind slots =
      eval module (fuel+1) (readBinding ctx slots) (.variable symbol annotation) :=
  ⟨reads_variable symbol annotation, rfl⟩

theorem scope_constructor_coverage (module : Core.Module) (fuel : Nat)
    (values : Values) (body : Core.Term) :
    ForwardsScope body ∧ (.scope body : Core.Term).result = body.result ∧
    eval module (fuel+1) values (.scope body) = eval module fuel values body :=
  ⟨forwards_scope body, rfl, rfl⟩

theorem ascription_constructor_coverage (module : Core.Module) (fuel : Nat)
    (values : Values) (annotation : Core.DataType) (body : Core.Term) :
    ChecksAscription annotation body ∧
    (annotation = body.result.type → (.ascribe annotation body : Core.Term).result = body.result) ∧
    eval module (fuel+1) values (.ascribe annotation body) = eval module fuel values body := by
  refine ⟨checks_ascription annotation body, ?_, rfl⟩
  rintro rfl
  rfl

private theorem readBinding_cons (ctx : List (Nat × Ref)) (slots : Ref → Option Value)
    (symbol : Nat) (ref : Ref) (value : Value) (read : slots ref = some value) :
    readBinding ((symbol,ref) :: ctx) slots = bindValue (readBinding ctx slots) symbol value := by
  funext other
  by_cases h : other = symbol
  · subst other; simp [readBinding, List.lookup, bindValue, read]
  · simp [readBinding, List.lookup, bindValue, h, beq_eq_false_iff_ne.mpr h]

/-- The initializer and body use successive builder states. When the new SSA
slot contains the initializer's Core value and live bindings retain their
values across its evaluation, reading the extended context agrees with Core
for the entire body, even when another symbol refers to the same slot. -/
theorem let_constructor_coverage (module : Core.Module) (fuel symbol : Nat)
    (rhs body : Core.Term) (ctx : List (Nat × Ref)) (before after : Ref → Option Value) :
    BindsLet symbol rhs body ∧
    (eval module fuel (readBinding ctx before) rhs = none →
      eval module (fuel+1) (readBinding ctx before) (.letE symbol rhs body) = none) ∧
    ∀ ref value, eval module fuel (readBinding ctx before) rhs = some value →
      after ref = some value → readBinding ctx after = readBinding ctx before →
      eval module (fuel+1) (readBinding ctx before) (.letE symbol rhs body) =
        eval module fuel (readBinding ((symbol,ref) :: ctx) after) body := by
  refine ⟨binds_let symbol rhs body, ?_, ?_⟩
  · intro missing; simp [eval, missing]
  · intro ref value evaluated read preserved
    rw [readBinding_cons ctx after symbol ref value read, preserved]
    simp [eval, evaluated]

/-- A typed identity binding in an ordinary or assembled function produces the
same whole MidIR function as returning the parameter directly. -/
theorem lower_linked_typed_forwarder (env : Environment) (key : FunctionSource.Compiler.Key)
    (f : Core.Function) (resolve : Nat → Option CallTarget) (src localId : Nat) (ann : Core.Result) :
    lowerLinkedFunction env key {f with body := .scope (.letE localId
      (.ascribe ann.type (.variable src ann)) (.variable localId ann))} resolve =
    lowerLinkedFunction env key {f with body := .scope (.variable src ann)} resolve := by
  have keep {α β : Type} (o : Option (α × β)) : (o.bind fun v => some (v.1, v.2)) = o := by
    cases o <;> rfl
  let source := Core.Term.variable src ann
  let rhs := Core.Term.ascribe ann.type source
  let body := Core.Term.variable localId ann
  let binding := Core.Term.letE localId rhs body
  have foldedBinding : ExactFold.integer (.scope binding) = none := rfl
  have foldedDirect : ExactFold.integer (.scope source) = none := rfl
  have wrapped := forwards_scope binding
  have direct := forwards_scope source
  have ascribed := checks_ascription ann.type source
  have letBound := binds_let localId rhs body
  have variableRead := reads_variable src ann
  have bound := reads_variable localId ann
  unfold ForwardsScope at wrapped direct
  unfold ChecksAscription at ascribed
  unfold BindsLet at letBound
  unfold ReadsVariable at variableRead bound
  change lowerLinkedFunction env key {f with body := .scope binding} resolve =
    lowerLinkedFunction env key {f with body := .scope source} resolve
  unfold lowerLinkedFunction
  simp only [foldedBinding, foldedDirect, ite_self, wrapped, direct, binding, letBound, rhs, ascribed, source, Core.Term.result,
    ite_true, variableRead, body, bound, List.lookup_cons_self, Option.map_some]
  simp [keep]

/-- The typed local preserves the original Core value and the full execution
function, including its nominal identity, ABI and checked block graph. -/
theorem execute_linked_typed_forwarder (env : Environment) (key : FunctionSource.Compiler.Key)
    (f : Core.Function) (resolve : Nat → Option CallTarget) (src localId : Nat) (ann : Core.Result)
    (module : Core.Module) (values : Values) (fuel : Nat) :
    let direct := Core.Term.scope (.variable src ann)
    let bound := Core.Term.scope (.letE localId (.ascribe ann.type (.variable src ann)) (.variable localId ann))
    eval module (fuel+4) values bound = eval module (fuel+2) values direct ∧
    (lowerLinkedFunction env key {f with body := bound} resolve).bind (Function.execute env) =
      (lowerLinkedFunction env key {f with body := direct} resolve).bind (Function.execute env) := by
  dsimp only
  constructor
  · cases h : values src <;> simp [eval, h, bindValue]
  · rw [lower_linked_typed_forwarder]

end VastitasOracle.MidIR
