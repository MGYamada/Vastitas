import VastitasKernel.MidIR.Lower
import VastitasOracle.MidIR

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- Every ordered Nat/Int combination selected by the actual lowering has
the operand and result signature of the checked operation. Its denotation
uses unbounded Core values, including mixed division and saturation. -/
theorem selected_binary_numbers (env : Environment) (op : BinaryOp)
    (a b : VastitasKernel.MidIR.ExactFold.Scalar) (phase : Phase) (code : Opcode phase)
    (selected : binaryCode op a.type b.type = some code) (valid : code.valid env = true)
    (out : Core.DataType) (typed : Core.Typing.BinaryTyping op a.type b.type out)
    (resolver : Resolver) :
    [a.type,b.type].mapM Ty.ofCore = some code.operands ∧ Ty.ofCore out = some code.result ∧
    denote env code [ExactFold.scalarValue a, ExactFold.scalarValue b] resolver =
      evalBinary op (ExactFold.scalarValue a) (ExactFold.scalarValue b) := by
  cases a <;> cases b <;> cases op <;>
    simp [binaryCode, ExactOp.binary, Arithmetic.ofCore, VastitasKernel.MidIR.ExactFold.Scalar.type,
      Ty.ofCore, guard, failure, pure, bind] at selected <;> subst code <;>
    simp [Core.Typing.BinaryTyping, VastitasKernel.MidIR.ExactFold.Scalar.type] at typed <;>
    first | contradiction | subst out; exact ⟨rfl,rfl,rfl⟩


/-- Logical and equality instructions over an actual Boolean signature. -/
private theorem selected_bool (env : Environment) (op : BinaryOp) (p : Phase) (code : Opcode p)
    (a b : Bool) (out : Core.DataType)
    (selected : binaryCode op (.pure .bool) (.pure .bool) = some code)
    (typed : Core.Typing.BinaryTyping op (.pure .bool) (.pure .bool) out) (r : Resolver) :
    code.operands = [.bool,.bool] ∧ Ty.ofCore out = some code.result ∧
    denote env code [.boolean a,.boolean b] r = evalBinary op (.boolean a) (.boolean b) := by
  cases op <;> simp [Core.Typing.BinaryTyping] at typed <;> subst out <;>
    simp [binaryCode, Ty.ofCore] at selected <;> subst code <;>
    cases a <;> cases b <;> exact ⟨rfl,rfl,rfl⟩

private theorem selected_unit (env : Environment) (op : BinaryOp) (p : Phase) (code : Opcode p)
    (out : Core.DataType) (selected : binaryCode op (.pure .unit) (.pure .unit) = some code)
    (typed : Core.Typing.BinaryTyping op (.pure .unit) (.pure .unit) out) (r : Resolver) :
    code.operands = [.unit,.unit] ∧ Ty.ofCore out = some code.result ∧
    denote env code [.unit,.unit] r = evalBinary op .unit .unit := by
  cases op <;> simp [Core.Typing.BinaryTyping] at typed <;> subst out <;>
    simp [binaryCode, Ty.ofCore] at selected <;> subst code <;> exact ⟨rfl,rfl,rfl⟩

private theorem selected_finite (env : Environment) (op : BinaryOp) (p : Phase) (code : Opcode p)
    (s : FiniteSort) (a b : String) (out : Core.DataType)
    (selected : binaryCode op (.finite s) (.finite s) = some code)
    (typed : Core.Typing.BinaryTyping op (.finite s) (.finite s) out) (r : Resolver) :
    code.operands = [.finite s,.finite s] ∧ Ty.ofCore out = some code.result ∧
    denote env code [.finiteTag s a,.finiteTag s b] r = evalBinary op (.finiteTag s a) (.finiteTag s b) := by
  cases op <;> simp [Core.Typing.BinaryTyping] at typed <;> subst out <;>
    simp [binaryCode, Ty.ofCore] at selected <;> subst code <;> refine ⟨rfl,rfl,?_⟩
  all_goals simp [denote, Evaluation.compareValues, Comparison.equality, evalBinary, guard] <;> exact (Bool.not_not _).symm

private theorem input_shapes {op : BinaryOp} {l r out : Core.DataType}
    (typed : Core.Typing.BinaryTyping op l r out) :
    ((l = .pure .nat ∨ l = .pure .int) ∧ (r = .pure .nat ∨ r = .pure .int)) ∨
    (l = .pure .bool ∧ r = .pure .bool) ∨
    (l = .pure .unit ∧ r = .pure .unit) ∨ ∃ s, l = .finite s ∧ r = .finite s := by
  cases op <;> simp only [Core.Typing.BinaryTyping] at typed
  case div =>
    rcases typed with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩ <;> simp
  all_goals obtain ⟨rfl, h, _⟩ := typed
  case eq | ne =>
    rcases h with h | h | h | h | finite
    all_goals first
      | subst l; simp
      | cases l <;> simp_all
  all_goals first | exact Or.inl ⟨h,h⟩ | exact Or.inr (Or.inl ⟨h,h⟩)

private theorem numeric_value (env : Core.Declarations) (world : World) {t : Core.DataType} {v : Value}
    (type : t = .pure .nat ∨ t = .pure .int) (h : ValueHasType env world v t) :
    ∃ a : VastitasKernel.MidIR.ExactFold.Scalar, t = a.type ∧ v = ExactFold.scalarValue a := by
  rcases type with rfl | rfl
  all_goals cases v <;> simp [ValueHasType] at h
  case natural n => exact ⟨.nat n,rfl,rfl⟩
  case integer n => exact ⟨.int n,rfl,rfl⟩

/-- For every admitted binary signature and every pair of well-typed Core
values, the SSA instruction preserves the complete mathematical value. The
nominal operand check is also preserved for finite equality. -/
theorem selected_binary {op : BinaryOp} {l r out : Core.DataType}
    (env : Core.Declarations) (world : World) (lhs rhs : Value) (phase : Phase) (code : Opcode phase)
    (typed : Core.Typing.BinaryTyping op l r out)
    (left : ValueHasType env world lhs l) (right : ValueHasType env world rhs r)
    (selected : binaryCode op l r = some code) (valid : code.valid env.indexed = true)
    (resolver : Resolver) :
    [l,r].mapM Ty.ofCore = some code.operands ∧ Ty.ofCore out = some code.result ∧
      denote env.indexed code [lhs,rhs] resolver = evalBinary op lhs rhs := by
  rcases input_shapes typed with ⟨lt,rt⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨s,rfl,rfl⟩
  · obtain ⟨a,rfl,rfl⟩ := numeric_value env world lt left
    obtain ⟨b,rfl,rfl⟩ := numeric_value env world rt right
    exact selected_binary_numbers _ _ _ _ _ _ selected valid out typed _
  · cases lhs <;> simp [ValueHasType] at left
    cases rhs <;> simp [ValueHasType] at right
    obtain ⟨args, res, obs⟩ := selected_bool _ _ _ _ _ _ _ selected typed resolver
    exact ⟨by rw [args]; rfl,res,obs⟩
  · cases lhs <;> simp [ValueHasType] at left
    cases rhs <;> simp [ValueHasType] at right
    obtain ⟨args, res, obs⟩ := selected_unit _ _ _ _ _ selected typed resolver
    exact ⟨by rw [args]; rfl,res,obs⟩
  · cases lhs <;> simp [ValueHasType] at left
    cases rhs <;> simp [ValueHasType] at right
    obtain ⟨rfl,_⟩ := left
    obtain ⟨rfl,_⟩ := right
    obtain ⟨args, res, obs⟩ := selected_finite _ _ _ _ _ _ _ _ selected typed resolver
    exact ⟨by rw [args]; rfl,res,obs⟩


/-- The opcode metadata and the constructor theorem use these exact alternatives.
An exact literal equality can take the Boolean constant route. -/
def binaryTags : List String :=
  let order : List Comparison := [.eq,.ne,.lt,.le,.gt,.ge]
  let arithmetic : List Arithmetic := [.add,.sub,.mul,.div]
  [(Opcode.boolean (p := .optimization) false).tag, (Opcode.boolAnd (p := .optimization)).tag,
    (Opcode.boolOr (p := .optimization)).tag] ++ order.map Comparison.tag ++
    (arithmetic.map fun op => (Opcode.exactOp (p := .optimization) (.nat op)).tag) ++
    (arithmetic.map fun op => (Opcode.exactOp (p := .optimization) (.int op)).tag) ++
    [(Opcode.exactOp (p := .optimization) .natIntDiv).tag, (Opcode.exactOp (p := .optimization) .intNatDiv).tag]

private theorem numeric_selection (env : Environment) (op : BinaryOp) (a b : VastitasKernel.MidIR.ExactFold.Scalar)
    (out : Core.DataType) (rule : Core.Typing.BinaryTyping op a.type b.type out) :
    ∃ (c : Opcode .optimization) (d : Opcode .execution),
      binaryCode op a.type b.type = some c ∧ binaryCode op a.type b.type = some d ∧
      c.execute env = some d ∧ c.valid env = true ∧ d.valid env = true ∧ c.tag ∈ binaryTags := by
  cases a <;> cases b <;> cases op <;>
    simp [Core.Typing.BinaryTyping, VastitasKernel.MidIR.ExactFold.Scalar.type] at rule <;>
    exact ⟨_,_,rfl,rfl,rfl,rfl,rfl,by decide⟩

/-- Every checked binary signature for actual Core operands selects a valid
instruction in both phases. The declared nominal sort is recovered from the
finite operand when equality is over a carrier or Hom set. -/
theorem binary_signature_selected {op : BinaryOp} {l r out : Core.DataType}
    (env : Core.Declarations) (world : World) (lhs rhs : Value)
    (rule : Core.Typing.BinaryTyping op l r out)
    (lt : ValueHasType env world lhs l) (rt : ValueHasType env world rhs r) :
    ∃ (c : Opcode .optimization) (d : Opcode .execution),
      binaryCode op l r = some c ∧ binaryCode op l r = some d ∧ c.execute env.indexed = some d ∧
      c.valid env.indexed = true ∧ d.valid env.indexed = true ∧ c.tag ∈ binaryTags := by
  rcases input_shapes rule with ⟨a,b⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨s,rfl,rfl⟩
  · obtain ⟨lhsNum,rfl,_⟩ := numeric_value env world a lt
    obtain ⟨rhsNum,rfl,_⟩ := numeric_value env world b rt
    exact numeric_selection env.indexed op lhsNum rhsNum out rule
  · cases op <;> simp [Core.Typing.BinaryTyping] at rule <;>
      exact ⟨_,_,rfl,rfl,rfl,rfl,rfl,by decide⟩
  · cases op <;> simp [Core.Typing.BinaryTyping] at rule <;>
      exact ⟨_,_,rfl,rfl,rfl,rfl,rfl,by decide⟩
  · have known : (FiniteSort.tags env.indexed s).isSome = true := by
      cases lhs <;> simp [ValueHasType] at lt
      obtain ⟨rfl, tag⟩ := lt
      cases found : FiniteSort.tags env.indexed _ <;> simp_all
    cases op <;> simp [Core.Typing.BinaryTyping] at rule <;>
      exact ⟨_,_,rfl,rfl,rfl,known,known,by simp only [Opcode.tag, Comparison.tag]; decide⟩


/-- The actual binary builder covers the exact literal optimization as well
as ordered operand evaluation. In each live instruction the selected operand
and result types, nominal comparison and semantic operation agree in both phases. -/
theorem binary_constructor_coverage (m : Core.Module) (op : BinaryOp) (left right : Core.Term)
    (out : Core.Result) (values : Values) (world : World) (r : Resolver) :
    LowersBinary op left right out ∧
    (∀ b, VastitasKernel.MidIR.ExactFold.literalComparison op left right = some b →
      IndexedEvaluation.Evaluates m values (.binary op left right out) (.boolean b) ∧
      (Opcode.boolean (p := .optimization) b).tag ∈ binaryTags) ∧
    ∀ lhs rhs, Core.Typing.BinaryTyping op left.result.type right.result.type out.type →
      ValueHasType m.declarations world lhs left.result.type →
      ValueHasType m.declarations world rhs right.result.type →
      ∃ (c : Opcode .optimization) (d : Opcode .execution),
        binaryCode op left.result.type right.result.type = some c ∧
        binaryCode op left.result.type right.result.type = some d ∧
        c.tag ∈ binaryTags ∧ c.execute m.declarations.indexed = some d ∧
        c.valid m.declarations.indexed = true ∧ d.valid m.declarations.indexed = true ∧
        [left.result.type,right.result.type].mapM Ty.ofCore = some c.operands ∧
        Ty.ofCore out.type = some c.result ∧
        [left.result.type,right.result.type].mapM Ty.ofCore = some d.operands ∧
        Ty.ofCore out.type = some d.result ∧
        denote m.declarations.indexed c [lhs,rhs] r = evalBinary op lhs rhs ∧
        denote m.declarations.indexed d [lhs,rhs] r = evalBinary op lhs rhs := by
  refine ⟨lowers_binary .., ?_, ?_⟩
  · intro b fold
    exact ⟨ExactFold.literal_comparison_evaluates m values out fold, List.Mem.head _⟩
  · intro lhs rhs typed hl hr
    obtain ⟨c,d,hc,hd,executed,vc,vd,tag⟩ := binary_signature_selected m.declarations world lhs rhs typed hl hr
    obtain ⟨ac,rc,oc⟩ := selected_binary m.declarations world lhs rhs _ c typed hl hr hc vc r
    obtain ⟨ad,rd,od⟩ := selected_binary m.declarations world lhs rhs _ d typed hl hr hd vd r
    exact ⟨c,d,hc,hd,tag,executed,vc,vd,ac,rc,ad,rd,oc,od⟩

end VastitasOracle.MidIR
