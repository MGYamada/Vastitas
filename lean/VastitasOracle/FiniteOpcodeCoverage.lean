import VastitasKernel.MidIR.Lower
import VastitasOracle.MidIR

set_option autoImplicit false

namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

/-- The optimization opcode retains the declared sort and tag. The execution
opcode indexes that sort's own enumeration and recovers the same Core value.
Both phases require zero operands, including for a dependent Hom fiber. -/
theorem finite_tag_constructor_coverage (module : Core.Module) (values : Values) (fuel : Nat)
    (c : FiniteSort) (tag : String) (tags : List String)
    (enumerated : FiniteSort.tags module.declarations.indexed c = some tags) (member : tag ∈ tags)
    (resolver : Resolver) (bad : Value) (rest : List Value) :
    let env := module.declarations.indexed
    let opt := Opcode.finiteTag c tag
    let exe := Opcode.finiteOrdinal c (tags.idxOf tag)
    AppendsNullary (.finiteTag c tag) opt ∧ (``Core.Term.finiteTag, opt.tag) = finiteTagRegistryRow ∧
    opt.execute env = some exe ∧ opt.valid env = true ∧ exe.valid env = true ∧
    opt.operands = [] ∧ exe.operands = [] ∧
    Ty.ofCore (Core.Term.finiteTag c tag).result.type = some opt.result ∧ exe.result = opt.result ∧
    denote env opt [] resolver = eval module (fuel+1) values (.finiteTag c tag) ∧
    (∀ args, denote env exe args resolver = denote env opt args resolver) ∧
    denote env opt (bad :: rest) resolver = none := by
  dsimp only
  have bound := List.idxOf_lt_length_of_mem member
  have atTag : tags[tags.idxOf tag]? = some tag := by
    rw [List.getElem?_eq_getElem bound, List.getElem_idxOf]
  have executed : (Opcode.finiteTag c tag).execute module.declarations.indexed =
      some (.finiteOrdinal c (tags.idxOf tag)) := by simp [Opcode.execute, enumerated, atTag]
  refine ⟨appends_finite_tag c tag, rfl, executed, ?_, ?_, rfl, rfl, rfl, rfl, rfl,
    fun args => execute_denote_with resolver _ _ _ args executed, rfl⟩
  · simp [Opcode.valid, enumerated, member]
  · simp [Opcode.valid, enumerated, bound]

theorem finite_tag_missing_rejected (env : Environment) (c : FiniteSort) (tag : String)
    (missing : (FiniteSort.tags env c).any (·.contains tag) = false) :
    (Opcode.finiteTag c tag).valid env = false ∧ (Opcode.finiteTag c tag).execute env = none := by
  refine ⟨missing, ?_⟩
  cases h : FiniteSort.tags env c with
  | none => simp [Opcode.execute, h]
  | some tags =>
    have absent : tag ∉ tags := by simpa [h] using missing
    simp [Opcode.execute, h, List.idxOf_eq_length absent]

/-- The site includes the selected table, owner, argument sorts and result
fiber. Lowering preserves ordered operands, including repeated references.
The execution phase and Core both read that site's checked table plan. -/
theorem finite_lookup_constructor_coverage (module : Core.Module) (site : FiniteLookup) (symbols : List Nat)
    (values : Values) (args : List Value) (readArgs : symbols.mapM values = some args)
    (resolver : Resolver) (fuel : Nat) :
    let env := module.declarations.indexed
    let opt := Opcode.lookupTag site
    let exe := Opcode.lookupOrdinal site
    AppendsLookup site symbols ∧ (``Core.Term.finiteLookup, opt.tag) = lookupRegistryRow ∧
    opt.execute env = some exe ∧ opt.valid env = (site.plan? env).isSome ∧ exe.valid env = opt.valid env ∧
    opt.operands = site.inputs.map Ty.finite ∧ exe.operands = opt.operands ∧
    Ty.ofCore (Core.Term.finiteLookup site symbols).result.type = some opt.result ∧ exe.result = opt.result ∧
    denote env opt args resolver = eval module (fuel+1) values (.finiteLookup site symbols) ∧
    (∀ supplied, denote env exe supplied resolver = denote env opt supplied resolver) := by
  refine ⟨appends_lookup site symbols, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun _ => rfl⟩
  exact lookup_from_core _ _ _ _ _ readArgs

private theorem read_resolved_slots (ctx : List (Nat × Ref)) (slots : Ref → Option Value)
    (symbols : List Nat) :
    (symbols.mapM (fun n => ctx.lookup n) >>= fun refs => refs.mapM slots) =
      symbols.mapM (fun n => (ctx.lookup n).bind slots) := by
  induction symbols with
  | nil => rfl
  | cons sym tail ih =>
    cases head : ctx.lookup sym with
    | none => simp [List.mapM_cons, head]
    | some ref =>
      cases remaining : tail.mapM (fun n => ctx.lookup n) <;> cases value : slots ref <;>
        simp [List.mapM_cons, head, remaining, value, ← ih]

/-- Read exactly the SSA references supplied to the appended lookup. A missing
symbol or unreadable slot produces the same failure in the Core evaluator. -/
theorem finite_lookup_slots (module : Core.Module) (site : FiniteLookup) (symbols : List Nat)
    (ctx : List (Nat × Ref)) (slots : Ref → Option Value) (resolver : Resolver) (fuel : Nat) :
    (do let refs ← symbols.mapM (fun n => ctx.lookup n)
        let args ← refs.mapM slots
        denote module.declarations.indexed (.lookupOrdinal site) args resolver) =
    eval module (fuel+1) (fun n => (ctx.lookup n).bind slots) (.finiteLookup site symbols) := by
  change (symbols.mapM (fun n => ctx.lookup n) >>= fun (refs : List Ref) =>
    refs.mapM slots >>= lookupValue module.declarations.indexed site) = evalFiniteLookup _ _ _ _
  rw [← bind_assoc, read_resolved_slots, lookup_from_core_partial]

theorem finite_lookup_wrong_sort (env : Environment) (site : FiniteLookup)
    (expected actual : FiniteSort) (rest : List FiniteSort) (inputs : site.inputs = expected :: rest)
    (wrong : actual ≠ expected) (tag : String) (tail : List Value) (resolver : Resolver) :
    denote env (.lookupTag site) (.finiteTag actual tag :: tail) resolver = none ∧
    denote env (.lookupOrdinal site) (.finiteTag actual tag :: tail) resolver = none := by
  have key : lookupKey site.inputs (.finiteTag actual tag :: tail) = none := by
    simp [inputs, lookupKey, guard, wrong]
  have noRow : lookupValue env site (.finiteTag actual tag :: tail) = none := by
    cases plan : site.plan? env <;> simp [lookupValue, plan, key]
  exact ⟨noRow, noRow⟩

end VastitasOracle.MidIR
