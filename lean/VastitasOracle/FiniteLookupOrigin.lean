import VastitasOracle.ResourceSource

set_option autoImplicit false

namespace VastitasOracle.FiniteLookupOrigin
open VastitasKernel VastitasKernel.Indexed

/-- A direct lookup uses the declared rows verbatim. A projected lookup
uses the structure selected by the number of Hom arguments. -/
def OwnerMatches (s : FiniteLookup) (rows : List (List String × String)) (d : Declaration) : Prop :=
  match s.category, s.inputs, d with
  | none, _, .finiteTable domain range actual =>
    s.inputs = domain.map FiniteSort.carrier ∧ s.output = .carrier range ∧ rows = actual
  | some _, [], .finiteIso .. | some _, [_], .finiteMonad .. => True
  | some _, [_,_], .finiteCategory .. | some _, [_,_], .finiteOpposite .. => True
  | _, _, _ => False

private theorem owner_found {env : Environment} {s : FiniteLookup} (p : FiniteLookup.Plan env s) :
    ∃ d, lookup env (s.category.getD s.table) = some d ∧ OwnerMatches s p.rows d := by
  obtain ⟨table, category, inputs, output⟩ := s
  have h := p.selectedRows
  cases category with
  | none =>
    simp only [FiniteLookup.signature, bind, Option.bind_eq_some_iff] at h
    obtain ⟨decl, found, matched⟩ := h
    split at matched <;> try contradiction
    next domain range rows =>
      simp [guard, Option.bind_eq_some_iff] at matched
      obtain ⟨args, out, data⟩ := matched
      exact ⟨_,found, args, out.symm, data.symm⟩
  | some owner =>
    cases inputs with
    | nil =>
      simp only [FiniteLookup.signature, bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, chosen, _⟩ := h
      simp only [FiniteSort.isoArrow?, bind, Option.bind_eq_some_iff] at chosen
      obtain ⟨d, found, matched⟩ := chosen
      split at matched <;> try contradiction
      exact ⟨_, found, trivial⟩
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [FiniteLookup.signature, bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, chosen, _⟩ := h
        cases a <;> simp only [FiniteSort.monadMap?, bind, Option.bind_eq_some_iff, reduceCtorEq] at chosen
        obtain ⟨_, monad, _⟩ := chosen
        simp only [FiniteSort.monad?, bind, Option.bind_eq_some_iff] at monad
        obtain ⟨d, found, matched⟩ := monad
        split at matched <;> try contradiction
        exact ⟨_, found, trivial⟩
      | cons b more =>
        cases more with
        | cons => simp [FiniteLookup.signature] at h
        | nil =>
          simp only [FiniteLookup.signature, bind, Option.bind_eq_some_iff] at h
          obtain ⟨_, chosen, _⟩ := h
          cases a <;> cases b <;> simp only [FiniteSort.composition?, bind, Option.bind_eq_some_iff, reduceCtorEq] at chosen
          obtain ⟨_, _, _, selected, _⟩ := chosen
          simp only [FiniteSort.selected, bind, Option.bind_eq_some_iff] at selected
          obtain ⟨d, found, matched⟩ := selected
          split at matched <;> try contradiction
          all_goals exact ⟨_, found, trivial⟩

/-- The nominal owner read by the table plan resolves from a physical source
declaration to the very payload used in the returned Core. -/
theorem physical_authority {json main} (req : ResourceSource.Wire.CheckedInput json main)
    {env : Environment} (source : env = req.checked.pureProgram.compiled.core.module.declarations.indexed)
    {s : FiniteLookup} (p : FiniteLookup.Plan env s) :
    ∃ d, lookup env (s.category.getD s.table) = some d ∧
      OwnerMatches s p.rows d ∧ ResourceSource.PhysicalFiniteOrigin req ⟨s.category.getD s.table,d⟩ := by
  subst env
  obtain ⟨d, found, agrees⟩ := owner_found p
  refine ⟨d, found, agrees, ResourceSource.physical_origin_of_finite_entry req (List.mem_filter.mpr ⟨
    FiniteCategoryExecution.lookup_member found, ?_⟩)⟩
  unfold OwnerMatches at agrees
  split at agrees <;> first | rfl | contradiction

end VastitasOracle.FiniteLookupOrigin
