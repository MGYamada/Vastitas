import VastitasOracle.FiniteHom
import VastitasOracle.IndexedReverseCore
import VastitasOracle.IndexedAuthority

namespace VastitasOracle.FiniteFunctions
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource

/-- An actual successful instantiation agrees with the signature under its
nominal static substitution and its body has that result under the emitted
Core parameters. Even unused parameters have valid types and distinct symbols. -/
theorem instantiate_sound {t : FiniteTemplate} {env : Core.Declarations}
    {key : List StaticIndex} {symbols : List Nat} {params : List Core.Parameter}
    {result : Core.DataType} {term : Core.Term}
    (accepted : t.instantiate env key symbols = .ok (params, result, term)) :
    t.validKey env.indexed key = true ∧ t.signature key symbols env.indexed = some (params,result) ∧
    Core.Typing.ParametersValid env [] params ∧ term.result.type = result ∧
    Core.Typing.HasType env {} params term := by
  cases h : t.specialize env key symbols with
  | error d => simp [FiniteTemplate.instantiate, h, bind, Except.bind] at accepted
  | ok i =>
    simp [FiniteTemplate.instantiate, h, bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨rfl, rfl, rfl⟩ := accepted
    exact ⟨i.keyValid, i.signatureExact, i.parametersValid, i.resultExact, i.typed⟩

/-- The abstract Hom at three slots specializes to exactly the fiber of
the selected nominal model over those two endpoint tags. -/
theorem realize_hom {key : List StaticIndex}
    (model : key[c]? = some (.category owner))
    (src : key[x]? = some (.object owner source)) (dst : key[y]? = some (.object owner target)) :
    (TemplateType.hom c x y).realize key = some (.finite (.hom owner source target)) := by
  simp [TemplateType.realize, model, src, dst, guard]

/-- Recover the three actual slot values from a realized Hom. In particular,
equal endpoint spellings in another category cannot inhabit this result. -/
theorem realize_hom_iff {key : List StaticIndex} :
    (TemplateType.hom c x y).realize key = some (.finite (.hom owner source target)) ↔
    key[c]? = some (.category owner) ∧ key[x]? = some (.object owner source) ∧
    key[y]? = some (.object owner target) := by
  constructor
  · intro h
    unfold TemplateType.realize at h
    cases hc : key[c]? with
    | none => simp [hc] at h
    | some a =>
      cases a with
      | object => simp [hc] at h
      | monad => simp [hc] at h
      | category cat =>
        cases hx : key[x]? with
        | none => simp [hc, hx] at h
        | some b =>
          cases b with
          | category => simp [hc, hx] at h
          | monad => simp [hc, hx] at h
          | object cx src =>
            cases hy : key[y]? with
            | none => simp [hc, hx, hy] at h
            | some d =>
              cases d with
              | category => simp [hc, hx, hy] at h
              | monad => simp [hc, hx, hy] at h
              | object cy dst =>
                by_cases hcx : cx = cat <;> by_cases hcy : cy = cat <;>
                  simp_all [guard, failure, Alternative.failure]
  · rintro ⟨hm,hx,hy⟩
    exact realize_hom hm hx hy

open FunctionSource.Compiler

/-- A materialized specialization names a concrete owner/key in the compiler
and retains exactly the parameters, result and body obtained at that key. -/
def Materialized (input : Input) (entry : Prepared) (id : Nat) : Prop :=
  input.finiteInstances[(entry.definition.owner, entry.finiteKey)]? = some id ∧
    ∃ source template term, input.templates[entry.definition.owner]? = some (source,template) ∧
      entry.finiteBody = some term ∧
      template.instantiate input.body.declarations entry.finiteKey (List.range source.params.length) =
        .ok (entry.parameters,entry.result,term) ∧
      template.validKey input.body.declarations.indexed entry.finiteKey = true ∧
      Core.Typing.ParametersValid input.body.declarations [] entry.parameters ∧
      term.result.type = entry.result ∧ Core.Typing.HasType input.body.declarations {} entry.parameters term

theorem valid_finite_prepared_sound {input : Input} {entry : Prepared} {id : Nat}
    (accepted : validFinitePrepared input entry id = true) : Materialized input entry id := by
  cases found : input.templates[entry.definition.owner]? with
  | none => simp [validFinitePrepared, found] at accepted
  | some pair =>
    rcases pair with ⟨source,t⟩
    cases body : entry.finiteBody with
    | none => simp [validFinitePrepared, found, body] at accepted
    | some term =>
      cases made : t.instantiate input.body.declarations entry.finiteKey (List.range source.params.length) with
      | error d => simp [validFinitePrepared, found, body, made] at accepted
      | ok tuple =>
        rcases tuple with ⟨params,result,expected⟩
        simp only [validFinitePrepared, found, body, made, Id.run, pure, Bool.and_eq_true,
          beq_iff_eq, and_assoc] at accepted
        obtain ⟨_, _, _, _, _, selected, hp, hr, _, _, equal⟩ := accepted
        have ht := IndexedReverseCore.termEq_sound equal
        subst params result expected
        obtain ⟨valid, _, typedParams, output, typed⟩ := instantiate_sound made
        exact ⟨selected, source, t, term, found, body, made, valid, typedParams, output, typed⟩

/-- Every specialization in the public request's actual prepared table is an
exact nominal substitution and has a typed function in its all-body audit. -/
theorem wire_finite_specialization {raw : Lean.Json} (wire : ResourceSource.Wire.CheckedInput raw requireMain)
    {offset : Nat} {entry : Prepared}
    (found : wire.checked.pureProgram.compiler.input.prepared[
      wire.checked.pureProgram.lifted.definitions.size + offset]? = some entry) :
    Materialized wire.checked.pureProgram.compiler.input entry
      (wire.checked.pureProgram.lifted.definitions.size + offset) ∧
    ∃ function ∈ wire.checked.pureProgram.audit.lowered.module.functions, ∃ key,
      wire.checked.pureProgram.audit.lowered.origins[function.id]? = some key ∧
      key.definition = entry.definition.id ∧
      Core.Typing.FunctionTyped wire.checked.pureProgram.audit.lowered.module.declarations
        (Core.Typing.signatures wire.checked.pureProgram.audit.lowered.module) function := by
  have valid := wire.checked.pureProgram.preparation
  simp only [validPrepared, Bool.and_eq_true, List.all_eq_true] at valid
  have member : (entry,offset) ∈ (wire.checked.pureProgram.compiler.input.prepared.toList.drop
      wire.checked.pureProgram.lifted.definitions.size).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simpa only [List.getElem?_drop, Array.getElem?_toList] using found
  exact ⟨valid_finite_prepared_sound (valid.2.2 _ member),
    IndexedAuthority.definition_body_checked wire.checked.pureProgram entry (Array.mem_of_getElem? found)⟩

private def homResult (owner : DeclId) (x y : String) : Core.Result := ⟨.finite (.hom owner x y), none⟩

private def compositionBody (table owner : DeclId) (x y z : String) : Core.Term :=
  .letE 2 (.variable 0 (homResult owner y z))
    (.letE 3 (.variable 1 (homResult owner x y))
      (.finiteLookup ⟨table, some owner, [.hom owner y z, .hom owner x y], .hom owner x z⟩ [2, 3]))

private theorem instantiated_compose {t : FiniteTemplate} {env : Core.Declarations} {owner table : DeclId}
    {x y z : String} {rows : List (List String × String)}
    (params : t.inputs = [.hom 0 2 3, .hom 0 1 2])
    (result : t.result = .hom 0 1 3)
    (body : t.body = .compose 0 (.variable 0) (.variable 1))
    (projection : FiniteSort.composition? env.indexed owner (.hom owner y z) (.hom owner x y) =
      some (table, .hom owner x z, rows))
    (ok : t.instantiate env [.category owner, .object owner x, .object owner y, .object owner z] [0, 1] =
      .ok (ps, r, term)) :
    term = compositionBody table owner x y z := by
  let key := [StaticIndex.category owner, .object owner x, .object owner y, .object owner z]
  have sig : t.signature key [0, 1] env.indexed = some ([⟨0, homResult owner y z⟩, ⟨1, homResult owner x y⟩], .finite (.hom owner x z)) := by
    simp [FiniteTemplate.signature, params, result, key, TemplateType.realize, guard, homResult,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind]
  change (t.specialize env key [0, 1] >>= _) = _ at ok
  cases specialized : t.specialize env key [0, 1] with
  | error d => simp [specialized, bind, Except.bind] at ok
  | ok value =>
    simp [specialized, bind, Except.bind, pure, Except.pure] at ok
    rcases ok with ⟨rfl, rfl, rfl⟩
    unfold FiniteTemplate.specialize at specialized
    split at specialized
    next h =>
      split at specialized
      next no => simp [sig] at no
      next p ret eq =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (eq.symm.trans sig))
        rw [body] at specialized
        split at specialized
        next term n he =>
          simp [StateT.run, key, homResult] at he
          -- Reduce emission through its two variables up to the actual table lookup.
          conv at he => lhs; whnf
          rw [projection] at he
          change some (compositionBody table owner x y z, 4) = some (term, n) at he
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
          split at specialized
          · cases specialized; rfl
          · contradiction
        next => contradiction
    next h => contradiction
open Core.Semantics

/-- Evaluating the specialized composition body returns the mathematical
composite for any two arrows of the selected category. Core typing supplies
the lookup plan for these fibers. -/
theorem eval_instantiated_compose {t : FiniteTemplate} {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {model : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (after : FiniteHom.Hom model y z) (before : FiniteHom.Hom model x y)
    (mod : Core.Module) (environment : mod.declarations = checked.resolved.declarations)
    (params : t.inputs = [.hom 0 2 3, .hom 0 1 2])
    (result : t.result = .hom 0 1 3)
    (body : t.body = .compose 0 (.variable 0) (.variable 1))
    (projection : FiniteSort.composition? checked.resolved.declarations.indexed owner
      (.hom owner y z) (.hom owner x y) = some (table, .hom owner x z, rows))
    (ok : t.instantiate checked.resolved.declarations
      [.category owner, .object owner x, .object owner y, .object owner z] [0, 1] = .ok (ps, r, term))
    (vs : Values) (g : vs 0 = some (.finiteTag (.hom owner y z) after.tag))
    (f : vs 1 = some (.finiteTag (.hom owner x y) before.tag)) (fuel : Nat) :
    eval mod (fuel + 3) vs term = some (.finiteTag (.hom owner x z)
        (FiniteCategoryExecution.compose checked after before).tag) := by
  rcases mod with ⟨env, functions, main⟩
  dsimp at environment
  subst env
  have ht := (instantiate_sound ok).2.2.2.2
  have shape := instantiated_compose params result body projection ok
  rw [shape] at ht ⊢
  let site : FiniteLookup := ⟨table, some owner, [.hom owner y z, .hom owner x y], .hom owner x z⟩
  have existsPlan : (site.plan? checked.resolved.declarations.indexed).isSome = true :=
    ht.2.2.2.2.2.2.2.1
  obtain ⟨plan, selected⟩ := Option.isSome_iff_exists.mp existsPlan
  have row := FiniteCategoryExecution.plan_atKey_compose_total checked after before plan
  dsimp [site] at selected
  simp [compositionBody, eval, g, f, bindValue, evalFiniteLookup, selected,
    readFiniteTags, guard, row]
end VastitasOracle.FiniteFunctions
