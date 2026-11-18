import VastitasOracle.FiniteMonadEvaluation
import VastitasOracle.FiniteFunctions

/-! Evaluation of the actual Core emitted for the unit and lift templates of
the finite Monad library, on the exact category, object action and component
tables of the selected public Monad. -/
namespace VastitasOracle.FiniteMonadUnit
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open FiniteKleisli
open Core.Semantics

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
  {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}
  {owner : DeclId} (c : Context checked fields m)
  (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields, m))

private theorem lift_some (v : α) (n : Nat) :
    (liftM (some v) : StateT Nat Option α) n = some (v,n) := rfl

include selected

/-- Instantiating the ordinary nullary unit function with the selected Monad
and object emits the corresponding component as a typed Core tag. -/
theorem eval_instantiated_unit {t : FiniteTemplate} (x : Obj m)
    (inputs : t.inputs = []) (result : t.result = .monadHom 0 (.slot 1) (.action (.slot 1)))
    (body : t.body = .component 0 1 false)
    (ok : t.instantiate checked.resolved.declarations [.monad owner, .object fields.category x.1] [] =
      .ok (ps, r, term)) (module : Core.Module) (vs : Values) (fuel : Nat) :
    eval module (fuel + 1) vs term =
      some (.finiteTag (.hom fields.category x.1 (T c x).1) (Kleisli.unit (data c) x).tag) := by
  let key := [StaticIndex.monad owner, .object fields.category x.1]
  have sig : t.signature key [] checked.resolved.declarations.indexed = some
      ([], .finite (.hom fields.category x.1 (T c x).1)) := by
    simp [FiniteTemplate.signature, inputs, result, TemplateType.realize, selected, Endpoint.tag,
      key, guard, T_row c x]
  change (t.specialize checked.resolved.declarations key [] >>= _) = _ at ok
  cases specialized : t.specialize checked.resolved.declarations key [] with
  | error d => simp [specialized, bind, Except.bind] at ok
  | ok val =>
    simp [specialized, bind, Except.bind, pure, Except.pure] at ok
    rcases ok with ⟨rfl,rfl,rfl⟩
    unfold FiniteTemplate.specialize at specialized
    split at specialized <;> try contradiction
    split at specialized
    next nope => simp [sig] at nope
    next params ret found =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans sig))
      rw [body] at specialized
      split at specialized <;> try contradiction
      next term n emitted =>
        conv at emitted => lhs; whnf
        rw [selected] at emitted
        conv at emitted => lhs; whnf
        simp [guard, T_row c x, eta_row c x] at emitted
        obtain ⟨rfl,rfl⟩ := emitted
        split at specialized <;> try contradiction
        cases specialized
        rfl


theorem selected_declaration :
    ∃ schema, lookup checked.resolved.declarations.indexed owner = some (.finiteMonad schema fields) := by
  unfold FiniteSort.monad? at selected
  generalize h : lookup checked.resolved.declarations.indexed owner = d at selected
  obtain _ | d := d
  · contradiction
  cases d <;> try contradiction
  rename_i schema s
  change (do let model ← Indexed.FiniteMonads.model (Indexed.FiniteCategories.view _) schema s; pure (s,model)) = some (fields,m) at selected
  generalize hm : Indexed.FiniteMonads.model (Indexed.FiniteCategories.view checked.resolved.declarations.indexed) schema s = model at selected
  obtain _ | model := model
  · contradiction
  cases selected
  exact ⟨schema, rfl⟩

private def liftTerm (table category : DeclId) (x y ty component : String) : Core.Term :=
  .letE 1 (.finiteTag (.hom category y ty) component)
    (.letE 2 (.variable 0 ⟨.finite (.hom category x y),none⟩)
      (.finiteLookup ⟨table,some category,[.hom category y ty,.hom category x y],.hom category x ty⟩ [1,2]))

private theorem emitted_lift {t : FiniteTemplate} (x y : Obj m)
    (inputs : t.inputs = [.monadHom 0 (.slot 1) (.slot 2)])
    (result : t.result = .monadHom 0 (.slot 1) (.action (.slot 2)))
    (body : t.body = .monadCompose 0 (.component 0 2 false) (.variable 0))
    (ok : t.instantiate checked.resolved.declarations
        [.monad owner, .object fields.category x.1, .object fields.category y.1] [0] = .ok (ps,r,term)) :
    ∃ table, term = liftTerm table fields.category x.1 y.1 (T c y).1 (eta c y).tag := by
  let key := [StaticIndex.monad owner, .object fields.category x.1, .object fields.category y.1]
  have sig : t.signature key [0] checked.resolved.declarations.indexed = some
      ([⟨0,⟨.finite (.hom fields.category x.1 y.1),none⟩⟩], .finite (.hom fields.category x.1 (T c y).1)) := by
    simp [FiniteTemplate.signature, inputs, result, TemplateType.realize, selected, Endpoint.tag,
      key, guard, T_row c y, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind]
  obtain ⟨_, declared⟩ := selected_declaration selected
  change (t.specialize checked.resolved.declarations key [0] >>= _) = _ at ok
  cases specialized : t.specialize checked.resolved.declarations key [0] with
  | error d => simp [specialized, bind, Except.bind] at ok
  | ok val =>
    simp [specialized, bind, Except.bind, pure, Except.pure] at ok
    rcases ok with ⟨rfl,rfl,rfl⟩
    unfold FiniteTemplate.specialize at specialized
    split at specialized <;> try contradiction
    split at specialized
    next nope => simp [sig] at nope
    next params ret found =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans sig))
      rw [body] at specialized
      split at specialized <;> try contradiction
      next term n emitted =>
        simp! [StateT.run, StateT.bind, StateT.pure, lift_some, bind, pure, guard,
          Core.Term.result, key, declared, selected, T_row c y, eta_row c y] at emitted
        cases projection : FiniteSort.composition? checked.resolved.declarations.indexed fields.category
              (.hom fields.category y.1 (T c y).1) (.hom fields.category x.1 y.1) with
        | none =>
          conv at projection => lhs; simp [FiniteSort.composition?, guard]
          rw [projection] at emitted
          contradiction
        | some route =>
          obtain ⟨table,out,rows⟩ := route
          have range : out = .hom fields.category x.1 (T c y).1 := by
            have h := projection
            simp [FiniteSort.composition?, guard, Option.bind_eq_some_iff] at h
            grind
          subst out
          conv at projection => lhs; simp [FiniteSort.composition?, guard]
          rw [projection] at emitted
          change some (liftTerm table fields.category x.1 y.1 (T c y).1 (eta c y).tag,3) = some (term,n) at emitted
          cases emitted
          split at specialized <;> try contradiction
          cases specialized
          exact ⟨table,rfl⟩

/-- The evaluator on the actual specialized lift composes the selected unit
at the target after the supplied ordinary arrow. -/
theorem eval_instantiated_lift {t : FiniteTemplate} {x y : Obj m} (f : Hom c x y)
    (inputs : t.inputs = [.monadHom 0 (.slot 1) (.slot 2)])
    (result : t.result = .monadHom 0 (.slot 1) (.action (.slot 2)))
    (body : t.body = .monadCompose 0 (.component 0 2 false) (.variable 0))
    (ok : t.instantiate checked.resolved.declarations
        [.monad owner, .object fields.category x.1, .object fields.category y.1] [0] = .ok (ps,r,term))
    (module : Core.Module) (environment : module.declarations = checked.resolved.declarations)
    (vs : Values) (arg : vs 0 = some (.finiteTag (.hom fields.category x.1 y.1) f.tag)) (fuel : Nat) :
    eval module (fuel+3) vs term =
      some (.finiteTag (.hom fields.category x.1 (T c y).1) (Kleisli.lift (data c) f).tag) := by
  rcases module with ⟨env,functions,main⟩
  dsimp at environment
  subst env
  have typed := (FiniteFunctions.instantiate_sound ok).2.2.2.2
  obtain ⟨table,shape⟩ := emitted_lift c selected x y inputs result body ok
  rw [shape] at typed ⊢
  let site : FiniteLookup := ⟨table,some fields.category,
    [.hom fields.category y.1 (T c y).1,.hom fields.category x.1 y.1], .hom fields.category x.1 (T c y).1⟩
  have existsPlan : (site.plan? checked.resolved.declarations.indexed).isSome = true :=
    typed.2.2.2.2.2.2.2.1
  obtain ⟨plan,chosen⟩ := Option.isSome_iff_exists.mp existsPlan
  have row := FiniteCategoryExecution.plan_atKey_compose_total checked (eta c y) f plan
  dsimp [site] at chosen
  simp [liftTerm, eval, arg, bindValue, evalFiniteLookup, chosen, readFiniteTags, guard, row,
    Kleisli.lift, Kleisli.unit, data, comp]

end VastitasOracle.FiniteMonadUnit
