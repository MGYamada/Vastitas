import VastitasOracle.FiniteKleisliRoutes
import VastitasOracle.FiniteMonadEvaluation
import VastitasOracle.FiniteFunctions

/-! The canonical bind and compose function bodies specialize to three finite
lookups. Their Core evaluation uses the checked Monad and the two actual
input arrows in the declared order. -/
namespace VastitasOracle.FiniteMonadBind
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open VastitasOracle.FiniteKleisli

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
variable {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}

private def result (s : FiniteSort) : Core.Result := ⟨.finite s, none⟩

private def params (b : Fibers) (flipped : Bool) : List Core.Parameter :=
  if flipped then [⟨0, result b.next⟩, ⟨1, result b.first⟩]
  else [⟨0, result b.first⟩, ⟨1, result b.next⟩]

private def core (flipped : Bool) (b : Fibers) (owner cat arrowTable composition : DeclId)
    (mu : String) : Core.Term :=
  let mapped : Core.Term := .letE 2 (.variable (if flipped then 0 else 1) (result b.next))
    (.finiteLookup ⟨arrowTable,some owner,[b.next],b.mapped⟩ [2])
  let extended : Core.Term := .letE 4 (.finiteTag b.multiplication mu)
    (.letE 5 (.variable 3 (result b.mapped))
      (.finiteLookup ⟨composition,some cat,[b.multiplication,b.mapped],b.extension⟩ [4,5]))
  .letE 3 mapped (.letE 6 extended
    (.letE 7 (.variable 6 (result b.extension))
      (.letE 8 (.variable (if flipped then 1 else 0) (result b.first))
        (.finiteLookup ⟨composition,some cat,[b.extension,b.first],b.result⟩ [7,8]))))

set_option maxRecDepth 4096 in
private theorem emitted {c : Context checked fields m} {w x y : Obj m} {owner : DeclId}
    (r : Routes c owner w x y) (t : FiniteTemplate) (flipped : Bool)
    (inputs : t.inputs = abstractInputs flipped)
    (output : t.result = .monadHom 0 (.slot 1) (.action (.slot 3)))
    (body : t.body = abstractBody flipped)
    (ok : t.instantiate checked.resolved.declarations (key owner fields.category w.1 x.1 y.1) [0,1] = .ok (ps,res,term)) :
    term = core flipped (fibers c w x y) owner fields.category c.selected.functorFields.arrows
      c.selected.categoryFields.comp (mu c y).tag := by
  let indices := key owner fields.category w.1 x.1 y.1
  let b := fibers c w x y
  have sig : t.signature indices [0,1] checked.resolved.declarations.indexed =
      some (params b flipped, .finite b.result) := by
    cases flipped <;> simp [FiniteTemplate.signature, inputs, output, abstractInputs, TemplateType.realize,
      key, indices, b, params, fibers, result, r.selected, Endpoint.tag, guard,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, T_row c x, T_row c y]
  change (t.specialize checked.resolved.declarations indices [0,1] >>= _) = _ at ok
  cases specialized : t.specialize checked.resolved.declarations indices [0,1] with
  | error d => simp [specialized, bind, Except.bind] at ok
  | ok value =>
    simp [specialized, bind, Except.bind, pure, Except.pure] at ok
    rcases ok with ⟨rfl, rfl, rfl⟩
    unfold FiniteTemplate.specialize at specialized
    split at specialized
    next valid =>
      split at specialized
      next missing => simp [sig] at missing
      next ps ret eq =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (eq.symm.trans sig))
        rw [body] at specialized
        split at specialized
        next term n ran =>
          cases flipped <;> simp only [StateT.run, abstractBody, Bool.false_eq_true, ite_true, ite_false] at ran
          all_goals
            conv at ran => lhs; whnf
            split at ran <;> try contradiction
            rename_i _ _ pair firstStep
            conv at firstStep => lhs; whnf
            rw [r.mapSite] at firstStep
            conv at firstStep => lhs; whnf
            cases Option.some.inj firstStep
            conv at ran => lhs; whnf
            split at ran <;> try contradiction
            rename_i _ _ rest tailStep
            conv at tailStep => lhs; whnf
            split at tailStep <;> try contradiction
            rename_i _ _ ext extensionStep
            conv at extensionStep => lhs; whnf
            rw [r.declared] at extensionStep
            conv at extensionStep => lhs; whnf
            split at extensionStep <;> try contradiction
            rename_i _ _ component componentStep
            conv at componentStep => lhs; whnf
            rw [r.selected] at componentStep
            conv at componentStep => lhs; whnf
            simp [guard, T_row c y, mu_row c y] at componentStep
            conv at componentStep => lhs; whnf
            rw [T_row c (T c y)] at componentStep
            cases Option.some.inj componentStep
            conv at extensionStep => lhs; whnf
            erw [r.extendSite] at extensionStep
            conv at extensionStep => lhs; whnf
            cases Option.some.inj extensionStep
            conv at tailStep => lhs; whnf
            split at tailStep <;> try contradiction
            rename_i _ _ last lastStep
            conv at lastStep => lhs; whnf
            rw [r.declared] at lastStep
            conv at lastStep => lhs; whnf
            erw [r.resultSite] at lastStep
            cases Option.some.inj lastStep
            cases Option.some.inj tailStep
            cases Option.some.inj ran
            split at specialized
            · cases specialized; rfl
            · contradiction
        next => contradiction
    next => contradiction

open Core.Semantics

/-- For either declared argument order, evaluating the specialized Core returns
the Kleisli composite of the two supplied arrows. The three required execution
plans follow from the typechecking of this very instantiation. -/
theorem eval_instantiated_bind {c : Context checked fields m} {w x y : Obj m} {owner : DeclId}
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (t : FiniteTemplate) (flipped : Bool)
    (inputs : t.inputs = abstractInputs flipped)
    (output : t.result = .monadHom 0 (.slot 1) (.action (.slot 3)))
    (body : t.body = abstractBody flipped)
    (ok : t.instantiate checked.resolved.declarations (key owner fields.category w.1 x.1 y.1) [0,1] =
      .ok (ps,res,term))
    (first : Hom c w (T c x)) (next : Hom c x (T c y))
    (module : Core.Module) (environment : module.declarations = checked.resolved.declarations)
    (vs : Values)
    (firstArg : vs (if flipped then 1 else 0) = some (.finiteTag (fibers c w x y).first first.tag))
    (nextArg : vs (if flipped then 0 else 1) = some (.finiteTag (fibers c w x y).next next.tag))
    (fuel : Nat) :
    eval module (fuel+6) vs term = some (.finiteTag (fibers c w x y).result
      (Kleisli.bind (data c) first next).tag) := by
  obtain ⟨r⟩ := routes_of_instantiation c selected t flipped inputs output body ok
  rcases module with ⟨env,functions,main⟩
  dsimp at environment
  subst env
  have typed := (FiniteFunctions.instantiate_sound ok).2.2.2.2
  have shape := emitted r t flipped inputs output body ok
  rw [shape] at typed ⊢
  let b := fibers c w x y
  let mapSite : FiniteLookup := ⟨c.selected.functorFields.arrows,some owner,[b.next],b.mapped⟩
  let muSite : FiniteLookup := ⟨c.selected.categoryFields.comp,some fields.category,
    [b.multiplication,b.mapped],b.extension⟩
  let composeSite : FiniteLookup := ⟨c.selected.categoryFields.comp,some fields.category,
    [b.extension,b.first],b.result⟩
  have mapTyped := typed.2.1
  have extendTyped := typed.2.2.2.2.1
  have composeTyped := typed.2.2.2.2.2.2
  have mapExists : (mapSite.plan? checked.resolved.declarations.indexed).isSome = true :=
    mapTyped.2.2.2.2.1
  have muExists : (muSite.plan? checked.resolved.declarations.indexed).isSome = true :=
    extendTyped.2.2.2.2.2.2.2.1
  have composeExists : (composeSite.plan? checked.resolved.declarations.indexed).isSome = true :=
    composeTyped.2.2.2.2.2.2.2.1
  dsimp [mapSite,muSite,composeSite,b,fibers] at mapExists muExists composeExists
  obtain ⟨mapPlan, mapFound⟩ := Option.isSome_iff_exists.mp mapExists
  obtain ⟨muPlan, muFound⟩ := Option.isSome_iff_exists.mp muExists
  obtain ⟨composePlan, composeFound⟩ := Option.isSome_iff_exists.mp composeExists
  have mapped := FiniteMonadEvaluation.plan_map c r.selected next mapPlan
  have extended := FiniteCategoryExecution.plan_atKey_compose_total checked (mu c y) (map c next) muPlan
  have composed := FiniteCategoryExecution.plan_atKey_compose_total checked (comp c (mu c y) (map c next))
    first composePlan
  dsimp [comp] at composed
  cases flipped <;> simp [fibers] at firstArg nextArg <;>
    simp [core, fibers, eval, bindValue, readFiniteTags, guard, evalFiniteLookup,
      firstArg, nextArg, mapFound, muFound, composeFound,
      Kleisli.bind, Kleisli.extend, data, comp]
  all_goals
    simp [mapped, extended, composed]

/-- The ordinary after-before entry point gives mathematical Kleisli composition. -/
theorem eval_instantiated_compose {c : Context checked fields m} {w x y : Obj m} {owner : DeclId}
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (t : FiniteTemplate)
    (inputs : t.inputs = abstractInputs true)
    (output : t.result = .monadHom 0 (.slot 1) (.action (.slot 3)))
    (body : t.body = abstractBody true)
    (ok : t.instantiate checked.resolved.declarations (key owner fields.category w.1 x.1 y.1) [0,1] =
      .ok (ps,res,term))
    (after : Hom c x (T c y)) (before : Hom c w (T c x))
    (module : Core.Module) (environment : module.declarations = checked.resolved.declarations)
    (vs : Values) (afterArg : vs 0 = some (.finiteTag (fibers c w x y).next after.tag))
    (beforeArg : vs 1 = some (.finiteTag (fibers c w x y).first before.tag)) (fuel : Nat) :
    eval module (fuel+6) vs term = some (.finiteTag (fibers c w x y).result
      (Kleisli.compose (data c) after before).tag) :=
  eval_instantiated_bind selected t true inputs output body ok before after module environment vs beforeArg afterArg fuel

end VastitasOracle.FiniteMonadBind
