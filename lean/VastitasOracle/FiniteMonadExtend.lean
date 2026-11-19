import VastitasOracle.FiniteMonadBind

set_option autoImplicit false

namespace VastitasOracle.FiniteMonadExtend
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.FunctionSource
open FiniteKleisli Core.Semantics

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
    {fields : MonadFields DeclId} {m : Indexed.FiniteMonads.Model}

private def result (s : FiniteSort) : Core.Result := ⟨.finite s, none⟩

private def emitted (cat owner arrows composition : DeclId) (x tx ty tty component : String) : Core.Term :=
  let input := FiniteSort.hom cat x ty
  let mapped := FiniteSort.hom cat tx tty
  let mult := FiniteSort.hom cat tty ty
  let target := FiniteSort.hom cat tx ty
  let mapTerm := Core.Term.letE 1 (.variable 0 (result input))
    (.finiteLookup ⟨arrows, some owner, [input], mapped⟩ [1])
  .letE 2 (.finiteTag mult component) (.letE 3 mapTerm
    (.finiteLookup ⟨composition, some cat, [mult,mapped], target⟩ [2,3]))

private def body := TemplateExpr.monadCompose 0 (.component 0 2 true) (.monadMap 0 (.variable 0))

set_option maxRecDepth 4096 in
/-- A successful specialization of the extension template selects the map
and multiplication of its checked Monad, followed by base composition. -/
private theorem shape {owner : DeclId} (c : Context checked fields m) (x y : Obj m)
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (t : FiniteTemplate)
    (inputs : t.inputs = [.monadHom 0 (.slot 1) (.action (.slot 2))])
    (output : t.result = .monadHom 0 (.action (.slot 1)) (.action (.slot 2)))
    (expr : t.body = body) {ps : List Core.Parameter} {res : Core.DataType} {term : Core.Term}
    (ok : t.instantiate checked.resolved.declarations
      [.monad owner,.object fields.category x.1,.object fields.category y.1] [0] = .ok (ps,res,term)) :
    term = emitted fields.category owner c.selected.functorFields.arrows c.selected.categoryFields.comp
      x.1 (T c x).1 (T c y).1 (T c (T c y)).1 (mu c y).tag := by
  let key := [StaticIndex.monad owner,.object fields.category x.1,.object fields.category y.1]
  let env := checked.resolved.declarations.indexed
  let cat := fields.category
  have sig : t.signature key [0] checked.resolved.declarations.indexed = some ([⟨0, result (.hom cat x.1 (T c y).1)⟩],
      .finite (.hom cat (T c x).1 (T c y).1)) := by
    simp [FiniteTemplate.signature, inputs, output, TemplateType.realize, selected, T_row c x, T_row c y,
      Endpoint.tag, guard, key, cat, result, List.mapM_cons, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind]
  obtain ⟨schema, decl⟩ := FiniteMonadUnit.selected_declaration selected
  change (t.specialize checked.resolved.declarations key [0] >>= _) = _ at ok
  cases sp : t.specialize checked.resolved.declarations key [0] with
  | error e => simp [sp, bind, Except.bind] at ok
  | ok v =>
    simp [sp, bind, Except.bind, pure, Except.pure] at ok
    rcases ok with ⟨rfl,rfl,rfl⟩
    unfold FiniteTemplate.specialize at sp
    split at sp <;> try contradiction
    split at sp
    next missing => simp [sig] at missing
    next params ret found =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans sig))
      rw [expr] at sp
      split at sp <;> try contradiction
      next term n h =>
        simp only [StateT.run, body] at h
        conv at h => lhs; whnf
        rw [decl] at h
        conv at h => lhs; whnf
        split at h <;> try contradiction
        rename_i _ _ component compStep
        conv at compStep => lhs; whnf
        rw [selected] at compStep
        conv at compStep => lhs; whnf
        simp [guard, T_row c y, mu_row c y] at compStep
        conv at compStep => lhs; whnf
        rw [T_row c (T c y)] at compStep
        cases Option.some.inj compStep
        conv at h => lhs; whnf
        split at h <;> try contradiction
        rename_i _ _ mapped mapStep
        cases hm : FiniteSort.monadMap? env owner (.hom cat x.1 (T c y).1) with
        | none =>
          conv at mapStep => lhs; whnf
          rw [hm] at mapStep
          contradiction
        | some route =>
          obtain ⟨tab,out,rows⟩ := route
          obtain ⟨rfl,rfl⟩ := FiniteMonadBind.map_target c selected hm
          conv at mapStep => lhs; whnf
          rw [hm] at mapStep
          conv at mapStep => lhs; whnf
          cases Option.some.inj mapStep
          cases hc : FiniteSort.composition? env cat (.hom cat (T c (T c y)).1 (T c y).1)
              (.hom cat (T c x).1 (T c (T c y)).1) with
          | none =>
            conv at h => lhs; whnf
            erw [hc] at h
            contradiction
          | some route =>
            obtain ⟨t,o,rs⟩ := route
            obtain ⟨rfl,rfl⟩ := FiniteMonadBind.composition_target c hc
            conv at h => lhs; whnf
            erw [hc] at h
            cases Option.some.inj h
            split at sp <;> try contradiction
            cases sp
            rfl

/-- The Core produced by the ordinary public extension body evaluates to
the extension arrow of the selected Monad on every member of the input Hom. -/
theorem eval_instantiated_extend {owner : DeclId} (c : Context checked fields m) {x y : Obj m}
    (f : Hom c x (T c y))
    (selected : FiniteSort.monad? checked.resolved.declarations.indexed owner = some (fields,m))
    (t : FiniteTemplate)
    (inputs : t.inputs = [.monadHom 0 (.slot 1) (.action (.slot 2))])
    (output : t.result = .monadHom 0 (.action (.slot 1)) (.action (.slot 2)))
    (expr : t.body = .monadCompose 0 (.component 0 2 true) (.monadMap 0 (.variable 0)))
    {ps : List Core.Parameter} {res : Core.DataType} {term : Core.Term}
    (ok : t.instantiate checked.resolved.declarations
      [.monad owner,.object fields.category x.1,.object fields.category y.1] [0] = .ok (ps,res,term))
    (module : Core.Module) (environment : module.declarations = checked.resolved.declarations)
    (vs : Values) (arg : vs 0 = some (.finiteTag (.hom fields.category x.1 (T c y).1) f.tag)) (fuel : Nat) :
    eval module (fuel+4) vs term = some (.finiteTag (.hom fields.category (T c x).1 (T c y).1)
      ((triple c).extend f).tag) := by
  obtain ⟨env,fs,entry⟩ := module
  dsimp at environment
  subst env
  have typed := (FiniteFunctions.instantiate_sound ok).2.2.2.2
  rw [shape c x y selected t inputs output expr ok] at typed ⊢
  obtain ⟨mp, hm⟩ := Option.isSome_iff_exists.mp typed.2.2.2.2.1.2.2.2.2.1
  obtain ⟨cp, hc⟩ := Option.isSome_iff_exists.mp typed.2.2.2.2.2.2.2.1
  have mapRow := FiniteMonadEvaluation.plan_map c selected f mp
  have composeRow := FiniteCategoryExecution.plan_atKey_compose_total checked (mu c y) (map c f) cp
  simp [emitted, eval, arg, bindValue, evalFiniteLookup, hm, hc, readFiniteTags, guard,
    mapRow, composeRow, triple, Kleisli.Triple.fromMonad, Kleisli.extend, data, comp, result]

end VastitasOracle.FiniteMonadExtend
