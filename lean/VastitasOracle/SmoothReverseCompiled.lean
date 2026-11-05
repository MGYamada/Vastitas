import VastitasOracle.IndexedReverseCore
import VastitasOracle.SmoothReverseCore

set_option autoImplicit false

/-! Compiled reverse Core computes the reverse pass of its sites (#623).

`SmoothReverseCore` states what the Core of a site evaluates to under premises
about the module, and `IndexedReverseCore` that a compiled module lists the
generated function and the declarations of every entry. This module
discharges the premises for every entry of a compiled module
(`Reverse.Compiled`), from the definitions of `resolve`, `stepsOf`,
`compileSite` and `generate`:

- `entry_well_formed`: every premise of `SmoothReverseCore` about the module
  and the entry. The generated function and every declaration of the entry
  are found by their names, and the seed of a differential is over a fiber
  family; the site has a step; the map type of every declared step names two
  objects (`StepFormed`); and every declared step is a declaration of the
  compiled module whose derivative rule is `morphism` with the step's map
  (`MorphismsDeclared`). `resolve` reads a declared leaf only through that
  rule, `stepsOf` builds its map type from two objects, `compileSite` requires
  a step, and the compiled module keeps the source declarations.
- `compiled_saved_entry`, `compiled_recomputed_entry`: a call of the generated
  function of an entry, on arguments that evaluate to one smooth map per
  opaque step, the points and a covector, evaluates to the runtime pullback
  along the chain of the step programs, with saved points in the residual
  relation for a saved site. `compiled_saved_entry_cot` and
  `compiled_recomputed_entry_cot` give its value in coordinates; they use the
  chain rule (`SmoothCalculus.backward_eq_cot`), the others do not.
- `public_wire_entries`, `legacy_wire_entries`, `public_resource_entries` and
  `public_pure_entry_computes`: on every public path (protocols 2-6, 7 and
  8/9), every entry of the compiled modules of the accepted certificate, and of
  the module that the pure emit path generates, satisfies these
  (`EntryComputes`).

The premises that stay are facts about the arguments: one value per opaque
step (`count`), composable programs (`Composable`) and, for a saved site, the
residual relation of the points. The theorems do not prove that consecutive
steps share their objects (the target object of each map is the source object
of the next); they do not need it, since they hold for every list of
programs. They concern checked Core, not the generated text or native code. -/

namespace VastitasOracle.SmoothReverseCompiled

open VastitasKernel.Indexed (Variance DeclId ObjectRef)
open VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics (Values)
open VastitasKernel.Indexed.Core.Reverse
open VastitasKernel.SmoothRuntime (Program FiberValue Fiber pullback coordinates)
open VastitasOracle.IndexedEvaluation (Evaluates ArgumentsEvaluate)
open VastitasOracle.SmoothReverseCore

/-! ## The maps that `resolve` reads -/

/-- Every declared leaf of a tree is a declaration whose derivative rule is
`morphism` with the leaf's map. -/
def TreeDeclared (env : Declarations) : Tree → Prop
  | .declared _ morphism map => ruleOf env morphism = .morphism map
  | .opaque _ => True
  | .node after before => TreeDeclared env after ∧ TreeDeclared env before

theorem charge_tree {tree tree' : Tree} {budget rest : Nat} (charged : Tree.charge tree budget = some (tree', rest)) :
    tree' = tree := by
  unfold Tree.charge at charged
  split at charged
  · cases charged
  · exact (Prod.mk.inj (Option.some.inj charged)).1.symm

theorem charge_opaque {env : Declarations} {term : Term} {tree : Tree} {budget rest : Nat}
    (charged : Tree.charge (.opaque term) budget = some (tree, rest)) : TreeDeclared env tree := by
  rw [charge_tree charged]
  trivial

/-- `resolve` reads a declared leaf only through its derivative rule. -/
theorem resolve_declared (env : Declarations) (defs : Defs) :
    ∀ (fuel budget : Nat) (term : Term) {tree : Tree} {rest : Nat},
      resolve env defs fuel budget term = some (tree, rest) → TreeDeclared env tree
  | 0, _, _, _, _, resolved => by
    rw [resolve] at resolved
    exact charge_opaque resolved
  | fuel + 1, budget, term, tree, rest, resolved => by
    have recurse : ∀ (budget : Nat) (term : Term) {tree : Tree} {rest : Nat},
        resolve env defs fuel budget term = some (tree, rest) → TreeDeclared env tree :=
      fun budget term => resolve_declared env defs fuel budget term
    rw [resolve] at resolved
    split at resolved
    · split at resolved
      · rw [charge_tree resolved]
        simp only [TreeDeclared]
        assumption
      · split at resolved
        · rename_i first second _ _
          cases readFirst : resolve env defs fuel budget first with
          | none => simp [readFirst] at resolved
          | some pair =>
            obtain ⟨firstTree, firstRest⟩ := pair
            cases readSecond : resolve env defs fuel firstRest second with
            | none => simp [readFirst, readSecond] at resolved
            | some pair =>
              obtain ⟨secondTree, secondRest⟩ := pair
              simp only [readFirst, readSecond, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at resolved
              obtain ⟨rfl, -⟩ := resolved
              exact ⟨recurse _ _ readFirst, recurse _ _ readSecond⟩
        · exact charge_opaque resolved
      · exact charge_opaque resolved
    · split at resolved
      · split at resolved
        · split at resolved
          · cases resolved
            exact recurse _ _ (by assumption)
          · exact charge_opaque resolved
        · exact charge_opaque resolved
      · exact charge_opaque resolved
    · exact charge_opaque resolved

theorem leaves_declared {env : Declarations} : ∀ {tree : Tree}, TreeDeclared env tree →
    ∀ leaf ∈ tree.leaves, TreeDeclared env leaf
  | .declared _ _ _, declared, leaf, member => by
    rw [List.mem_singleton.mp member]
    exact declared
  | .opaque _, declared, leaf, member => by
    rw [List.mem_singleton.mp member]
    exact declared
  | .node _ _, declared, leaf, member => by
    rcases List.mem_append.mp member with member | member
    · exact leaves_declared declared.2 leaf member
    · exact leaves_declared declared.1 leaf member

theorem mapM_some_mem {α β : Type} {f : α → Option β} : ∀ {as : List α} {bs : List β},
    as.mapM f = some bs → ∀ b ∈ bs, ∃ a ∈ as, f a = some b
  | [], bs, mapped, b, member => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at mapped
    subst mapped
    cases member
  | a :: as, bs, mapped, b, member => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at mapped
    obtain ⟨head, found, rest, mappedRest, rfl⟩ := mapped
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨a, List.mem_cons_self, found⟩
    · obtain ⟨a', member', found'⟩ := mapM_some_mem mappedRest b member
      exact ⟨a', List.mem_cons_of_mem a member', found'⟩

/-- The steps that `stepsOf` reads from declared leaves: every declared step
names two objects in its map type and carries the morphism of its leaf. -/
theorem stepsOf_declared {env : Declarations} {smooth : DeclId} {leaves : List Tree} {steps : List Step}
    (read : stepsOf smooth leaves = some steps) (declared : ∀ leaf ∈ leaves, TreeDeclared env leaf) :
    ∀ step ∈ steps, StepFormed step ∧ ∀ morphism application map,
      step.kind = .declared morphism application map → ruleOf env morphism = .morphism map := by
  intro step member
  obtain ⟨leaf, leafMember, built⟩ := mapM_some_mem read step member
  have leafDeclared := declared leaf leafMember
  cases leaf with
  | declared call morphism map =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at built
    obtain ⟨⟨source, target⟩, _, built⟩ := built
    simp only [Option.some.injEq] at built
    subst built
    refine ⟨fun _ _ _ kind => ?_, fun _ _ _ kind => ?_⟩
    · cases kind
      exact ⟨.global source, .global target, rfl⟩
    · cases kind
      exact leafDeclared
  | «opaque» value =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at built
    obtain ⟨⟨source, target⟩, _, built⟩ := built
    simp only [Option.some.injEq] at built
    subst built
    exact ⟨fun _ _ _ kind => (by cases kind), fun _ _ _ kind => (by cases kind)⟩
  | node => cases built

/-! ## What `compileSite` records -/

/-- The facts of an entry that `compileSite` establishes against the
declarations `env` of the source module: the site has a step, every declared
step names two objects, and every declared step is a declaration with
derivative rule `morphism` and the step's map. -/
structure SiteFormed (env : Declarations) (entry : Entry) : Prop where
  nonempty : entry.site.steps ≠ []
  formed : ∀ step ∈ entry.site.steps, StepFormed step
  morphisms : ∀ step ∈ entry.site.steps, ∀ morphism application map,
    step.kind = .declared morphism application map → ruleOf env morphism = .morphism map

/-- A compiled site appends one entry to the ledger, and the entry is formed. -/
theorem compileSite_entry {env : Declarations} {defs : Defs} {state : State} {id : DeclId}
    {arguments : List Term} {result : Result} {term : Term} {state' : State}
    (compiled : compileSite env defs state id arguments result = some (term, state')) :
    ∃ entry, state'.entries = state.entries ++ [entry] ∧ SiteFormed env entry := by
  unfold compileSite at compiled
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨⟨map, point, seed, mode⟩, -, compiled⟩ := compiled
  simp only at compiled
  obtain ⟨⟨smooth, origin, object⟩, -, compiled⟩ := compiled
  simp only at compiled
  obtain ⟨cotangent, -, compiled⟩ := compiled
  obtain ⟨steps, read, compiled⟩ := compiled
  obtain ⟨⟨⟩, nonempty, compiled⟩ := compiled
  obtain ⟨⟨⟩, -, compiled⟩ := compiled
  obtain ⟨⟨⟩, -, compiled⟩ := compiled
  have notEmpty : steps ≠ [] := by
    have holds : (!steps.isEmpty) = true := by
      unfold guard at nonempty
      split at nonempty
      · assumption
      · cases nonempty
    intro empty
    subst empty
    simp at holds
  have stepsDeclared : ∀ step ∈ steps, StepFormed step ∧ ∀ morphism application map,
      step.kind = .declared morphism application map → ruleOf env morphism = .morphism map := by
    revert read
    split
    · intro read
      exact stepsOf_declared read (leaves_declared (resolve_declared env defs _ _ _ (by assumption)))
    · intro read
      exact stepsOf_declared read (leaves_declared (tree := .opaque map) trivial)
  refine ⟨⟨state.entries.length, state.scope, state.caller, state.base + state.entries.length,
    ⟨smooth, cotangent, origin, steps, mode⟩, if seed.isSome then .operand else .unit⟩, ?_,
    ⟨notEmpty, fun step member => (stepsDeclared step member).1, fun step member => (stepsDeclared step member).2⟩⟩
  split at compiled
  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at compiled
    obtain ⟨-, rfl⟩ := compiled
    rfl
  · cases compiled
  · split at compiled <;>
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at compiled
      obtain ⟨-, rfl⟩ := compiled
      rfl

/-- Every entry of a ledger is formed against `env`. -/
def EntriesFormed (env : Declarations) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, SiteFormed env entry

/-! ## The ledger of `generate` -/

/-- The rewriting appends only formed entries to the ledger. -/
theorem rewrite_formed (env : Declarations) (term : Term) :
    ∀ (defs : Defs) (state : State), EntriesFormed env state.entries →
      EntriesFormed env (rewrite env defs state term).2.entries := by
  induction term using Term.rec (motive_2 := fun terms => ∀ (defs : Defs) (state : State),
      EntriesFormed env state.entries → EntriesFormed env (rewriteAll env defs state terms).2.entries) with
  | natural => intro _ _ formed; exact formed
  | integer => intro _ _ formed; exact formed
  | boolean => intro _ _ formed; exact formed
  | unit => intro _ _ formed; exact formed
  | «variable» => intro _ _ formed; exact formed
  | unary _ _ _ ih => intro defs state formed; exact ih defs state formed
  | binary _ left _ _ ihLeft ihRight =>
    intro defs state formed
    exact ihRight defs (rewrite env defs state left).2 (ihLeft defs state formed)
  | pair _ first _ ihFirst ihSecond =>
    intro defs state formed
    exact ihSecond defs (rewrite env defs state first).2 (ihFirst defs state formed)
  | project _ _ _ ih => intro defs state formed; exact ih defs state formed
  | natToInt _ ih => intro defs state formed; exact ih defs state formed
  | ascribe _ _ ih => intro defs state formed; exact ih defs state formed
  | primitive id arguments result ih =>
    intro defs state formed
    have rewritten := ih defs state formed
    simp only [rewrite]
    split
    · rename_i compiled site
      obtain ⟨entry, entries, siteFormed⟩ := compileSite_entry (term := compiled.1) (state' := compiled.2) site
      rw [entries]
      intro other member
      rcases List.mem_append.mp member with member | member
      · exact rewritten other member
      · rw [List.mem_singleton.mp member]
        exact siteFormed
    · exact rewritten
  | call _ arguments _ _ ih => intro defs state formed; exact ih defs state formed
  | branch condition yes _ _ ihCondition ihYes ihNo =>
    intro defs state formed
    exact ihNo defs (rewrite env defs (rewrite env defs state condition).2 yes).2
      (ihYes defs _ (ihCondition defs state formed))
  | pack _ witness _ ihWitness ihFields =>
    intro defs state formed
    exact ihFields defs (rewrite env defs state witness).2 (ihWitness defs state formed)
  | unpack _ _ package _ ihPackage ihBody =>
    intro defs state formed
    exact ihBody defs (rewrite env defs state package).2 (ihPackage defs state formed)
  | scope _ ih => intro defs state formed; exact ih defs state formed
  | letE symbol value body ihValue ihBody =>
    intro defs state formed
    exact ihBody _ (rewrite env defs state value).2 (ihValue defs state formed)
  | nil => assumption
  | cons head _ ihHead ihRest =>
    rename_i defs state formed
    exact ihRest defs (rewrite env defs state head).2 (ihHead defs state formed)

theorem rewriteFunction_formed (env : Declarations) (base baseIds : Nat) {entries : List Entry}
    (function : Function) (formed : EntriesFormed env entries) :
    EntriesFormed env (rewriteFunction env base baseIds entries function).2 := by
  unfold rewriteFunction
  dsimp only
  split
  · exact rewrite_formed env function.body [] _ formed
  · exact formed

theorem fold_formed (env : Declarations) (base baseIds : Nat) :
    ∀ (functions : List Function) (state : List Function × List Entry), EntriesFormed env state.2 →
      EntriesFormed env (functions.foldl (IndexedReverseCore.foldStep env base baseIds) state).2
  | [], _, formed => formed
  | function :: rest, _, formed =>
    fold_formed env base baseIds rest _ (rewriteFunction_formed env base baseIds function formed)

/-- Every entry of the ledger of `generate` is formed against the source
declarations. -/
theorem generate_formed (module : Module) : EntriesFormed module.declarations (generate module).2 := by
  rw [IndexedReverseCore.generate_eq]
  split
  · intro _ member
    cases member
  · exact fold_formed module.declarations _ _ module.functions ([], []) (fun _ member => by cases member)

/-- A declaration keeps its binding when declarations are appended. -/
theorem primitive_append {env : Declarations} {extra : List NamedPrimitive} {id : DeclId}
    {binding : VastitasKernel.Indexed.PrimitiveBinding} (found : env.primitive? id = some binding) :
    ({ env with primitives := env.primitives ++ extra } : Declarations).primitive? id = some binding := by
  unfold Declarations.primitive? at found ⊢
  dsimp only
  cases first : env.primitives.find? (fun declaration => declaration.id == id) with
  | none =>
    rw [first] at found
    cases found
  | some declaration =>
    rw [first] at found
    simpa [List.find?_append, first] using found

/-- The rule of a declaration is kept when declarations are appended. -/
theorem ruleOf_append {env : Declarations} {extra : List NamedPrimitive} {id : DeclId}
    {map : VastitasKernel.AlgebraRuntime.Map} (rule : ruleOf env id = .morphism map) :
    ruleOf { env with primitives := env.primitives ++ extra } id = .morphism map := by
  unfold ruleOf at rule ⊢
  cases found : env.primitive? id with
  | none =>
    rw [found] at rule
    cases rule
  | some binding =>
    rw [found] at rule
    rw [primitive_append found]
    exact rule

/-- A `fiberVector` declaration of a valid module names a fiber family. -/
theorem fiberVector_variance {env : Declarations} (valid : env.Valid) {id family smooth object : DeclId}
    (member : (⟨id, .fiberVector family smooth object⟩ : NamedPrimitive) ∈ env.primitives) :
    ∃ variance, VastitasKernel.Indexed.fiberVariance? env.indexed family = some variance := by
  have checked := valid.primitives _ member
  simp only [VastitasKernel.Indexed.PrimitiveBinding.Valid, VastitasKernel.Indexed.PrimitiveBinding.contract,
    VastitasKernel.Indexed.PrimitiveDescriptor.ofBool, VastitasKernel.Indexed.fiberVectorValid,
    Bool.and_eq_true] at checked
  exact Option.isSome_iff_exists.mp checked.1.1.1

/-! ## The entries of a compiled module -/

/-- The facts about an entry of `module` that the theorems of
`SmoothReverseCore` assume of the entry and the module: the generated
function is found by the entry's function id; the forward step, the backward
step of every map and, for a differential, the seed are declared under the
entry's names, the seed over a fiber family; the site has a step; the map type
of every declared step names two objects; and every declared step is a
declaration with derivative rule `morphism` and the step's map. -/
structure EntryWellFormed (module : Module) (entry : Entry) : Prop where
  function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated
  apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth)
  declared : StepsDeclared module entry.names entry.site
  seed : entry.seed = .unit → module.declarations.primitive? entry.names.seed =
    some (.fiberVector entry.site.cotangent entry.site.smooth entry.site.output)
  seedFamily : entry.seed = .unit →
    ∃ variance, VastitasKernel.Indexed.fiberVariance? module.declarations.indexed entry.site.cotangent = some variance
  length : entry.names.steps.length = entry.site.steps.length
  nonempty : entry.site.steps ≠ []
  formed : ∀ step ∈ entry.site.steps, StepFormed step
  morphisms : MorphismsDeclared module entry.site.steps

section Compiled
variable {requireMain : Bool} {source : Typing.CheckedModule requireMain}

theorem compiled_formed (compiled : Compiled source) :
    EntriesFormed source.module.declarations compiled.entries := by
  have formed := generate_formed source.module
  rw [IndexedReverseCore.compiled_generate compiled] at formed
  exact formed

/-- **Every entry of a compiled module is well formed.** -/
theorem entry_well_formed (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries) :
    EntryWellFormed compiled.core.module entry := by
  obtain ⟨function, declarations⟩ := IndexedReverseCore.compiled_entry_resolves compiled member
  have formed := compiled_formed compiled entry member
  obtain ⟨kept, -⟩ := IndexedReverseCore.compiled_shape compiled
  refine ⟨function, declarations ⟨entry.names.apply, .smoothApply entry.site.smooth⟩ ?_,
    fun id step zipped => declarations ⟨id, stepBinding entry.site step.kind⟩ ?_,
    fun unit => declarations ⟨entry.names.seed, .fiberVector entry.site.cotangent entry.site.smooth
      entry.site.output⟩ ?_, fun unit => fiberVector_variance (id := entry.names.seed)
      (smooth := entry.site.smooth) (object := entry.site.output) compiled.core.typed.declarations ?_,
    entry_names_steps_length entry, formed.nonempty, formed.formed, ?_⟩
  · simp [Entry.declarations]
  · simp only [Entry.declarations, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨(id, step), zipped, rfl⟩)
  · simp [Entry.declarations, unit]
  · rw [kept]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, member, by simp [Entry.declarations, unit]⟩)
  · intro step stepMember morphism application map kind
    rw [kept]
    exact ruleOf_append (formed.morphisms step stepMember morphism application map kind)

end Compiled

/-! ## The generated function of a well-formed entry -/

section Calls
variable {module : Module} {entry : Entry}

/-- A saved entry's generated function, called on arguments that evaluate to
one smooth map per opaque step, the input point, one point per step and a
seed, evaluates to `backwardPass` at those points. -/
theorem EntryWellFormed.saved_call (wellFormed : EntryWellFormed module entry) (saved : entry.site.mode = .saved)
    {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length) (start : Program) {outputs : List Program}
    (outputCount : outputs.length = entry.site.steps.length) (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate module values arguments
      (functionArguments opaques (start :: outputs) variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent
        (backwardPass entry.site.steps (stepPrograms entry.site.steps opaques) start outputs seed))) :=
  call_evaluates wellFormed.function argumentsEval
    (by rw [functionParameters_length_saved saved]; simp [functionArguments, count, outputCount] <;> omega)
    substitution result fun _ bound =>
      saved_function_evaluates saved wellFormed.declared wellFormed.length wellFormed.formed wellFormed.nonempty
        count start outputCount variance seed bound

/-- With composable programs and saved points in the residual relation, the
call is the saved-mode pullback along the chain of the step programs. -/
theorem EntryWellFormed.saved_pullback (wellFormed : EntryWellFormed module entry)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques)) (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate module values arguments
      (functionArguments opaques (start :: outputs) variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms entry.site.steps opaques)) start seed))) := by
  have outputCount : outputs.length = entry.site.steps.length := by
    rw [← residual_length residual, stepPrograms_length]
  rw [← backwardPass_eq_pullback entry.site.steps _ start outputs seed (matches_stepPrograms _ _)
    (stepPrograms_ne_nil wellFormed.nonempty opaques) composable residual]
  exact wellFormed.saved_call saved count start outputCount variance seed argumentsEval substitution result

/-- A recomputing entry's generated function, called on arguments that
evaluate to one smooth map per opaque step, the input point and a seed,
evaluates to `backwardPass` at the evaluated images of the input point. -/
theorem EntryWellFormed.recomputed_call (wellFormed : EntryWellFormed module entry)
    (recomputed : entry.site.mode = .recomputed) {values : Values} {arguments : List Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length) (start : Program)
    (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate module values arguments (functionArguments opaques [start] variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (backwardPass entry.site.steps (stepPrograms entry.site.steps opaques) start
        (images (stepPrograms entry.site.steps opaques) start) seed))) :=
  call_evaluates wellFormed.function argumentsEval
    (by rw [functionParameters_length_recomputed recomputed]; simp [functionArguments, count])
    substitution result fun _ bound =>
      recomputed_function_evaluates recomputed wellFormed.apply wellFormed.declared wellFormed.length
        wellFormed.formed wellFormed.morphisms wellFormed.nonempty count start variance seed bound

/-- With composable programs, the call is the recomputing pullback along the
chain of the step programs. -/
theorem EntryWellFormed.recomputed_pullback (wellFormed : EntryWellFormed module entry)
    (recomputed : entry.site.mode = .recomputed) {values : Values} {arguments : List Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques)) (start : Program)
    (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate module values arguments (functionArguments opaques [start] variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent
        (pullback .recomputed (chain (stepPrograms entry.site.steps opaques)) start seed))) := by
  rw [← VastitasOracle.SmoothRuntime.pullback_saved_eq_recomputed,
    ← backwardPass_eq_pullback entry.site.steps _ start _ seed (matches_stepPrograms _ _)
      (stepPrograms_ne_nil wellFormed.nonempty opaques) composable (residualRel_images _ _)]
  exact wellFormed.recomputed_call recomputed count start variance seed argumentsEval substitution result

end Calls

/-! ## What every entry computes -/

/-- What the generated function of a ledger entry computes in `module`: the
entry is well formed, and a call of its function, on arguments that evaluate
to one smooth map per opaque step, the points and a seed, evaluates to the
pullback of the seed along the chain of the step programs, in the site's
mode. A saved site takes the input point and one saved point per step, in the
residual relation; a recomputing site takes the input point. -/
structure EntryComputes (module : Module) (entry : Entry) : Prop where
  wellFormed : EntryWellFormed module entry
  saved : entry.site.mode = .saved →
    ∀ (values : Values) (arguments : List Term) (opaques : List Program) (start : Program)
      (outputs : List Program) (variance : Variance) (seed : FiberValue)
      (substitution : List (ObjectRef × ObjectRef)) (result : Result),
      opaques.length = entry.site.opaqueSteps.length → Composable (stepPrograms entry.site.steps opaques) →
      ResidualRel (stepPrograms entry.site.steps opaques) start outputs →
      ArgumentsEvaluate module values arguments (functionArguments opaques (start :: outputs) variance seed) →
      Evaluates module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms entry.site.steps opaques)) start seed)))
  recomputed : entry.site.mode = .recomputed →
    ∀ (values : Values) (arguments : List Term) (opaques : List Program) (start : Program)
      (variance : Variance) (seed : FiberValue) (substitution : List (ObjectRef × ObjectRef)) (result : Result),
      opaques.length = entry.site.opaqueSteps.length → Composable (stepPrograms entry.site.steps opaques) →
      ArgumentsEvaluate module values arguments (functionArguments opaques [start] variance seed) →
      Evaluates module values (.call entry.function arguments substitution result)
        (.indexed (.fiber .cotangent
          (pullback .recomputed (chain (stepPrograms entry.site.steps opaques)) start seed)))

theorem EntryWellFormed.computes {module : Module} {entry : Entry} (wellFormed : EntryWellFormed module entry) :
    EntryComputes module entry :=
  ⟨wellFormed,
    fun saved _ _ _ start _ variance seed substitution result count composable residual argumentsEval =>
      wellFormed.saved_pullback saved count composable start residual variance seed argumentsEval substitution result,
    fun recomputed _ _ _ start variance seed substitution result count composable argumentsEval =>
      wellFormed.recomputed_pullback recomputed count composable start variance seed argumentsEval substitution
        result⟩

/-- **The meaning of a saved entry (uses the chain rule).** When the chain of
the step programs is well typed from dimension `n` to `m` and the seed lies
over its image of the input point with `m` components, the call evaluates to
the covector at the input point whose components are `cot` of the composite
map. -/
theorem EntryComputes.saved_cot {module : Module} {entry : Entry} (computes : EntryComputes module entry)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length) {n m : Nat}
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true) (start : Program)
    {outputs : List Program} (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot
        (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start) seed.components⟩))) := by
  rw [← pullback_chain_cot .saved typed start seed over components]
  exact computes.saved saved values arguments opaques start outputs variance (some seed) substitution result count
    (composable_of_wellTyped _ typed) residual argumentsEval

/-- **The meaning of a recomputing entry (uses the chain rule).** -/
theorem EntryComputes.recomputed_cot {module : Module} {entry : Entry} (computes : EntryComputes module entry)
    (recomputed : entry.site.mode = .recomputed) {values : Values} {arguments : List Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length) {n m : Nat}
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true) (start : Program)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot
        (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start) seed.components⟩))) := by
  rw [← pullback_chain_cot .recomputed typed start seed over components]
  exact computes.recomputed recomputed values arguments opaques start variance (some seed) substitution result
    count (composable_of_wellTyped _ typed) argumentsEval

section Compiled
variable {requireMain : Bool} {source : Typing.CheckedModule requireMain}

/-- **Every entry of a compiled module computes the pullback of its site.** -/
theorem compiled_entries_compute (compiled : Compiled source) :
    ∀ entry ∈ compiled.entries, EntryComputes compiled.core.module entry :=
  fun _ member => (entry_well_formed compiled member).computes

/-- **A saved entry of a compiled module.** A call of the entry's generated
function in the compiled module, on arguments that evaluate to one smooth map
per opaque step, the input point, one saved point per step in the residual
relation and a seed, evaluates to the saved-mode pullback of the seed along
the chain of the step programs. No chain rule is used. -/
theorem compiled_saved_entry (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques)) (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms entry.site.steps opaques)) start seed))) :=
  (entry_well_formed compiled member).saved_pullback saved count composable start residual variance seed
    argumentsEval substitution result

/-- **A recomputing entry of a compiled module.** A call of the entry's
generated function in the compiled module, on arguments that evaluate to one
smooth map per opaque step, the input point and a seed, evaluates to the
recomputing pullback of the seed along the chain of the step programs. No
chain rule is used. -/
theorem compiled_recomputed_entry (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries)
    (recomputed : entry.site.mode = .recomputed) {values : Values} {arguments : List Term}
    {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques)) (start : Program)
    (variance : Variance) (seed : FiberValue)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance seed))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent
        (pullback .recomputed (chain (stepPrograms entry.site.steps opaques)) start seed))) :=
  (entry_well_formed compiled member).recomputed_pullback recomputed count composable start variance seed
    argumentsEval substitution result

/-- **The meaning of a saved entry of a compiled module (uses the chain
rule).** -/
theorem compiled_saved_entry_cot (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length) {n m : Nat}
    (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true) (start : Program)
    {outputs : List Program} (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot
        (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start) seed.components⟩))) :=
  (compiled_entries_compute compiled _ member).saved_cot saved count typed start residual variance seed over
    components argumentsEval substitution result

/-- **The meaning of a recomputing entry of a compiled module (uses the chain
rule).** -/
theorem compiled_recomputed_entry_cot (compiled : Compiled source) {entry : Entry}
    (member : entry ∈ compiled.entries) (recomputed : entry.site.mode = .recomputed) {values : Values}
    {arguments : List Term} {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    {n m : Nat} (typed : (chain (stepPrograms entry.site.steps opaques)).wellTyped n m = true)
    (start : Program) (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms entry.site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = m)
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques [start] variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent (some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot
        (chain (stepPrograms entry.site.steps opaques)).denote (coordinates start) seed.components⟩))) :=
  (compiled_entries_compute compiled _ member).recomputed_cot recomputed count typed start variance seed over
    components argumentsEval substitution result

end Compiled

/-! ## Public paths -/

/-- **Protocol 7.** For every JSON that `Indexed.Wire.check` accepts, every
entry of the compiled module of the accepted certificate, the module that
`Main` emits, computes the pullback of its site. -/
theorem public_wire_entries {json : Lean.Json} {requireMain : Bool}
    (accepted : VastitasKernel.Indexed.Wire.CheckedInput json requireMain) :
    ∀ entry ∈ accepted.checked.compiled.entries, EntryComputes accepted.checked.compiled.core.module entry :=
  compiled_entries_compute accepted.checked.compiled

/-- **Protocols 2-6.** The same for every JSON that the legacy checker
accepts. -/
theorem legacy_wire_entries {json : Lean.Json} {requireMain : Bool}
    (accepted : VastitasKernel.Indexed.LegacySource.CheckedInput json requireMain) :
    ∀ entry ∈ accepted.checked.compiled.entries, EntryComputes accepted.checked.compiled.core.module entry :=
  compiled_entries_compute accepted.checked.compiled

/-- **Protocols 8/9.** For every JSON that `ResourceSource.Wire.check`
accepts, every entry of both compiled modules of the certificate (the pure
program, which the pure emit path generates, and the pure values of a
resource entry, whose library the mixed emit path generates) computes the
pullback of its site. -/
theorem public_resource_entries {json : Lean.Json} {requireMain : Bool}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    (∀ entry ∈ input.checked.pureProgram.compiled.entries,
      EntryComputes input.checked.pureProgram.compiled.core.module entry) ∧
    ∀ entry ∈ input.checked.values.compiled.entries,
      EntryComputes input.checked.values.compiled.core.module entry :=
  ⟨compiled_entries_compute input.checked.pureProgram.compiled,
    compiled_entries_compute input.checked.values.compiled⟩

/-- **Protocols 8/9 emit without a resource entry.** The module that the
public emit path generates code from is the compiled pure program of the
checked certificate, and every entry of its ledger computes the pullback of
its site there. -/
theorem public_pure_entry_computes {json : Lean.Json} {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (decoded : VastitasKernel.ResourceSource.Wire.program json = .ok program) (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Wire.emit json = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Codegen.generate core = .ok generated.source ∧
      ∀ entry ∈ checked.pureProgram.compiled.entries, EntryComputes core.module entry := by
  obtain ⟨checked, accepted, core, same, emittedCore, _, _⟩ :=
    IndexedReverseCore.public_pure_entry_compiled decoded found emitted
  refine ⟨checked, accepted, core, same, emittedCore, ?_⟩
  rw [same]
  exact compiled_entries_compute checked.pureProgram.compiled

end VastitasOracle.SmoothReverseCompiled
