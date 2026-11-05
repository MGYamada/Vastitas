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
  family. The site has a step, and the map type of every declared step names
  two objects (`StepFormed`). Every declared step is a declaration of the
  compiled module whose derivative rule is `morphism` with the step's map
  (`MorphismsDeclared`).
- `compiled_saved_entry`, `compiled_recomputed_entry`: a call of the generated
  function of an entry, on arguments that evaluate to one smooth map per
  opaque step, the points and a covector, evaluates to the runtime pullback
  along the chain of those step programs. For a saved site the saved points
  satisfy the residual relation. `compiled_saved_entry_foreign_seed`: a seed
  over another point gives the failure value.
- `compiled_saved_entry_cot`, `compiled_recomputed_entry_cot`,
  `EntryComputes.saved_cot` and `EntryComputes.recomputed_cot`: the value in
  coordinates. These four use the chain rule (`SmoothCalculus.backward_eq_cot`).
- `resolve_factors`: when the `let` definitions in scope agree with the
  activation (`DefsAgree`), the value of a map operand that `resolve` reads is
  a composition tree of the step programs (`Factors`).
- `compileSite_term`: the term that `compileSite` returns and the entry that it
  appends. `compiled_site_evaluates`: that term and the source call evaluate to
  the same value, for a pullback, a differential and a tape.
- `public_wire_entries`, `legacy_wire_entries`, `public_resource_entries` and
  `public_pure_entry_computes`: on every public path (protocols 2-6, 7 and
  8/9), every entry of the compiled modules of the accepted certificate, and of
  the module that the pure emit path generates code from, satisfies these
  (`EntryComputes`).

The premises that stay are facts about the arguments and the activation: one
value per opaque step (`count`), composable programs (`Composable`), for a
saved site the residual relation of the points, and for a site the agreement
of the `let` definitions. The theorems do not prove that consecutive steps
share their objects, and they do not need it. They concern checked Core, not
the generated text or native code. `scripts/check_chain_rule_free.lean` checks
which theorems use the chain rule. -/

namespace VastitasOracle.SmoothReverseCompiled

open VastitasKernel.Indexed (Variance DeclId ObjectRef ReverseRule)
open VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics (Values Value eval evalPrimitive bindValue)
open VastitasKernel.Indexed.Core.Reverse
open VastitasKernel.SmoothRuntime (Program FiberValue Fiber PullbackMode pullback coordinates)
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

/-- What the generated function of a ledger entry computes in `module`. The
entry is well formed. A call of its function, on arguments that evaluate to
one smooth map per opaque step, the points and a seed, evaluates to the
pullback of the seed along the chain of the step programs passed as
arguments, in the site's mode. A saved site takes the input point and one
saved point per step, in the residual relation; a recomputing site takes the
input point. -/
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

/-- **Every entry of a compiled module computes the pullback along the chain
of its step programs.** -/
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

/-! ## A seed over another point -/

/-- A saved entry's generated function, called with saved points in the
residual relation and a seed that does not lie over the last saved point,
evaluates to the failure value. Composability is not needed. -/
theorem EntryWellFormed.saved_foreign_seed {module : Module} {entry : Entry}
    (wellFormed : EntryWellFormed module entry) (saved : entry.site.mode = .saved) {values : Values}
    {arguments : List Term} {opaques : List Program} (count : opaques.length = entry.site.opaqueSteps.length)
    (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs) (variance : Variance)
    (seed : Fiber) (foreign : seed.point ≠ coordinates (outputs.getLastD start))
    (argumentsEval : ArgumentsEvaluate module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates module values (.call entry.function arguments substitution result) (.indexed (.fiber .cotangent none)) := by
  have outputCount : outputs.length = entry.site.steps.length := by
    rw [← residual_length residual, stepPrograms_length]
  rw [← backwardPass_foreign_seed entry.site.steps _ start outputs seed (matches_stepPrograms _ _)
    (stepPrograms_ne_nil wellFormed.nonempty opaques) residual foreign]
  exact wellFormed.saved_call saved count start outputCount variance (some seed) argumentsEval substitution result

/-- **A seed over another point, for a compiled entry.** For every saved entry
of a compiled module, a call of its generated function with saved points in
the residual relation and a seed that does not lie over the last saved point
evaluates to the failure value. No chain rule is used. -/
theorem compiled_saved_entry_foreign_seed {requireMain : Bool} {source : Typing.CheckedModule requireMain}
    (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries)
    (saved : entry.site.mode = .saved) {values : Values} {arguments : List Term} {opaques : List Program}
    (count : opaques.length = entry.site.opaqueSteps.length) (start : Program) {outputs : List Program}
    (residual : ResidualRel (stepPrograms entry.site.steps opaques) start outputs) (variance : Variance)
    (seed : Fiber) (foreign : seed.point ≠ coordinates (outputs.getLastD start))
    (argumentsEval : ArgumentsEvaluate compiled.core.module values arguments
      (functionArguments opaques (start :: outputs) variance (some seed)))
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Evaluates compiled.core.module values (.call entry.function arguments substitution result)
      (.indexed (.fiber .cotangent none)) :=
  (entry_well_formed compiled member).saved_foreign_seed saved count start residual variance seed foreign
    argumentsEval substitution result

/-! ## Evaluation of the terms that `resolve` reads -/

theorem evaluates_ascribe_iff {module : Module} {values : Values} {annotation : DataType} {term : Term}
    {value : Value} : Evaluates module values (.ascribe annotation term) value ↔ Evaluates module values term value := by
  constructor
  · rintro ⟨bound, evaluated⟩
    exact ⟨bound, fun fuel enough => by simpa [eval] using evaluated (fuel + 1) (by omega)⟩
  · exact IndexedEvaluation.ascribe annotation

theorem evaluates_strip {module : Module} {values : Values} : ∀ (term : Term) {value : Value},
    Evaluates module values (strip term) value ↔ Evaluates module values term value
  | .ascribe _ inner, _ => by
    rw [strip]
    exact (evaluates_strip inner).trans evaluates_ascribe_iff.symm
  | .natural _, _ | .integer _, _ | .boolean _, _ | .unit, _ | .variable _ _, _ | .unary _ _ _, _
  | .binary _ _ _ _, _ | .pair _ _ _, _ | .project _ _ _, _ | .natToInt _, _ | .primitive _ _ _, _
  | .call _ _ _ _, _ | .branch _ _ _ _, _ | .pack _ _ _, _ | .unpack _ _ _ _, _ | .scope _, _
  | .letE _ _ _, _ => Iff.rfl

theorem stable_strip {module : Module} {values : Values} {bound : Nat} (term : Term) {value : Value} :
    Stable module values bound (strip term) value ↔ Stable module values bound term value :=
  ⟨fun stable values' agrees => (evaluates_strip term).mp (stable values' agrees),
    fun stable values' agrees => (evaluates_strip term).mpr (stable values' agrees)⟩

theorem variable_holds {module : Module} {values : Values} {symbol : Nat} {result : Result} {value : Value}
    (evaluated : Evaluates module values (.variable symbol result) value) : values symbol = some value := by
  obtain ⟨bound, evaluated⟩ := evaluated
  simpa [eval] using evaluated (bound + 1) (by omega)

theorem eval_primitive_some {module : Module} {fuel : Nat} {values : Values} {id : DeclId}
    {arguments : List Term} {result : Result} {value : Value}
    (evaluated : eval module (fuel + 1) values (.primitive id arguments result) = some value) :
    ∃ binding operands, module.declarations.primitive? id = some binding ∧
      arguments.mapM (eval module fuel values) = some operands ∧
      evalPrimitive module.declarations.indexed binding operands = some value := by
  simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at evaluated
  obtain ⟨binding, found, operands, mapped, operated⟩ := evaluated
  exact ⟨binding, operands, found, mapped, operated⟩

theorem mapM_getElem? {α β : Type} {f : α → Option β} : ∀ {as : List α} {bs : List β}, as.mapM f = some bs →
    ∀ {index : Nat} {a : α}, as[index]? = some a → ∃ b, bs[index]? = some b ∧ f a = some b
  | [], _, _, _, _, found => by simp at found
  | _ :: _, _, mapped, index, _, found => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at mapped
    obtain ⟨head, headFound, rest, restMapped, rfl⟩ := mapped
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨head, rfl, headFound⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨b, at', image⟩ := mapM_getElem? restMapped found
      exact ⟨b, by simpa using at', image⟩

/-- A rule of the source declarations is a rule of a module that keeps their
bindings. -/
theorem ruleOf_transfer {env : Declarations} {module : Module}
    (rules : ∀ id binding, env.primitive? id = some binding → module.declarations.primitive? id = some binding)
    {id : DeclId} {rule : ReverseRule} (found : ruleOf env id = rule) (proper : rule ≠ .none) :
    ruleOf module.declarations id = rule := by
  obtain ⟨binding, declared, reverse⟩ := ruleOf_found found proper
  unfold ruleOf
  rw [rules id binding declared]
  exact reverse

/-- The operands of a call with rule `chain after before` whose value is a
smooth map `map`: `map` is `compose outer inner`, and the operands at `after`
and `before` evaluate to `outer` and `inner` (`ReverseSound`). -/
theorem chain_operands {module : Module} {values : Values} {bound : Nat} {id : DeclId} {arguments : List Term}
    {result : Result} {after before : Nat} (rule : ruleOf module.declarations id = .chain after before)
    {first second : Term} (atAfter : arguments[after]? = some first) (atBefore : arguments[before]? = some second)
    {map : Program} (stable : Stable module values bound (.primitive id arguments result) (smoothValue map)) :
    ∃ outer inner, map = .compose outer inner ∧ Stable module values bound first (smoothValue outer) ∧
      Stable module values bound second (smoothValue inner) := by
  obtain ⟨binding, found, reverse⟩ := ruleOf_found rule (by intro same; cases same)
  have sound := SmoothJacobian.registry_reverse_sound binding
  unfold SmoothJacobian.ReverseSound at sound
  rw [reverse] at sound
  have split : ∀ (values' : Values) (fuel : Nat),
      eval module (fuel + 1) values' (.primitive id arguments result) = some (smoothValue map) →
      ∃ outer inner, map = .compose outer inner ∧ eval module fuel values' first = some (smoothValue outer) ∧
        eval module fuel values' second = some (smoothValue inner) := by
    intro values' fuel evaluated
    obtain ⟨binding', operands, found', mapped, operated⟩ := eval_primitive_some evaluated
    rw [found, Option.some.injEq] at found'
    subst found'
    obtain ⟨outer, inner, _, outerAt, innerAt, same⟩ := (sound _ _ _).mp operated
    obtain ⟨outerValue, outerFound, outerEval⟩ := mapM_getElem? mapped atAfter
    obtain ⟨innerValue, innerFound, innerEval⟩ := mapM_getElem? mapped atBefore
    rw [outerAt, Option.some.injEq] at outerFound
    rw [innerAt, Option.some.injEq] at innerFound
    subst outerFound innerFound
    refine ⟨outer, inner, ?_, outerEval, innerEval⟩
    cases same
    rfl
  obtain ⟨found, evaluated⟩ := stable.evaluates
  obtain ⟨outer, inner, rfl, -, -⟩ := split values found (evaluated (found + 1) (by omega))
  refine ⟨outer, inner, rfl, fun values' agrees => ?_, fun values' agrees => ?_⟩
  · obtain ⟨least, evaluated'⟩ := stable values' agrees
    refine ⟨least, fun fuel enough => ?_⟩
    obtain ⟨outer', inner', same, image, -⟩ := split values' fuel (evaluated' (fuel + 1) (by omega))
    cases same
    exact image
  · obtain ⟨least, evaluated'⟩ := stable values' agrees
    refine ⟨least, fun fuel enough => ?_⟩
    obtain ⟨outer', inner', same, -, image⟩ := split values' fuel (evaluated' (fuel + 1) (by omega))
    cases same
    exact image

/-! ## The reading of a site's maps is sound -/

/-- The `let` definitions in scope agree with the activation: each symbol
holds a value that its definition evaluates to, reading no symbol at or above
`bound`. -/
def DefsAgree (module : Module) (values : Values) (bound : Nat) (defs : Defs) : Prop :=
  ∀ definition ∈ defs, ∃ value, values definition.symbol = some value ∧
    Stable module values bound definition.value value

/-- The opaque leaves of a tree, in application order. -/
def opaqueLeaves (leaves : List Tree) : List Term :=
  leaves.filterMap fun
    | .opaque value => some value
    | _ => none

/-- The programs of a tree's leaves in application order: the map of a
declared leaf as one program node, and the next of `opaques` for an opaque
leaf. -/
def leafPrograms : List Tree → List Program → List Program
  | [], _ => []
  | .declared _ _ map :: rest, opaques => .primitive map :: leafPrograms rest opaques
  | .opaque _ :: rest, program :: more => program :: leafPrograms rest more
  | .opaque _ :: rest, [] => default :: leafPrograms rest []
  | .node _ _ :: rest, opaques => default :: leafPrograms rest opaques

theorem opaqueLeaves_append (first second : List Tree) :
    opaqueLeaves (first ++ second) = opaqueLeaves first ++ opaqueLeaves second := by
  simp [opaqueLeaves, List.filterMap_append]

theorem leafPrograms_append : ∀ (first second : List Tree) (opaques rest : List Program),
    (opaqueLeaves first).length = opaques.length →
    leafPrograms (first ++ second) (opaques ++ rest) = leafPrograms first opaques ++ leafPrograms second rest
  | [], _, opaques, _, count => by
    cases opaques with
    | nil => rfl
    | cons _ _ => simp [opaqueLeaves] at count
  | .declared _ _ _ :: first, second, opaques, rest, count => by
    simp only [List.cons_append, leafPrograms,
      leafPrograms_append first second opaques rest (by simpa [opaqueLeaves] using count)]
  | .opaque _ :: _, _, [], _, count => by simp [opaqueLeaves] at count
  | .opaque _ :: first, second, _ :: opaques, rest, count => by
    simp only [List.cons_append, leafPrograms,
      leafPrograms_append first second opaques rest (by simpa [opaqueLeaves] using count)]
  | .node _ _ :: first, second, opaques, rest, count => by
    simp only [List.cons_append, leafPrograms,
      leafPrograms_append first second opaques rest (by simpa [opaqueLeaves] using count)]

theorem opaque_factors {module : Module} {values : Values} {bound : Nat} {term : Term} {map : Program}
    (stable : Stable module values bound term (smoothValue map)) :
    ∃ opaques, AllPairs (fun leaf program => Stable module values bound leaf (smoothValue program))
      (opaqueLeaves (Tree.opaque term).leaves) opaques ∧ Factors map (leafPrograms (Tree.opaque term).leaves opaques) :=
  ⟨[map], ⟨stable, trivial⟩, .leaf map⟩

theorem defs_find_stable {module : Module} {values : Values} {bound : Nat} {defs : Defs}
    (agree : DefsAgree module values bound defs) {symbol : Nat} {definition : Def}
    (found : defs.find symbol = some definition) {result : Result} {value : Value}
    (stable : Stable module values bound (.variable symbol result) value) :
    Stable module values bound definition.value value := by
  unfold Defs.find at found
  have member := List.mem_of_find?_eq_some found
  have same := List.find?_some found
  simp only [beq_iff_eq] at same
  obtain ⟨held, holds, heldStable⟩ := agree definition member
  rw [same, variable_holds stable.evaluates, Option.some.injEq] at holds
  rw [holds]
  exact heldStable

/-- **The reading of a site's maps is sound.** Let the `let` definitions in
scope agree with the activation (`DefsAgree`), and let the source
declarations keep their bindings in `module`. When `resolve` reads a tree from
a map term whose value is a well-typed program `map`, every opaque leaf term
evaluates to a program, and `map` is a composition tree whose leaves are the
leaf programs (`Factors`). The proof reads the derivative rules through
`SmoothJacobian.registry_reverse_sound`: a `morphism` call evaluates to its
map, and a `chain` call to the `compose` of its operands. No chain rule is
used. -/
theorem resolve_factors {module : Module} {env : Declarations}
    (rules : ∀ id binding, env.primitive? id = some binding → module.declarations.primitive? id = some binding)
    {values : Values} {bound : Nat} {defs : Defs} (agree : DefsAgree module values bound defs) :
    ∀ (fuel budget : Nat) (term : Term) {tree : Tree} {rest : Nat},
      resolve env defs fuel budget term = some (tree, rest) → ∀ {map : Program},
      Stable module values bound term (smoothValue map) → ∀ {source target : Nat},
      map.wellTyped source target = true →
      ∃ opaques, AllPairs (fun leaf program => Stable module values bound leaf (smoothValue program))
        (opaqueLeaves tree.leaves) opaques ∧ Factors map (leafPrograms tree.leaves opaques)
  | 0, _, _, _, _, resolved, _, stable, _, _, _ => by
    rw [resolve] at resolved
    rw [charge_tree resolved]
    exact opaque_factors stable
  | fuel + 1, budget, term, tree, rest, resolved, map, stable, source, target, typed => by
    have stripped := (stable_strip term).mpr stable
    rw [resolve] at resolved
    split at resolved
    · rw [‹strip term = _›] at stripped
      split at resolved
      · subst_vars
        rw [charge_tree resolved]
        have same := IndexedEvaluation.evaluates_unique stripped.evaluates (morphism_evaluates
          (ruleOf_transfer rules ‹ruleOf env _ = .morphism _› (by intro same; cases same)) values _)
        cases same
        exact ⟨[], trivial, .leaf _⟩
      · split at resolved
        · rename_i first second atAfter atBefore
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
              obtain ⟨outer, inner, rfl, outerStable, innerStable⟩ := chain_operands
                (ruleOf_transfer rules ‹ruleOf env _ = .chain _ _› (by intro same; cases same)) atAfter atBefore
                stripped
              simp only [VastitasKernel.SmoothRuntime.Program.wellTyped, Bool.and_eq_true] at typed
              obtain ⟨outerOpaques, outerPairs, outerFactors⟩ :=
                resolve_factors rules agree fuel budget first readFirst outerStable typed.2
              obtain ⟨innerOpaques, innerPairs, innerFactors⟩ :=
                resolve_factors rules agree fuel firstRest second readSecond innerStable typed.1
              refine ⟨innerOpaques ++ outerOpaques, ?_, ?_⟩
              · show AllPairs _ (opaqueLeaves (secondTree.leaves ++ firstTree.leaves)) _
                rw [opaqueLeaves_append]
                exact AllPairs.append innerPairs outerPairs
              · show Factors _ (leafPrograms (secondTree.leaves ++ firstTree.leaves) _)
                rw [leafPrograms_append _ _ _ _ innerPairs.length]
                exact Factors.node outerFactors innerFactors
                  (VastitasOracle.SmoothRuntime.wellTyped_inputArity typed.2)
        · rw [charge_tree resolved]
          exact opaque_factors stable
      · rw [charge_tree resolved]
        exact opaque_factors stable
    · rw [‹strip term = _›] at stripped
      split at resolved
      · split at resolved
        · split at resolved
          · cases resolved
            exact resolve_factors rules agree fuel budget _ ‹resolve env defs fuel budget _ = some (tree, rest)›
              (defs_find_stable agree ‹_› stripped) typed
          · rw [charge_tree resolved]
            exact opaque_factors stripped
        · rw [charge_tree resolved]
          exact opaque_factors stripped
      · rw [charge_tree resolved]
        exact opaque_factors stripped
    · rw [charge_tree resolved]
      exact opaque_factors stable

/-- The steps that `stepsOf` reads have the leaf programs as their programs,
and one opaque step per opaque leaf. -/
theorem stepsOf_programs {smooth : DeclId} : ∀ {leaves : List Tree} {steps : List Step},
    stepsOf smooth leaves = some steps → ∀ opaques : List Program,
      stepPrograms steps opaques = leafPrograms leaves opaques ∧
      (steps.filter fun step => step.kind == .opaque).length = (opaqueLeaves leaves).length
  | [], _, read, _ => by
    simp only [stepsOf, List.mapM_nil, Option.pure_def, Option.some.injEq] at read
    subst read
    exact ⟨rfl, rfl⟩
  | leaf :: leaves, _, read, opaques => by
    simp only [stepsOf, List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at read
    obtain ⟨step, built, steps, rest, rfl⟩ := read
    cases leaf with
    | declared call morphism map =>
      simp only [Option.bind_eq_some_iff] at built
      obtain ⟨⟨source, target⟩, _, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      obtain ⟨programs, count⟩ := stepsOf_programs rest opaques
      refine ⟨by simp only [stepPrograms, leafPrograms, programs], ?_⟩
      simpa [opaqueLeaves] using count
    | «opaque» value =>
      simp only [Option.bind_eq_some_iff] at built
      obtain ⟨⟨source, target⟩, _, built⟩ := built
      simp only [Option.some.injEq] at built
      subst built
      cases opaques with
      | nil =>
        obtain ⟨programs, count⟩ := stepsOf_programs rest []
        refine ⟨by simp only [stepPrograms, leafPrograms, programs], ?_⟩
        simpa [opaqueLeaves] using count
      | cons program more =>
        obtain ⟨programs, count⟩ := stepsOf_programs rest more
        refine ⟨by simp only [stepPrograms, leafPrograms, programs], ?_⟩
        simpa [opaqueLeaves] using count
    | node => cases built

theorem evaluationOrder_opaque : ∀ (tree : Tree) {value : Term},
    value ∈ tree.evaluationOrder → value ∈ opaqueLeaves tree.leaves
  | .node after before, value, member => by
    simp only [Tree.evaluationOrder, List.mem_append] at member
    show value ∈ opaqueLeaves (before.leaves ++ after.leaves)
    rw [opaqueLeaves_append, List.mem_append]
    rcases member with member | member
    · exact Or.inr (evaluationOrder_opaque after member)
    · exact Or.inl (evaluationOrder_opaque before member)
  | .opaque _, _, member => by
    simpa [Tree.evaluationOrder, Tree.leaves, opaqueLeaves] using member
  | .declared _ _ _, _, member => by
    simp [Tree.evaluationOrder] at member

/-! ## What `compileSite` returns -/

/-- The `let`s of a list of bindings around a body, the first outermost. -/
def letsOf (binds : List (Nat × Term)) (body : Term) : Term :=
  binds.foldr (fun bind rest => .letE bind.1 bind.2 rest) body

/-- The bindings of the compound opaque leaves of a site at the symbols
`next, next + 1, …`, as `compileSite` lists them. -/
def compoundBinds (next : Nat) (compound : List Term) : List (Nat × Term) :=
  (compound.zipIdx.map fun pair => (pair.1, next + pair.2)).map fun pair => (pair.2, pair.1)

/-- A map term that `compileSite` passes for the opaque leaf `leaf`: the leaf
itself, or the variable of a compound leaf structurally equal to it. -/
def OpaqueArgument (next : Nat) (compound : List Term) (argument leaf : Term) : Prop :=
  argument = leaf ∨ ∃ (index : Nat) (result : Result), compound[index]? = some leaf ∧
    argument = .variable (next + index) result

/-- The Core that `compileSite` puts at a site after the `let` of its input
point at `start`: the seed `let` and the call for a recomputing site; the seed
`let`, the forward `let`s and the call for a saved site with a seed operand;
the forward `let`s, the unit seed and the call for a differential. -/
def siteBody (entry : Entry) (seed : Option Term) (opaqueTerms : List Term) (start : Nat) (point : Term)
    (result : Result) : Term :=
  match entry.site.mode, seed with
  | .recomputed, some seedTerm =>
    .letE (start + 1) seedTerm (.call entry.function (opaqueTerms ++ [.variable start point.result,
      .variable (start + 1) seedTerm.result]) [] result)
  | .recomputed, none => .unit
  | .saved, some seedTerm =>
    .letE (start + 1) seedTerm (forwardLets entry.names entry.site entry.site.steps
      (mapTerms entry.site.steps opaqueTerms) (.variable start point.result)
      (pointSymbols (start + 2) entry.site.steps.length)
      (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable start point.result)
        (pointSymbols (start + 2) entry.site.steps.length) ++ [.variable (start + 1) seedTerm.result]) [] result))
  | .saved, none =>
    forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
      (.variable start point.result) (pointSymbols (start + 2) entry.site.steps.length)
      (.letE (start + 1) (unitSeed entry (sitePoints entry.site (.variable start point.result)
          (pointSymbols (start + 2) entry.site.steps.length)) (.variable start point.result))
        (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable start point.result)
          (pointSymbols (start + 2) entry.site.steps.length) ++
          [.variable (start + 1) (fiberResult entry.site entry.site.output)]) [] result))

theorem allPairs_map_self {α β : Type} {relation : β → α → Prop} {f : α → β} :
    ∀ (as : List α), (∀ a ∈ as, relation (f a) a) → AllPairs relation (as.map f) as
  | [], _ => trivial
  | a :: as, each => ⟨each a (by simp), allPairs_map_self as fun b member => each b (by simp [member])⟩

/-- **What `compileSite` returns.** A compiled site appends one entry to the
ledger. Its term binds the compound opaque leaves at `next, next + 1, …`, then
the input point at `start`, after them, and continues with `siteBody`. The
entry's steps are those of the tree that `resolve` reads from the map operand,
or of that operand as one step. Every opaque term of the call is an opaque
leaf or the variable of an equal compound leaf. -/
theorem compileSite_term {env : Declarations} {defs : Defs} {state : State} {id : DeclId}
    {arguments : List Term} {result : Result} {term : Term} {state' : State}
    (compiled : compileSite env defs state id arguments result = some (term, state')) :
    ∃ (map point : Term) (seed : Option Term) (tree : Tree) (entry : Entry) (compound opaqueTerms : List Term),
      siteOperands env defs id arguments = some (map, point, seed, entry.site.mode) ∧
      ((∃ rest, resolve env defs (defs.length + 64) VastitasKernel.Limits.reverseLeaves map = some (tree, rest)) ∨
        tree = .opaque map) ∧
      stepsOf entry.site.smooth tree.leaves = some entry.site.steps ∧
      entry.seed = (if seed.isSome then .operand else .unit) ∧
      ¬(entry.site.mode = .recomputed ∧ seed = none) ∧
      (∀ value ∈ compound, value ∈ opaqueLeaves tree.leaves) ∧
      AllPairs (OpaqueArgument state.next compound) opaqueTerms (opaqueLeaves tree.leaves) ∧
      state'.entries = state.entries ++ [entry] ∧
      term = letsOf (compoundBinds state.next compound)
        (.letE (state.next + compound.length) point
          (siteBody entry seed opaqueTerms (state.next + compound.length) point result)) := by
  unfold compileSite at compiled
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨⟨map, point, seed, mode⟩, operands, compiled⟩ := compiled
  simp only at compiled
  obtain ⟨⟨smooth, origin, object⟩, -, compiled⟩ := compiled
  simp only at compiled
  obtain ⟨cotangent, -, compiled⟩ := compiled
  obtain ⟨steps, read, compiled⟩ := compiled
  obtain ⟨⟨⟩, -, compiled⟩ := compiled
  obtain ⟨⟨⟩, -, compiled⟩ := compiled
  obtain ⟨⟨⟩, -, compiled⟩ := compiled
  cases resolved : resolve env defs (defs.length + 64) VastitasKernel.Limits.reverseLeaves map
  case' none =>
    simp only [resolved] at read compiled
    generalize treeIs : Tree.opaque map = tree at read compiled
    have treeCase : (∃ rest, resolve env defs (defs.length + 64) VastitasKernel.Limits.reverseLeaves map =
        some (tree, rest)) ∨ tree = .opaque map := Or.inr treeIs.symm
  case' some pair =>
    obtain ⟨tree, rest⟩ := pair
    simp only [resolved] at read compiled
    have treeCase : (∃ rest, resolve env defs (defs.length + 64) VastitasKernel.Limits.reverseLeaves map =
        some (tree, rest)) ∨ tree = .opaque map := Or.inl ⟨rest, resolved⟩
  all_goals
    refine ⟨map, point, seed, tree, ⟨state.entries.length, state.scope, state.caller,
      state.base + state.entries.length, ⟨smooth, cotangent, origin, steps, mode⟩,
      if seed.isSome then .operand else .unit⟩,
      tree.evaluationOrder.filter (fun value => match strip value with
        | .variable _ _ => false
        | _ => true),
      (opaqueLeaves tree.leaves).map (fun value => match strip value with
        | .variable _ _ => value
        | _ =>
          match ((tree.evaluationOrder.filter (fun value => match strip value with
              | .variable _ _ => false
              | _ => true)).zipIdx.map fun pair => (pair.1, state.next + pair.2)).find?
              (fun pair => termEq pair.1 value) with
          | some (_, symbol) => .variable symbol value.result
          | none => value),
      operands, treeCase, read, rfl, ?notBoth, ?member, ?arguments, ?final⟩
    case notBoth =>
      rintro ⟨recomputed, absent⟩
      simp only at recomputed
      subst recomputed absent
      cases compiled
    case member =>
      intro value member
      exact evaluationOrder_opaque _ (List.mem_filter.mp member).1
    case arguments =>
      refine allPairs_map_self _ fun leaf _ => ?_
      split
      · exact Or.inl rfl
      · split
        · rename_i found
          obtain ⟨⟨other, index⟩, member, same⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
          simp only [Prod.mk.injEq] at same
          obtain ⟨sameValue, sameSymbol⟩ := same
          subst sameValue
          subst sameSymbol
          have matched := List.find?_some found
          simp only at matched
          have equal : other = leaf := IndexedReverseCore.termEq_sound matched
          subst equal
          exact Or.inr ⟨index, _, List.mem_zipIdx_iff_getElem?.mp member, rfl⟩
        · exact Or.inl rfl
    case final =>
      split at compiled
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        refine ⟨rfl, ?_⟩
        rw [letsOf, List.foldr_append]
        rfl
      · cases compiled
      · split at compiled
        all_goals
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at compiled
          obtain ⟨rfl, rfl⟩ := compiled
          refine ⟨rfl, ?_⟩
          rw [letsOf, List.foldr_append]
          rfl

/-! ## The compiled site evaluates to the source site -/

theorem letsOf_cons (bind : Nat × Term) (binds : List (Nat × Term)) (body : Term) :
    letsOf (bind :: binds) body = .letE bind.1 bind.2 (letsOf binds body) := rfl

/-- `let`s of stable terms at symbols at or above `bound` evaluate as their
body with the values bound in order. -/
theorem letsOf_evaluates {module : Module} : ∀ (symbols : List Nat) (terms : List Term) (results : List Value)
    (values : Values) (bound : Nat) (body : Term) (value : Value),
    (∀ symbol ∈ symbols, bound ≤ symbol) → symbols.length = terms.length →
    AllPairs (fun term result => Stable module values bound term result) terms results →
    (Evaluates module values (letsOf (symbols.zip terms) body) value ↔
      Evaluates module (bindAll values symbols results) body value)
  | [], [], [], _, _, _, _, _, _, _ => Iff.rfl
  | symbol :: symbols, term :: terms, result :: results, values, bound, body, value, high, length, pairs => by
    have agrees := agrees_bindValue (values := values) result (high symbol (by simp))
    have rest := letsOf_evaluates symbols terms results (bindValue values symbol result) bound body value
      (fun other member => high other (by simp [member])) (by simpa using length)
      (pairs.2.imp fun _ _ stable => stable.extend agrees (Nat.le_refl _))
    rw [List.zip_cons_cons, letsOf_cons, letE_iff pairs.1.evaluates]
    exact rest
  | [], _ :: _, _, _, _, _, _, _, length, _ => by simp at length
  | _ :: _, [], _, _, _, _, _, _, length, _ => by simp at length
  | [], [], _ :: _, _, _, _, _, _, _, pairs => pairs.elim
  | _ :: _, _ :: _, [], _, _, _, _, _, _, pairs => pairs.elim

theorem compoundBinds_eq (next : Nat) (compound : List Term) :
    compoundBinds next compound = (pointSymbols next compound.length).zip compound := by
  apply List.ext_getElem
  · simp [compoundBinds, pointSymbols]
  · intro index first second
    simp [compoundBinds, pointSymbols, List.getElem_zipIdx]

theorem allPairs_getElem? {α β : Type} {relation : α → β → Prop} : ∀ {as : List α} {bs : List β},
    AllPairs relation as bs → ∀ {index : Nat} {a : α}, as[index]? = some a →
      ∃ b, bs[index]? = some b ∧ relation a b
  | [], [], _, _, _, found => by simp at found
  | _ :: _, _ :: _, pairs, index, _, found => by
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      exact ⟨_, rfl, pairs.1⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨b, at', holds⟩ := allPairs_getElem? pairs.2 found
      exact ⟨b, by simpa using at', holds⟩
  | [], _ :: _, pairs, _, _, _ => pairs.elim
  | _ :: _, [], pairs, _, _, _ => pairs.elim

theorem allPairs_exists_of_mem {α β : Type} {relation : α → β → Prop} : ∀ {as : List α} {bs : List β},
    AllPairs relation as bs → ∀ {a : α}, a ∈ as → ∃ b, relation a b
  | [], [], _, _, member => by cases member
  | _ :: _, _ :: _, pairs, _, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, pairs.1⟩
    · exact allPairs_exists_of_mem pairs.2 member
  | [], _ :: _, pairs, _, _ => pairs.elim
  | _ :: _, [], pairs, _, _ => pairs.elim

theorem allPairs_of_exists {α β : Type} {relation : α → β → Prop} :
    ∀ (as : List α), (∀ a ∈ as, ∃ b, relation a b) → ∃ bs, AllPairs relation as bs
  | [], _ => ⟨[], trivial⟩
  | a :: as, each => by
    obtain ⟨b, holds⟩ := each a (by simp)
    obtain ⟨bs, pairs⟩ := allPairs_of_exists as fun a' member => each a' (by simp [member])
    exact ⟨b :: bs, holds, pairs⟩

theorem allPairs_compose {α β γ : Type} {first : α → β → Prop} {second : β → γ → Prop} {both : α → γ → Prop}
    (compose : ∀ a b c, first a b → second b c → both a c) : ∀ {as : List α} {bs : List β} {cs : List γ},
    AllPairs first as bs → AllPairs second bs cs → AllPairs both as cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, left, right =>
    ⟨compose _ _ _ left.1 right.1, allPairs_compose compose left.2 right.2⟩
  | [], _ :: _, _, left, _ => left.elim
  | _ :: _, [], _, left, _ => left.elim
  | [], [], _ :: _, _, right => right.elim
  | _ :: _, _ :: _, [], _, right => right.elim

theorem bindAll_pointSymbols (values : Values) (first : Nat) {results : List Value} {index : Nat} {value : Value}
    (found : results[index]? = some value) :
    bindAll values (pointSymbols first results.length) results (first + index) = some value := by
  obtain ⟨lt, equal⟩ := List.getElem?_eq_some_iff.mp found
  have bound := bindAll_getElem values (pointSymbols first results.length) results (pointSymbols_nodup _ _)
    (pointSymbols_length _ _) index (by rw [pointSymbols_length]; exact lt) lt
  rw [pointSymbols_getElem] at bound
  rw [bound, equal]

/-- The operands that `siteOperands` reads, by the rule of the site: a
pullback in some mode, a differential, or the reverse pass of a tape that a
call with rule `tape` builds, directly or through a `let`. -/
theorem siteOperands_cases {env : Declarations} {defs : Defs} {id : DeclId} {arguments : List Term}
    {map point : Term} {seed : Option Term} {mode : PullbackMode}
    (operands : siteOperands env defs id arguments = some (map, point, seed, mode)) :
    (∃ seedTerm, ruleOf env id = .pass (.pullback mode) ∧ arguments = [map, point, seedTerm] ∧
      seed = some seedTerm) ∨
    (ruleOf env id = .pass .differential ∧ arguments = [map, point] ∧ seed = none ∧ mode = .saved) ∨
    (∃ tapeTerm seedTerm builder tapeResult, ruleOf env id = .pass .backward ∧ arguments = [tapeTerm, seedTerm] ∧
      seed = some seedTerm ∧ mode = .saved ∧ ruleOf env builder = .tape ∧
      (strip tapeTerm = .primitive builder [map, point] tapeResult ∨
        ∃ symbol variableResult definition, strip tapeTerm = .variable symbol variableResult ∧
          defs.find symbol = some definition ∧ strip definition.value = .primitive builder [map, point] tapeResult)) := by
  unfold siteOperands at operands
  cases rule : ruleOf env id with
  | pass kind =>
    rw [rule] at operands
    cases kind with
    | pullback pullbackMode =>
      match arguments, operands with
      | [mapTerm, pointTerm, seedTerm], operands =>
        simp only [Option.some.injEq, Prod.mk.injEq] at operands
        obtain ⟨rfl, rfl, rfl, rfl⟩ := operands
        exact Or.inl ⟨seedTerm, rfl, rfl, rfl⟩
      | [], operands | [_], operands | [_, _], operands | _ :: _ :: _ :: _ :: _, operands =>
        simp at operands
    | differential =>
      match arguments, operands with
      | [functionTerm, pointTerm], operands =>
        simp only [Option.some.injEq, Prod.mk.injEq] at operands
        obtain ⟨rfl, rfl, rfl, rfl⟩ := operands
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      | [], operands | [_], operands | _ :: _ :: _ :: _, operands => simp at operands
    | backward =>
      match arguments, operands with
      | [tapeTerm, seedTerm], operands =>
        simp only at operands
        split at operands
        · rename_i symbol variableResult isVariable
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at operands
          obtain ⟨⟨mapTerm, pointTerm⟩, found, operands⟩ := operands
          split at operands
          · simp only [Option.some.injEq, Prod.mk.injEq] at operands
            obtain ⟨rfl, rfl, rfl, rfl⟩ := operands
            obtain ⟨definition, defined, built⟩ := found
            split at built
            · split at built
              · simp only [Option.some.injEq, Prod.mk.injEq] at built
                obtain ⟨rfl, rfl⟩ := built
                exact Or.inr (Or.inr ⟨tapeTerm, seedTerm, _, _, rfl, rfl, rfl, rfl, ‹_›,
                  Or.inr ⟨symbol, variableResult, definition, isVariable, defined, ‹_›⟩⟩)
              · cases built
            · cases built
          · cases operands
        · simp only [Option.map_eq_some_iff] at operands
          obtain ⟨⟨mapTerm, pointTerm⟩, built, operands⟩ := operands
          simp only [Prod.mk.injEq] at operands
          obtain ⟨rfl, rfl, rfl, rfl⟩ := operands
          split at built
          · split at built
            · simp only [Option.some.injEq, Prod.mk.injEq] at built
              obtain ⟨rfl, rfl⟩ := built
              exact Or.inr (Or.inr ⟨tapeTerm, seedTerm, _, _, rfl, rfl, rfl, rfl, ‹_›, Or.inl ‹_›⟩)
            · cases built
          · cases built
      | [], operands | [_], operands | _ :: _ :: _ :: _, operands => simp at operands
  | none | morphism _ | chain _ _ | tape =>
    rw [rule] at operands
    cases operands

/-- **The Core that `compileSite` returns evaluates to the value of the
source site.** Let `compileSite` compile a site of a function whose `let`
definitions in scope agree with the activation (`DefsAgree`), and let the
module keep the source bindings and hold every entry of the ledger
(`EntryWellFormed`). Let the map operand that `siteOperands` reads evaluate to
a well-typed program, and the point and seed operands evaluate, none of them
reading a symbol at or above `state.next`, where the compiled Core binds its
own symbols. Then the source call and the returned term evaluate to the same
value. This covers a pullback in either mode, a differential, and the reverse
pass of a tape, direct or bound by a `let`. No chain rule is used. -/
theorem compiled_site_evaluates {module : Module} {env : Declarations} {defs : Defs} {state : State}
    {id : DeclId} {arguments : List Term} {result : Result} {term : Term} {state' : State}
    (compiled : compileSite env defs state id arguments result = some (term, state'))
    (rules : ∀ id binding, env.primitive? id = some binding → module.declarations.primitive? id = some binding)
    (wellFormed : ∀ entry ∈ state'.entries, EntryWellFormed module entry)
    {values : Values} (agree : DefsAgree module values state.next defs)
    {mapTerm pointTerm : Term} {seed : Option Term} {mode : PullbackMode}
    (operands : siteOperands env defs id arguments = some (mapTerm, pointTerm, seed, mode))
    {map x : Program} (mapStable : Stable module values state.next mapTerm (smoothValue map))
    {source target : Nat} (typed : map.wellTyped source target = true)
    (pointStable : Stable module values state.next pointTerm (smoothValue x))
    (seedStable : ∀ seedTerm, seed = some seedTerm →
      ∃ variance seedValue, Stable module values state.next seedTerm (.indexed (.fiber variance seedValue))) :
    ∃ value, Evaluates module values (.primitive id arguments result) value ∧ Evaluates module values term value := by
  obtain ⟨mapTerm', pointTerm', seed', tree, entry, compound, opaqueTerms, operands', treeCase, read, seedKind,
    -, compoundLeaves, opaqueArguments, entries, rfl⟩ := compileSite_term compiled
  simp only [operands, Option.some.injEq, Prod.mk.injEq] at operands'
  obtain ⟨rfl, rfl, rfl, modeIs⟩ := operands'
  have wf := wellFormed entry (by rw [entries]; simp)
  obtain ⟨opaques, opaqueStable, factors⟩ : ∃ opaques, AllPairs
      (fun leaf program => Stable module values state.next leaf (smoothValue program))
      (opaqueLeaves tree.leaves) opaques ∧ Factors map (leafPrograms tree.leaves opaques) := by
    rcases treeCase with ⟨rest, resolved⟩ | rfl
    · exact resolve_factors rules agree _ _ _ resolved mapStable typed
    · exact opaque_factors mapStable
  obtain ⟨programs, opaqueCount⟩ := stepsOf_programs read opaques
  rw [← programs] at factors
  have count : opaques.length = entry.site.opaqueSteps.length := opaqueStable.length.symm.trans opaqueCount.symm
  obtain ⟨results, compoundStable⟩ := allPairs_of_exists
    (relation := fun term value => Stable module values state.next term value) compound fun value member => by
      obtain ⟨program, stable⟩ := allPairs_exists_of_mem opaqueStable (compoundLeaves value member)
      exact ⟨_, stable⟩
  have lengths : compound.length = results.length := compoundStable.length
  have agrees : Agrees values (bindAll values (pointSymbols state.next compound.length) results) state.next :=
    bindAll_agrees values _ results fun _ member => pointSymbols_high _ member
  have enough : state.next ≤ state.next + compound.length := Nat.le_add_right _ _
  have opaqueEval : AllPairs (fun term program => Stable module
      (bindAll values (pointSymbols state.next compound.length) results) (state.next + compound.length) term
      (smoothValue program)) opaqueTerms opaques := by
    refine allPairs_compose (fun argument leaf program isArgument leafStable => ?_) opaqueArguments opaqueStable
    rcases isArgument with rfl | ⟨index, variableResult, atIndex, rfl⟩
    · exact leafStable.extend agrees enough
    · obtain ⟨held, heldAt, heldStable⟩ := allPairs_getElem? compoundStable atIndex
      have same := IndexedEvaluation.evaluates_unique heldStable.evaluates leafStable.evaluates
      subst same
      have lt : index < compound.length := (List.getElem?_eq_some_iff.mp atIndex).1
      refine stable_variable module variableResult (by omega) ?_
      rw [lengths]
      exact bindAll_pointSymbols values state.next heldAt
  have pointEval : Evaluates module (bindAll values (pointSymbols state.next compound.length) results) pointTerm
      (smoothValue x) := pointStable _ agrees
  have letsEval := fun body value => letsOf_evaluates (module := module) (pointSymbols state.next compound.length)
    compound results values state.next body value (fun _ member => pointSymbols_high _ member)
    (pointSymbols_length _ _) compoundStable
  rcases siteOperands_cases operands with ⟨seedTerm, rule, rfl, rfl⟩ | ⟨rule, rfl, rfl, rfl⟩ |
    ⟨tapeTerm, seedTerm, builder, tapeResult, rule, rfl, rfl, rfl, tapeRule, tapeShape⟩
  · obtain ⟨variance, seedValue, seedEval⟩ := seedStable seedTerm rfl
    refine ⟨_, pass_pullback_evaluates (ruleOf_transfer rules rule (by intro same; cases same)) mapStable.evaluates
      pointStable.evaluates seedEval.evaluates result, ?_⟩
    rw [compoundBinds_eq, letsEval]
    cases mode with
    | saved =>
      have saved : entry.site.mode = .saved := modeIs.symm
      simp only [siteBody, saved]
      rw [factors.pullback_chain .saved factors.composable]
      exact site_saved_core wf.function saved wf.apply wf.declared wf.formed wf.morphisms wf.nonempty opaqueEval count
        factors.composable (Nat.le_refl _) (by omega) (by omega) pointEval (seedEval.extend agrees enough) result
    | recomputed =>
      have recomputed : entry.site.mode = .recomputed := modeIs.symm
      simp only [siteBody, recomputed]
      rw [factors.pullback_chain .recomputed factors.composable]
      exact site_recomputed_core wf.function recomputed wf.apply wf.declared wf.formed wf.morphisms wf.nonempty
        opaqueEval count factors.composable (Nat.le_refl _) (by omega) pointEval (seedEval.extend agrees enough)
        result
  · refine ⟨_, pass_differential_evaluates (ruleOf_transfer rules rule (by intro same; cases same))
      mapStable.evaluates pointStable.evaluates result, ?_⟩
    rw [compoundBinds_eq, letsEval]
    have saved : entry.site.mode = .saved := modeIs.symm
    have unit : entry.seed = .unit := by simpa using seedKind
    obtain ⟨seedVariance, seedFamily⟩ := wf.seedFamily unit
    simp only [siteBody, saved]
    rw [VastitasOracle.SmoothRuntime.differential_eq_pullback, factors.pullback_chain .saved factors.composable,
      ← factors.coordinates_reach, reach_eq_getLastD]
    exact site_differential_core wf.function saved wf.apply wf.declared wf.formed wf.morphisms wf.nonempty
      (wf.seed unit) seedFamily opaqueEval count factors.composable (Nat.le_refl _) (by omega) (by omega) pointEval
      result
  · obtain ⟨variance, seedValue, seedEval⟩ := seedStable seedTerm rfl
    have built := tape_evaluates (ruleOf_transfer rules tapeRule (by intro same; cases same)) mapStable.evaluates
      pointStable.evaluates tapeResult
    have tapeEval : Evaluates module values tapeTerm
        (.indexed (.tape (VastitasKernel.SmoothRuntime.linearize map x))) := by
      rcases tapeShape with direct | ⟨symbol, variableResult, definition, isVariable, found, defined⟩
      · rw [← evaluates_strip, direct]
        exact built
      · have definedEval := (evaluates_strip definition.value).mp (by rw [defined]; exact built)
        unfold Defs.find at found
        obtain ⟨held, holds, heldStable⟩ := agree definition (List.mem_of_find?_eq_some found)
        have same := IndexedEvaluation.evaluates_unique heldStable.evaluates definedEval
        subst same
        have same := List.find?_some found
        simp only [beq_iff_eq] at same
        rw [same] at holds
        rw [← evaluates_strip, isVariable]
        exact IndexedEvaluation.variable_value holds
    refine ⟨_, pass_backward_evaluates (ruleOf_transfer rules rule (by intro same; cases same)) tapeEval
      seedEval.evaluates result, ?_⟩
    rw [compoundBinds_eq, letsEval, VastitasOracle.SmoothRuntime.backward_linearize]
    have saved : entry.site.mode = .saved := modeIs.symm
    simp only [siteBody, saved]
    rw [factors.pullback_chain .saved factors.composable]
    exact site_saved_core wf.function saved wf.apply wf.declared wf.formed wf.morphisms wf.nonempty opaqueEval count
      factors.composable (Nat.le_refl _) (by omega) (by omega) pointEval (seedEval.extend agrees enough) result

/-! ## Public paths -/

/-- **Protocol 7.** For every JSON that `Indexed.Wire.check` accepts, every
entry of the compiled module of the accepted certificate satisfies
`EntryComputes`. `Main.process` generates code from this module; that is read
from `Main`, which the oracle does not import. -/
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
accepts, every entry of both compiled modules of the certificate satisfies
`EntryComputes`: the pure program and the pure values of a resource entry.
`public_pure_entry_computes` links the first to the emitted code; the mixed
emit path generates its library from the second, which is read from the
kernel's code generation. -/
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
checked certificate. Every entry of its ledger satisfies `EntryComputes`
there. -/
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
