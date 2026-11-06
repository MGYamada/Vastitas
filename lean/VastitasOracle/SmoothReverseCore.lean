import VastitasKernel.IndexedReverse
import VastitasOracle.IndexedEvaluation
import VastitasOracle.SmoothJacobian
import VastitasOracle.SmoothCalculus

set_option autoImplicit false

/-! The semantics of compiled reverse Core (#623).

`Reverse.compileSite` replaces a reverse site by forward Core at the site and
a generated backward function (`Entry.generated`). This module states what
that Core evaluates to under the kernel evaluator, in the `Evaluates` form of
`IndexedEvaluation`, for every list of steps.

The maps of a site mean programs. `stepPrograms` reads the program of each
step: a declared map as one program node, an opaque step from the supplied
value. `chain` composes them in application order. `ResidualRel` relates the
saved points to the maps, and `Composable` states that adjacent dimensions
agree. `backwardPass` is the runtime value of the generated backward Core at
any points.

- `forwardLets_evaluates`, `forwardLets_primal` (F): the forward Core binds
  the evaluated images, which satisfy the residual relation; the last image
  has the coordinates of the primal value.
- `saved_function_evaluates`, `saved_function_pullback` (B): the saved
  function computes `backwardPass`, and, with the residual relation, the
  saved-mode pullback along the chain; `saved_function_foreign_seed`: a seed
  over another point gives `none`.
- `recomputed_function_evaluates`, `recomputed_function_pullback` (R) and
  `saved_eq_recomputed`.
- `pullback_chain_cot` and `saved_function_cot` (D): the value in coordinates.
  These two use the chain rule (`SmoothCalculus.backward_eq_cot`).
- `site_saved_core`, `site_recomputed_core`, `site_differential_core` (S): the
  Core that `compileSite` builds at a site evaluates to the pullback along the
  chain of the step programs. `site_saved_rewrite`, `site_recomputed_rewrite`,
  `site_differential_rewrite` and `site_tape_rewrite`: the source call and
  that Core evaluate to the same covector, for a map operand whose value is a
  composition tree of the step programs (`Factors`).

The other theorems use the stepwise pullback (`pullback_stepwise`), table steps
(`jacobianStep_eq_of_output`) and evaluated points, not `cot_compose` or
`backward_eq_cot`. The module imports `SmoothCalculus` for the two (D)
theorems, so this independence holds of the constants that each theorem uses,
not of the imports. `scripts/check_chain_rule_free.lean` checks it.

The premises about the module are hypotheses: `StepsDeclared`, `StepFormed`,
`MorphismsDeclared`, the declaration of `names.apply`, the lookup of the
generated function and, for a differential, the declaration of the seed and
the variance of its family. `SmoothReverseCompiled` proves them for every
entry of a compiled module. -/

namespace VastitasOracle.SmoothReverseCore

open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.Indexed.Core.Reverse (Site Step StepKind Names Pull stepBinding applyTerm stepTerm
  mapTerms forwardLets backwardChain pulls functionParameters backwardBody)
open VastitasKernel.SmoothRuntime (Program FiberValue Fiber PullbackMode pullback applyPoint coordinates
  jacobianStep jacobian)
open VastitasOracle.IndexedEvaluation (Evaluates ArgumentsEvaluate)

/-! ## The meaning of a site's maps -/

/-- The program of each step, in application order: the declared map as one
program node, or the next of the opaque map values. A missing opaque value
reads `default`; the theorems supply one value per opaque step. -/
def stepPrograms : List Step → List Program → List Program
  | [], _ => []
  | step :: rest, opaques =>
    match step.kind, opaques with
    | .declared _ _ map, _ => .primitive map :: stepPrograms rest opaques
    | .opaque, value :: more => value :: stepPrograms rest more
    | .opaque, [] => default :: stepPrograms rest []

/-- The program that maps in application order denote: `chain [m₁, m₂, …, m_k]`
is the program node `compose (chain [m₂, …, m_k]) m₁`, that is
`m_k ∘ ⋯ ∘ m₂ ∘ m₁`. The empty list reads `default`; the theorems require a
step. -/
def chain : List Program → Program
  | [] => default
  | [map] => map
  | map :: next :: rest => .compose (chain (next :: rest)) map

/-- Adjacent maps agree in dimension: the source dimension of each map is the
target dimension of the map before it. -/
def Composable : List Program → Prop
  | first :: second :: rest => second.inputArity = first.outputArity ∧ Composable (second :: rest)
  | _ => True

/-- Each map is well typed between consecutive dimensions: the first map from
`source` to the first target, and so on. -/
def StepsTyped : List Program → Nat → List Nat → Prop
  | [], _, [] => True
  | program :: programs, source, target :: targets =>
    program.wellTyped source target = true ∧ StepsTyped programs target targets
  | _, _, _ => False

/-- The declared steps carry their own maps: the program of a declared step is
its declared map as one program node, and there is one program per step. -/
def Matches : List Step → List Program → Prop
  | [], [] => True
  | step :: steps, program :: programs =>
    (∀ morphism application map, step.kind = .declared morphism application map → program = .primitive map) ∧
      Matches steps programs
  | _, _ => False

/-- The images of a point along the maps, as evaluated points:
`r₁ = applyPoint m₁ r₀`, `r₂ = applyPoint m₂ r₁`, and so on. -/
def images : List Program → Program → List Program
  | [], _ => []
  | map :: maps, point => applyPoint map point :: images maps (applyPoint map point)

/-- The residual relation of saved points `r₁, …, r_k` over the input point
`r₀`: point `rᵢ` has the coordinates of `mᵢ` at the coordinates of `rᵢ₋₁`, and
there is one point per map. -/
def ResidualRel : List Program → Program → List Program → Prop
  | [], _, [] => True
  | map :: maps, input, output :: outputs =>
    coordinates output = map.eval (coordinates input) ∧ ResidualRel maps output outputs
  | _, _, _ => False

/-- One backward step at runtime: its step, the program of its map, and its
input and saved output point. -/
structure StepPoint where
  step : Step
  program : Program
  input : Program
  output : Program

/-- What one backward step computes: the Jacobian table step of a declared map,
or the saved-mode reference pass along an opaque map value. -/
def StepPoint.pull (point : StepPoint) (seed : FiberValue) : FiberValue :=
  match point.step.kind with
  | .declared _ _ map => jacobianStep map.images.length (jacobian map) point.input point.output seed
  | .opaque => pullback .saved point.program point.input seed

/-- The backward steps of a site in application order, with their programs
and points. -/
def stepPoints : List Step → List Program → Program → List Program → List StepPoint
  | step :: steps, program :: programs, input, output :: outputs =>
    ⟨step, program, input, output⟩ :: stepPoints steps programs output outputs
  | _, _, _, _ => []

/-- The value of the generated backward Core at runtime, for any points: the
seed pulled back by the last step first. -/
def backwardPass (steps : List Step) (programs : List Program) (start : Program) (outputs : List Program)
    (seed : FiberValue) : FiberValue :=
  (stepPoints steps programs start outputs).foldr StepPoint.pull seed

/-! ## The runtime value without the chain rule -/

section Runtime

open VastitasOracle.SmoothRuntime VastitasOracle.SmoothJacobian

theorem stepPrograms_length : ∀ (steps : List Step) (opaques : List Program),
    (stepPrograms steps opaques).length = steps.length
  | [], _ => rfl
  | ⟨.declared _ _ _, _, _⟩ :: rest, opaques => by
    simp only [stepPrograms, List.length_cons, stepPrograms_length rest opaques]
  | ⟨.opaque, _, _⟩ :: rest, _ :: more => by
    simp only [stepPrograms, List.length_cons, stepPrograms_length rest more]
  | ⟨.opaque, _, _⟩ :: rest, [] => by
    simp only [stepPrograms, List.length_cons, stepPrograms_length rest []]

theorem matches_stepPrograms : ∀ (steps : List Step) (opaques : List Program),
    Matches steps (stepPrograms steps opaques)
  | [], _ => trivial
  | ⟨.declared _ _ _, _, _⟩ :: rest, opaques => by
    refine ⟨?_, matches_stepPrograms rest opaques⟩
    intro morphism application map equal
    cases equal
    rfl
  | ⟨.opaque, _, _⟩ :: rest, _ :: more => ⟨fun _ _ _ equal => (by cases equal), matches_stepPrograms rest more⟩
  | ⟨.opaque, _, _⟩ :: rest, [] => ⟨fun _ _ _ equal => (by cases equal), matches_stepPrograms rest []⟩

theorem chain_inputArity (first : Program) : ∀ rest : List Program, (chain (first :: rest)).inputArity = first.inputArity
  | [] => rfl
  | _ :: _ => rfl

/-- The maps of a well-typed chain are composable. -/
theorem composable_of_wellTyped : ∀ (programs : List Program) {source target : Nat},
    (chain programs).wellTyped source target = true → Composable programs
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial
  | first :: second :: rest, source, target, typed => by
    simp only [chain, Program.wellTyped, Bool.and_eq_true] at typed
    refine ⟨?_, composable_of_wellTyped (second :: rest) typed.2⟩
    rw [← chain_inputArity second rest]
    exact wellTyped_inputArity typed.2

/-- Maps well typed between consecutive dimensions make a well-typed chain from
the first dimension to the last. -/
theorem chain_wellTyped : ∀ (programs : List Program) (source : Nat) (targets : List Nat),
    programs ≠ [] → StepsTyped programs source targets →
      (chain programs).wellTyped source (targets.getLastD source) = true
  | [], _, _, nonempty, _ => absurd rfl nonempty
  | [program], source, [target], _, typed => by
    simpa [chain, StepsTyped] using typed.1
  | [_], _, [], _, typed => typed.elim
  | [_], _, _ :: _ :: _, _, typed => typed.2.elim
  | _ :: _ :: _, _, [], _, typed => typed.elim
  | first :: second :: rest, source, target :: targets, _, typed => by
    obtain ⟨typedFirst, typedRest⟩ := typed
    have inner := chain_wellTyped (second :: rest) target targets (by simp) typedRest
    simp only [chain, Program.wellTyped, Bool.and_eq_true]
    rw [wellTyped_outputArity typedFirst]
    rw [List.getLastD_cons]
    exact ⟨typedFirst, inner⟩

theorem images_length : ∀ (programs : List Program) (point : Program),
    (images programs point).length = programs.length
  | [], _ => rfl
  | _ :: programs, _ => by simp [images, images_length programs]

/-- The images along the first maps are the first images. -/
theorem images_take : ∀ (count : Nat) (programs : List Program) (point : Program),
    images (programs.take count) point = (images programs point).take count
  | 0, _, _ => by simp [images]
  | _ + 1, [], _ => by simp [images]
  | count + 1, _ :: programs, _ => by simp [images, images_take count programs]

/-- Evaluated images satisfy the residual relation. -/
theorem residualRel_images : ∀ (programs : List Program) (point : Program),
    ResidualRel programs point (images programs point)
  | [], _ => trivial
  | map :: maps, point => ⟨coordinates_applyPoint map point, residualRel_images maps _⟩

theorem StepPoint.pull_none (point : StepPoint) : point.pull none = none := by
  unfold StepPoint.pull
  split
  · rfl
  · exact pullback_none _ _ _

/-- **One step is the pullback along its program.** When the program of a
declared step is its declared map and the output point has the coordinates of
the program at the input point, the step is the saved-mode pullback along the
program at the input point, for every seed. -/
theorem StepPoint.pull_eq (point : StepPoint)
    (declared : ∀ morphism application map, point.step.kind = .declared morphism application map →
      point.program = .primitive map)
    (residual : coordinates point.output = point.program.eval (coordinates point.input)) (seed : FiberValue) :
    point.pull seed = pullback .saved point.program point.input seed := by
  obtain ⟨⟨kind, source, target⟩, program, input, output⟩ := point
  rcases kind with ⟨morphism, application, map⟩ | _
  · have equal : program = .primitive map := declared morphism application map rfl
    subst equal
    exact jacobianStep_eq_of_output .saved map input output residual seed
  · rfl

/-- **The generated backward pass is the pullback along the chain, without the
chain rule.** For maps that match the steps, are composable and satisfy the
residual relation with the saved points, the backward pass is the saved-mode
pullback along `chain programs` at the input point, for every seed. The proof
uses `jacobianStep_eq_of_output`, `pullback_stepwise_applyPoint` and
`pullback_congr_point` only. -/
theorem backwardPass_eq_pullback : ∀ (steps : List Step) (programs : List Program) (start : Program)
    (outputs : List Program) (seed : FiberValue),
    Matches steps programs → programs ≠ [] → Composable programs → ResidualRel programs start outputs →
      backwardPass steps programs start outputs seed = pullback .saved (chain programs) start seed
  | [], programs, _, _, _, matching, nonempty, _, _ => by
    cases programs <;> simp_all [Matches]
  | _ :: _, [], _, _, _, matching, _, _, _ => matching.elim
  | _ :: _, _ :: _, _, [], _, _, _, _, residual => residual.elim
  | [step], [program], start, [output], seed, matching, _, _, residual => by
    simp only [backwardPass, stepPoints, List.foldr_cons, List.foldr_nil, chain]
    exact StepPoint.pull_eq ⟨step, program, start, output⟩ matching.1 residual.1 seed
  | [_], [_], _, _ :: _ :: _, _, _, _, _, residual => residual.2.elim
  | [_], _ :: _ :: _, _, _, _, matching, _, _, _ => matching.2.elim
  | _ :: _ :: _, [_], _, _, _, matching, _, _, _ => matching.2.elim
  | step :: next :: steps, program :: second :: programs, start, output :: outputs, seed, matching, _,
      composable, residual => by
    have rest := backwardPass_eq_pullback (next :: steps) (second :: programs) output outputs seed matching.2
      (by simp) composable.2 residual.2
    have first := StepPoint.pull_eq ⟨step, program, start, output⟩ matching.1 residual.1
    have stepwise := pullback_stepwise_applyPoint .saved (chain (second :: programs)) program start seed
      (by rw [chain_inputArity]; exact composable.1)
    have moved : coordinates (applyPoint program start) = coordinates output := by
      rw [coordinates_applyPoint]; exact residual.1.symm
    simp only [backwardPass, stepPoints, List.foldr_cons] at rest ⊢
    rw [rest, first, chain, stepwise, pullback_congr_point .saved (chain (second :: programs)) moved]

theorem residual_length : ∀ {programs : List Program} {start : Program} {outputs : List Program},
    ResidualRel programs start outputs → programs.length = outputs.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, residual => by simp [residual_length residual.2]
  | [], _, _ :: _, residual => residual.elim
  | _ :: _, _, [], residual => residual.elim

/-- The last saved point of a residual chain has the coordinates of the chain
at the input point. -/
theorem residual_last : ∀ (programs : List Program) (start : Program) (outputs : List Program),
    programs ≠ [] → ResidualRel programs start outputs →
      coordinates (outputs.getLastD start) = (chain programs).eval (coordinates start)
  | [], _, _, nonempty, _ => absurd rfl nonempty
  | [_], _, [_], _, residual => residual.1
  | [_], _, [], _, residual => residual.elim
  | [_], _, _ :: _ :: _, _, residual => residual.2.elim
  | _ :: _ :: _, _, [], _, residual => residual.elim
  | program :: second :: programs, start, output :: outputs, _, residual => by
    have rest := residual_last (second :: programs) output outputs (by simp) residual.2
    rw [List.getLastD_cons, rest, residual.1]
    rfl

/-- **A seed over another point gives the failure value.** With the residual
relation, a seed that does not lie over the last saved point pulls back to
`none`, whatever the maps. No dimension premise is needed. -/
theorem backwardPass_foreign_seed : ∀ (steps : List Step) (programs : List Program) (start : Program)
    (outputs : List Program) (seed : Fiber),
    Matches steps programs → programs ≠ [] → ResidualRel programs start outputs →
      seed.point ≠ coordinates (outputs.getLastD start) →
      backwardPass steps programs start outputs (some seed) = none
  | [], programs, _, _, _, matching, nonempty, _, _ => by
    cases programs <;> simp_all [Matches]
  | _ :: _, [], _, _, _, matching, _, _, _ => matching.elim
  | _ :: _, _ :: _, _, [], _, _, _, residual, _ => residual.elim
  | [step], [program], start, [output], seed, matching, _, residual, foreign => by
    simp only [backwardPass, stepPoints, List.foldr_cons, List.foldr_nil]
    rw [StepPoint.pull_eq ⟨step, program, start, output⟩ matching.1 residual.1]
    exact pullback_wrong_point .saved program start seed (residual.1 ▸ foreign)
  | [_], [_], _, _ :: _ :: _, _, _, _, residual, _ => residual.2.elim
  | [_], _ :: _ :: _, _, _, _, matching, _, _, _ => matching.2.elim
  | _ :: _ :: _, [_], _, _, _, matching, _, _, _ => matching.2.elim
  | step :: next :: steps, program :: second :: programs, start, output :: outputs, seed, matching, _,
      residual, foreign => by
    have rest := backwardPass_foreign_seed (next :: steps) (second :: programs) output outputs seed matching.2
      (by simp) residual.2 (by rw [List.getLastD_cons] at foreign; exact foreign)
    simp only [backwardPass, stepPoints, List.foldr_cons] at rest ⊢
    rw [rest, StepPoint.pull_none]

/-- **A last opaque step reads no output point.** When the last step is
opaque, the backward pass does not depend on the last output point: outputs
that agree on every other point give the same value. -/
theorem backwardPass_last_opaque (steps : List Step) : ∀ (programs : List Program) (start : Program)
    (outputs outputs' : List Program) (seed : FiberValue),
    steps.getLast?.map Step.kind = some .opaque → outputs.length = steps.length →
    outputs'.length = steps.length → outputs.dropLast = outputs'.dropLast →
    backwardPass steps programs start outputs seed = backwardPass steps programs start outputs' seed := by
  induction steps with
  | nil => intro _ _ _ _ _ last; simp at last
  | cons step rest ih =>
    intro programs start outputs outputs' seed last length length' same
    rcases programs with _ | ⟨program, programs⟩
    · rfl
    rcases outputs with _ | ⟨output, outputs⟩
    · simp at length
    rcases outputs' with _ | ⟨output', outputs'⟩
    · simp at length'
    rcases rest with _ | ⟨second, rest⟩
    · obtain ⟨kind, source, target⟩ := step
      simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at last
      subst last
      have none : outputs = [] := by simpa using length
      have none' : outputs' = [] := by simpa using length'
      subst none none'
      rfl
    · have nonempty : outputs ≠ [] := by intro empty; subst empty; simp at length
      have nonempty' : outputs' ≠ [] := by intro empty; subst empty; simp at length'
      rw [List.dropLast_cons_of_ne_nil nonempty, List.dropLast_cons_of_ne_nil nonempty'] at same
      obtain ⟨rfl, tails⟩ := List.cons.inj same
      have restEq := ih programs output outputs outputs' seed (by simpa using last) (by simpa using length)
        (by simpa using length') tails
      simp only [backwardPass, stepPoints, List.foldr_cons] at restEq ⊢
      rw [restEq]

/-- **The value in coordinates (uses the chain rule).** For a well-typed chain
and a seed over its image with one component per target coordinate, the
pullback along the chain is `cot` of the composite map at the input point.
This uses `SmoothCalculus.backward_eq_cot`, the kernel chain rule. -/
theorem pullback_chain_cot (mode : PullbackMode) {programs : List Program} {source target : Nat}
    (typed : (chain programs).wellTyped source target = true) (start : Program) (seed : Fiber)
    (over : seed.point = (chain programs).eval (coordinates start)) (count : seed.components.length = target) :
    pullback mode (chain programs) start (some seed) =
      some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot (chain programs).denote (coordinates start)
        seed.components⟩ := by
  rw [pullback_spec, ite_eq_left ⟨over, by rw [count, wellTyped_outputArity typed]⟩,
    VastitasOracle.SmoothCalculus.backward_eq_cot typed]

end Runtime

/-! ## Evaluation tools -/

/-- A smooth program as a Core value. -/
abbrev smoothValue (program : Program) : Value := .indexed (.smooth program)

/-- `values'` agrees with `values` on every symbol below `bound`. -/
def Agrees (values values' : Values) (bound : Nat) : Prop :=
  ∀ symbol, symbol < bound → values' symbol = values symbol

/-- `term` evaluates to `value` in every activation that agrees with `values`
below `bound`: it reads no symbol at or above `bound`. -/
def Stable (module : Module) (values : Values) (bound : Nat) (term : Term) (value : Value) : Prop :=
  ∀ values', Agrees values values' bound → Evaluates module values' term value

theorem Agrees.refl (values : Values) (bound : Nat) : Agrees values values bound := fun _ _ => rfl

theorem agrees_bindValue {values : Values} {bound symbol : Nat} (value : Value) (high : bound ≤ symbol) :
    Agrees values (bindValue values symbol value) bound := by
  intro other low
  simp only [bindValue]
  rw [ite_eq_right (by omega)]

theorem Stable.evaluates {module : Module} {values : Values} {bound : Nat} {term : Term} {value : Value}
    (stable : Stable module values bound term value) : Evaluates module values term value :=
  stable values (Agrees.refl values bound)

/-- A stable term stays stable in an activation that agrees below the bound,
for every larger bound. -/
theorem Stable.extend {module : Module} {values values' : Values} {bound bound' : Nat} {term : Term}
    {value : Value} (stable : Stable module values bound term value) (agrees : Agrees values values' bound)
    (le : bound ≤ bound') : Stable module values' bound' term value := by
  intro values'' agrees''
  apply stable
  intro symbol low
  rw [agrees'' symbol (by omega), agrees symbol low]

theorem stable_variable (module : Module) {values : Values} {bound symbol : Nat} {value : Value} (result : Result)
    (low : symbol < bound) (found : values symbol = some value) :
    Stable module values bound (.variable symbol result) value := by
  intro values' agrees
  exact IndexedEvaluation.variable_value ((agrees symbol low).trans found)

/-- Evaluating a `let` is evaluating its body with the bound value. -/
theorem letE_iff {module : Module} {values : Values} {symbol : Nat} {operand body : Term}
    {boundValue value : Value} (operandEval : Evaluates module values operand boundValue) :
    Evaluates module values (.letE symbol operand body) value ↔
      Evaluates module (bindValue values symbol boundValue) body value := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := operandEval
    refine ⟨max a b, fun fuel enough => ?_⟩
    have observed := hb (fuel + 1) (by omega)
    simpa [eval, ha fuel (by omega)] using observed
  · exact IndexedEvaluation.letE operandEval

/-- Two lists related entry by entry. -/
def AllPairs {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => relation a b ∧ AllPairs relation as bs
  | _, _ => False

theorem AllPairs.length {α β : Type} {relation : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, AllPairs relation as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, pairs => by simp [pairs.2.length]
  | [], _ :: _, pairs => pairs.elim
  | _ :: _, [], pairs => pairs.elim

theorem AllPairs.imp {α β : Type} {relation relation' : α → β → Prop}
    (implies : ∀ a b, relation a b → relation' a b) :
    ∀ {as : List α} {bs : List β}, AllPairs relation as bs → AllPairs relation' as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, pairs => ⟨implies _ _ pairs.1, AllPairs.imp implies pairs.2⟩
  | [], _ :: _, pairs => pairs.elim
  | _ :: _, [], pairs => pairs.elim

theorem AllPairs.append {α β : Type} {relation : α → β → Prop} :
    ∀ {as as' : List α} {bs bs' : List β}, AllPairs relation as bs → AllPairs relation as' bs' →
      AllPairs relation (as ++ as') (bs ++ bs')
  | [], _, [], _, _, rest => rest
  | _ :: _, _, _ :: _, _, pairs, rest => ⟨pairs.1, AllPairs.append pairs.2 rest⟩
  | [], _, _ :: _, _, pairs, _ => pairs.elim
  | _ :: _, _, [], _, pairs, _ => pairs.elim

theorem AllPairs.take {α β : Type} {relation : α → β → Prop} :
    ∀ (count : Nat) {as : List α} {bs : List β}, AllPairs relation as bs →
      AllPairs relation (as.take count) (bs.take count)
  | 0, _, _, _ => by simp [AllPairs]
  | _ + 1, [], [], _ => trivial
  | count + 1, _ :: _, _ :: _, pairs => ⟨pairs.1, AllPairs.take count pairs.2⟩
  | _ + 1, [], _ :: _, pairs => pairs.elim
  | _ + 1, _ :: _, [], pairs => pairs.elim

theorem AllPairs.reverse {α β : Type} {relation : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, AllPairs relation as bs → AllPairs relation as.reverse bs.reverse
  | [], [], _ => trivial
  | _ :: _, _ :: _, pairs => by
    simp only [List.reverse_cons]
    exact AllPairs.append pairs.2.reverse ⟨pairs.1, trivial⟩
  | [], _ :: _, pairs => pairs.elim
  | _ :: _, [], pairs => pairs.elim

theorem allPairs_of_getElem {α β : Type} {relation : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length →
      (∀ i (ha : i < as.length) (hb : i < bs.length), relation as[i] bs[i]) → AllPairs relation as bs
  | [], [], _, _ => trivial
  | a :: as, b :: bs, length, each =>
    ⟨each 0 (by simp) (by simp), allPairs_of_getElem (by simpa using length)
      fun i ha hb => each (i + 1) (by simpa using ha) (by simpa using hb)⟩
  | [], _ :: _, length, _ => by simp at length
  | _ :: _, [], length, _ => by simp at length

/-- Bind values to symbols in order: later bindings shadow earlier ones. -/
def bindAll (values : Values) : List Nat → List Value → Values
  | symbol :: symbols, value :: rest => bindAll (bindValue values symbol value) symbols rest
  | _, _ => values

theorem bindAll_agrees {bound : Nat} : ∀ (values : Values) (symbols : List Nat) (bound_values : List Value),
    (∀ symbol ∈ symbols, bound ≤ symbol) → Agrees values (bindAll values symbols bound_values) bound
  | values, symbol :: symbols, value :: rest, high => by
    intro other low
    simp only [bindAll]
    rw [bindAll_agrees _ symbols rest (fun s member => high s (by simp [member])) other low,
      agrees_bindValue value (high symbol (by simp)) other low]
  | values, [], _, _ => Agrees.refl values bound
  | values, _ :: _, [], _ => Agrees.refl values bound

theorem bindAll_not_mem : ∀ (values : Values) (symbols : List Nat) (bound_values : List Value) (symbol : Nat),
    symbol ∉ symbols → bindAll values symbols bound_values symbol = values symbol
  | values, other :: symbols, value :: rest, symbol, absent => by
    simp only [bindAll]
    rw [bindAll_not_mem _ symbols rest symbol (by simp_all)]
    simp only [bindValue]
    rw [ite_eq_right (by simp_all)]
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl

theorem bindAll_getElem : ∀ (values : Values) (symbols : List Nat) (bound_values : List Value),
    symbols.Nodup → symbols.length = bound_values.length →
      ∀ i (hs : i < symbols.length) (hv : i < bound_values.length),
        bindAll values symbols bound_values symbols[i] = some bound_values[i]
  | values, symbol :: symbols, value :: rest, nodup, length, i, hs, hv => by
    simp only [bindAll]
    rw [List.nodup_cons] at nodup
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [bindAll_not_mem _ symbols rest symbol nodup.1]
      simp [bindValue]
    | succ i =>
      simp only [List.getElem_cons_succ]
      exact bindAll_getElem _ symbols rest nodup.2 (by simpa using length) i (by simpa using hs) (by simpa using hv)
  | _, [], _, _, _, _, hs, _ => absurd hs (by simp)
  | _, _ :: _, [], _, _, _, _, hv => absurd hv (by simp)

/-- Parameters numbered from `start` by `zipIdx` have the symbols
`start, start + 1, …`. -/
theorem zipIdx_symbols (number : Result × Nat → Core.Parameter) (numbered : ∀ pair, (number pair).symbol = pair.2) :
    ∀ (results : List Result) (start : Nat),
      ((results.zipIdx start).map number).map Core.Parameter.symbol =
        List.range' start ((results.zipIdx start).map number).length
  | [], _ => rfl
  | result :: results, start => by
    have rest := zipIdx_symbols number numbered results (start + 1)
    simp only [List.zipIdx_cons, List.map_cons, List.length_cons, List.range'_succ, numbered, rest]

/-- `bindArguments` over parameters with the symbols `start, start + 1, …`
binds symbol `start + i` to the `i`-th value, and nothing else. -/
theorem bindArguments_symbols : ∀ (parameters : List Core.Parameter) (arguments : List Value) (start : Nat),
    parameters.map Core.Parameter.symbol = List.range' start parameters.length →
    parameters.length = arguments.length →
    bindArguments parameters arguments = some (fun symbol => if start ≤ symbol then arguments[symbol - start]? else none)
  | [], [], start, _, _ => by
    simp only [bindArguments, Option.some.injEq]
    funext symbol
    split <;> simp
  | parameter :: parameters, argument :: arguments, start, symbols, length => by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at symbols
    rw [bindArguments, bindArguments_symbols parameters arguments (start + 1) symbols.2 (by simpa using length)]
    refine congrArg some (funext fun symbol => ?_)
    simp only [bindValue, symbols.1]
    rcases Nat.lt_trichotomy symbol start with low | rfl | high
    · simp [show symbol ≠ start by omega, show ¬start + 1 ≤ symbol by omega, show ¬start ≤ symbol by omega]
    · simp
    · obtain ⟨offset, rfl⟩ : ∃ offset, symbol = start + 1 + offset := ⟨symbol - (start + 1), by omega⟩
      simp [show start + 1 + offset ≠ start by omega, show start ≤ start + 1 + offset by omega,
        show start + 1 + offset - start = offset + 1 by omega, show start + 1 + offset - (start + 1) = offset by omega]
  | [], _ :: _, _, _, length => by simp at length
  | _ :: _, [], _, _, length => by simp at length

/-- The parameters of a generated function have the symbols `0, 1, …`. -/
theorem functionParameters_symbols (site : Site) :
    (functionParameters site).map Core.Parameter.symbol = List.range' 0 (functionParameters site).length := by
  unfold functionParameters
  exact zipIdx_symbols (fun pair => ⟨pair.2, pair.1⟩) (fun _ => rfl) _ 0

/-- Binding the parameters of a generated function maps symbol `i` to the
`i`-th argument. -/
theorem bindArguments_functionParameters (site : Site) (arguments : List Value)
    (length : (functionParameters site).length = arguments.length) :
    bindArguments (functionParameters site) arguments = some (fun symbol => arguments[symbol]?) := by
  rw [bindArguments_symbols _ arguments 0 (functionParameters_symbols site) length]
  simp

/-! ## Hypotheses on the module -/

/-- The map type of a declared step names two objects, as `stepsOf` builds it. -/
def StepFormed (step : Step) : Prop :=
  ∀ morphism application map, step.kind = .declared morphism application map →
    ∃ source target, application.indices = [.object source, .object target]

/-- The module declares `id` as the backward step of kind `kind` of the site,
in some residual policy: `cotangentJacobian` for a declared map, and
`cotangentPullback` in either mode for an opaque one. The kernel declares an
opaque step in the site's own policy; both modes have the same value
(`pullback_saved_eq`), so the theorems accept either, and a saved site and the
same site recomputing share their declarations. -/
def StepDeclaredAs (module : Module) (site : Site) (id : DeclId) (kind : StepKind) : Prop :=
  ∃ mode, module.declarations.primitive? id = some (stepBinding { site with mode } kind)

/-- The module declares the backward step of every map of the site under the
name the site gives it (`StepDeclaredAs`). -/
def StepsDeclared (module : Module) (names : Names) (site : Site) : Prop :=
  ∀ id step, (id, step) ∈ names.steps.zip site.steps → StepDeclaredAs module site id step.kind

/-- Every declared map is a declaration whose derivative rule is `morphism`
with the step's map: the nullary call of the declaration is the map. -/
def MorphismsDeclared (module : Module) (steps : List Step) : Prop :=
  ∀ step ∈ steps, ∀ morphism application map, step.kind = .declared morphism application map →
    Reverse.ruleOf module.declarations morphism = .morphism map

/-! ## The steps evaluate -/

/-- The forward step evaluates the image of the point as an evaluated point. -/
theorem applyTerm_evaluates {module : Module} {names : Names} {site : Site} {values : Values}
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth)) (step : Step)
    {map previous : Term} {program point : Program}
    (mapEval : Evaluates module values map (smoothValue program))
    (pointEval : Evaluates module values previous (smoothValue point)) :
    Evaluates module values (applyTerm names site step map previous) (smoothValue (applyPoint program point)) :=
  IndexedEvaluation.primitive apply
    (IndexedEvaluation.arguments_cons mapEval
      (IndexedEvaluation.arguments_cons pointEval (IndexedEvaluation.arguments_nil _ _))) rfl

/-- The nullary call of a declaration with derivative rule `morphism map`
evaluates to `map` as one program node, in every activation. -/
theorem morphism_evaluates {module : Module} {morphism : DeclId} {map : VastitasKernel.AlgebraRuntime.Map}
    (rule : Reverse.ruleOf module.declarations morphism = .morphism map) (values : Values) (result : Result) :
    Evaluates module values (.primitive morphism [] result) (smoothValue (.primitive map)) := by
  unfold Reverse.ruleOf at rule
  split at rule
  · rename_i binding found
    have sound := SmoothJacobian.registry_reverse_sound binding
    unfold SmoothJacobian.ReverseSound at sound
    rw [rule] at sound
    exact IndexedEvaluation.primitive found (IndexedEvaluation.arguments_nil _ _)
      ((sound module.declarations.indexed [] _).mpr ⟨rfl, rfl⟩)
  · cases rule

/-- The runtime reverse pass has the same value in both residual policies. -/
theorem pullback_saved_eq (mode : PullbackMode) (map point : Program) (seed : FiberValue) :
    pullback .saved map point seed = pullback mode map point seed := by
  cases mode
  · rfl
  · exact VastitasOracle.SmoothRuntime.pullback_saved_eq_recomputed map point seed

/-- One backward step of the generated Core evaluates to `StepPoint.pull`. An
opaque step runs the reverse pass in the site's policy, which has the value of
the saved one (`pullback_saved_eq`). -/
theorem stepTerm_evaluates {module : Module} {site : Site} {values : Values} {id : DeclId} {step : Step}
    {map input output seedTerm : Term} {point : StepPoint} {variance : Variance} {seed : FiberValue}
    (same : point.step = step) (binding : StepDeclaredAs module site id step.kind)
    (formed : StepFormed step)
    (mapEval : step.kind = .opaque → Evaluates module values map (smoothValue point.program))
    (inputEval : Evaluates module values input (smoothValue point.input))
    (outputEval : Evaluates module values output (smoothValue point.output))
    (seedEval : Evaluates module values seedTerm (.indexed (.fiber variance seed))) :
    Evaluates module values (stepTerm site id step map input output seedTerm)
      (.indexed (.fiber .cotangent (point.pull seed))) := by
  subst same
  obtain ⟨mode, binding⟩ := binding
  obtain ⟨⟨kind, source, target⟩, program, inputPoint, outputPoint⟩ := point
  rcases kind with ⟨morphism, ⟨family, indices⟩, mapData⟩ | _
  · obtain ⟨objectSource, objectTarget, shape⟩ := formed morphism _ mapData rfl
    simp only at shape
    subst shape
    exact IndexedEvaluation.primitive binding
      (IndexedEvaluation.arguments_cons inputEval (IndexedEvaluation.arguments_cons outputEval
        (IndexedEvaluation.arguments_cons seedEval (IndexedEvaluation.arguments_nil _ _)))) rfl
  · refine IndexedEvaluation.primitive binding
      (IndexedEvaluation.arguments_cons (mapEval rfl) (IndexedEvaluation.arguments_cons inputEval
        (IndexedEvaluation.arguments_cons seedEval (IndexedEvaluation.arguments_nil _ _)))) ?_
    show (some (Value.indexed (.fiber .cotangent (pullback mode program inputPoint seed))) : Option Value) = _
    rw [← pullback_saved_eq mode program inputPoint seed]
    rfl

/-- A backward step of the generated Core and its runtime step: the step and
its declaration, and its map (for an opaque step), input and output terms read
no symbol at or above `bound`. -/
def PullDenotes (module : Module) (site : Site) (values : Values) (bound : Nat) (pull : Pull)
    (point : StepPoint) : Prop :=
  point.step = pull.2.1 ∧ StepDeclaredAs module site pull.1 pull.2.1.kind ∧
    StepFormed pull.2.1 ∧
    (pull.2.1.kind = .opaque → Stable module values bound pull.2.2.1 (smoothValue point.program)) ∧
    Stable module values bound pull.2.2.2.1 (smoothValue point.input) ∧
    Stable module values bound pull.2.2.2.2 (smoothValue point.output)

theorem PullDenotes.extend {module : Module} {site : Site} {values values' : Values} {bound bound' : Nat}
    {pull : Pull} {point : StepPoint} (denotes : PullDenotes module site values bound pull point)
    (agrees : Agrees values values' bound) (le : bound ≤ bound') :
    PullDenotes module site values' bound' pull point := by
  obtain ⟨same, binding, formed, mapS, inputS, outputS⟩ := denotes
  exact ⟨same, binding, formed, fun isOpaque => (mapS isOpaque).extend agrees le, inputS.extend agrees le,
    outputS.extend agrees le⟩

/-- **The backward chain.** `backwardChain` over pulls that denote runtime
steps evaluates to the seed pulled back by the steps in the order of the list:
the first pull acts first. Each intermediate covector is bound to the next
symbol, at or above `next`, which no pull term reads. -/
theorem backwardChain_evaluates {module : Module} {site : Site} :
    ∀ (pullList : List Pull) (points : List StepPoint) (values : Values) (next : Nat) (seedTerm : Term)
      (variance : Variance) (seed : FiberValue),
      AllPairs (PullDenotes module site values next) pullList points → pullList ≠ [] →
      Evaluates module values seedTerm (.indexed (.fiber variance seed)) →
      Evaluates module values (backwardChain site pullList seedTerm next)
        (.indexed (.fiber .cotangent (points.foldl (fun current point => point.pull current) seed)))
  | [], _, _, _, _, _, _, _, nonempty, _ => absurd rfl nonempty
  | [(id, step, map, input, output)], [point], values, next, seedTerm, variance, seed, denotes, _, seedEval => by
    obtain ⟨⟨same, binding, formed, mapS, inputS, outputS⟩, -⟩ := denotes
    exact stepTerm_evaluates same binding formed (fun isOpaque => (mapS isOpaque).evaluates) inputS.evaluates
      outputS.evaluates seedEval
  | [_], [], _, _, _, _, _, denotes, _, _ => denotes.elim
  | [_], _ :: _ :: _, _, _, _, _, _, denotes, _, _ => denotes.2.elim
  | _ :: _ :: _, [], _, _, _, _, _, denotes, _, _ => denotes.elim
  | _ :: _ :: _, [_], _, _, _, _, _, denotes, _, _ => denotes.2.elim
  | (id, step, map, input, output) :: second :: rest, point :: second' :: points, values, next, seedTerm, variance,
      seed, denotes, _, seedEval => by
    obtain ⟨⟨same, binding, formed, mapS, inputS, outputS⟩, restDenotes⟩ := denotes
    have first := stepTerm_evaluates (map := map) same binding formed (fun isOpaque => (mapS isOpaque).evaluates)
      inputS.evaluates outputS.evaluates seedEval
    have agrees := agrees_bindValue (values := values) (.indexed (.fiber .cotangent (point.pull seed)))
      (Nat.le_refl next)
    have rest := backwardChain_evaluates (second :: rest) (second' :: points)
      (bindValue values next (.indexed (.fiber .cotangent (point.pull seed)))) (next + 1)
      (.variable next (Reverse.fiberResult site step.source)) .cotangent (point.pull seed)
      (restDenotes.imp fun _ _ denotes => denotes.extend agrees (Nat.le_succ next)) (by simp)
      (IndexedEvaluation.variable_value (by simp [bindValue]))
    exact IndexedEvaluation.letE first rest

/-! ## The backward Core of a site -/

/-- The pulls of a site in application order: the declaration, step, map term,
input and output point terms of each step. -/
def appPulls : List DeclId → List Step → List Term → List Term → List Pull
  | id :: ids, step :: steps, map :: maps, input :: output :: points =>
    (id, step, map, input, output) :: appPulls ids steps maps (output :: points)
  | _, _, _, _ => []

/-- `pulls` lists the steps last first: it is the reverse of `appPulls`. -/
theorem pulls_eq (names : Names) (site : Site) (maps points : List Term) :
    pulls names site maps points = (appPulls names.steps site.steps maps points).reverse := by
  unfold pulls
  rw [List.map_reverse]
  congr 1
  generalize names.steps = ids
  generalize site.steps = steps
  induction ids generalizing steps maps points with
  | nil => simp [appPulls]
  | cons id ids ih =>
    cases steps with
    | nil => simp [appPulls]
    | cons step steps =>
      cases maps with
      | nil => simp [appPulls]
      | cons map maps =>
        rcases points with _ | ⟨input, _ | ⟨output, points⟩⟩
        · simp [appPulls]
        · simp [appPulls]
        · have rest := ih (steps := steps) (maps := maps) (points := output :: points)
          simp only [List.zip_cons_cons, List.tail_cons, List.map_cons, appPulls, List.cons.injEq, true_and] at rest ⊢
          exact rest

/-- The map terms of the steps, against the step programs: the term of every
opaque step evaluates to its program. -/
def StepMaps (module : Module) (values : Values) (bound : Nat) : List Step → List Term → List Program → Prop
  | [], [], [] => True
  | step :: steps, map :: maps, program :: programs =>
    (step.kind = .opaque → Stable module values bound map (smoothValue program)) ∧
      StepMaps module values bound steps maps programs
  | _, _, _ => False

theorem StepMaps.extend {module : Module} {values values' : Values} {bound bound' : Nat}
    (agrees : Agrees values values' bound) (le : bound ≤ bound') :
    ∀ {steps : List Step} {maps : List Term} {programs : List Program},
      StepMaps module values bound steps maps programs → StepMaps module values' bound' steps maps programs
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, _ :: _, denote => ⟨fun isOpaque => (denote.1 isOpaque).extend agrees le, StepMaps.extend agrees le denote.2⟩
  | [], [], _ :: _, denote => denote.elim
  | [], _ :: _, _, denote => denote.elim
  | _ :: _, [], _, denote => denote.elim
  | _ :: _, _ :: _, [], denote => denote.elim

theorem stepMaps_of_allPairs {module : Module} {values : Values} {bound : Nat} :
    ∀ {steps : List Step} {maps : List Term} {programs : List Program}, steps.length = maps.length →
      AllPairs (fun map program => Stable module values bound map (smoothValue program)) maps programs →
      StepMaps module values bound steps maps programs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, length, pairs =>
    ⟨fun _ => pairs.1, stepMaps_of_allPairs (by simpa using length) pairs.2⟩
  | [], _ :: _, _, length, _ => by simp at length
  | _ :: _, [], _, length, _ => by simp at length
  | _, [], _ :: _, _, pairs => pairs.elim
  | _, _ :: _, [], _, pairs => pairs.elim

/-- The map terms that `mapTerms` builds, from opaque terms that evaluate to
the opaque values: each opaque step's term evaluates to its program. -/
theorem stepMaps_mapTerms {module : Module} {values : Values} {bound : Nat} :
    ∀ (steps : List Step) (opaqueTerms : List Term) (opaques : List Program),
      AllPairs (fun term program => Stable module values bound term (smoothValue program)) opaqueTerms opaques →
      opaques.length = (steps.filter fun step => step.kind == .opaque).length →
      StepMaps module values bound steps (mapTerms steps opaqueTerms) (stepPrograms steps opaques)
  | [], _, _, _, _ => trivial
  | ⟨.declared _ _ _, _, _⟩ :: rest, opaqueTerms, opaques, pairs, count =>
    ⟨fun isOpaque => (by cases isOpaque), stepMaps_mapTerms rest opaqueTerms opaques pairs (by simpa using count)⟩
  | ⟨.opaque, _, _⟩ :: rest, term :: terms, program :: programs, pairs, count =>
    ⟨fun _ => pairs.1, stepMaps_mapTerms rest terms programs pairs.2 (by simpa using count)⟩
  | ⟨.opaque, _, _⟩ :: _, [], [], _, count => by simp at count
  | ⟨.opaque, _, _⟩ :: _, _ :: _, [], pairs, _ => pairs.elim
  | ⟨.opaque, _, _⟩ :: _, [], _ :: _, pairs, _ => pairs.elim

/-- The same with declared maps: every map term evaluates to its program. -/
theorem allPairs_mapTerms {module : Module} {values : Values} {bound : Nat} :
    ∀ (steps : List Step), MorphismsDeclared module steps → ∀ (opaqueTerms : List Term) (opaques : List Program),
      AllPairs (fun term program => Stable module values bound term (smoothValue program)) opaqueTerms opaques →
      opaques.length = (steps.filter fun step => step.kind == .opaque).length →
      AllPairs (fun term program => Stable module values bound term (smoothValue program))
        (mapTerms steps opaqueTerms) (stepPrograms steps opaques)
  | [], _, _, _, _, _ => trivial
  | ⟨.declared morphism application map, source, target⟩ :: rest, morphisms, opaqueTerms, opaques, pairs, count =>
    ⟨fun values' _ => morphism_evaluates (morphisms ⟨.declared morphism application map, source, target⟩
        List.mem_cons_self morphism application map rfl) values' _,
      allPairs_mapTerms rest (fun step member => morphisms step (by simp [member])) opaqueTerms opaques pairs
        (by simpa using count)⟩
  | ⟨.opaque, _, _⟩ :: rest, morphisms, term :: terms, program :: programs, pairs, count =>
    ⟨pairs.1, allPairs_mapTerms rest (fun step member => morphisms step (by simp [member])) terms programs pairs.2
      (by simpa using count)⟩
  | ⟨.opaque, _, _⟩ :: _, _, [], [], _, count => by simp at count
  | ⟨.opaque, _, _⟩ :: _, _, _ :: _, [], pairs, _ => pairs.elim
  | ⟨.opaque, _, _⟩ :: _, _, [], _ :: _, pairs, _ => pairs.elim

theorem mapTerms_length : ∀ (steps : List Step) (opaqueTerms : List Term),
    (mapTerms steps opaqueTerms).length = steps.length
  | [], _ => rfl
  | ⟨.declared _ _ _, _, _⟩ :: rest, opaqueTerms => by simp [mapTerms, mapTerms_length rest opaqueTerms]
  | ⟨.opaque, _, _⟩ :: rest, _ :: more => by simp [mapTerms, mapTerms_length rest more]
  | ⟨.opaque, _, _⟩ :: rest, [] => by simp [mapTerms, mapTerms_length rest []]

theorem stepPoints_length : ∀ (steps : List Step) (programs : List Program) (start : Program) (outputs : List Program),
    programs.length = steps.length → outputs.length = steps.length →
      (stepPoints steps programs start outputs).length = steps.length
  | [], _, _, _, _, _ => by simp [stepPoints]
  | _ :: steps, _ :: programs, _, _ :: outputs, lp, lo => by
    simp only [stepPoints, List.length_cons]
    rw [stepPoints_length steps programs _ outputs (by simpa using lp) (by simpa using lo)]
  | _ :: _, [], _, _, lp, _ => by simp at lp
  | _ :: _, _ :: _, _, [], _, lo => by simp at lo

/-- The pulls of a site in application order denote its runtime steps. -/
theorem appPulls_denote {module : Module} {site : Site} {values : Values} {bound : Nat} :
    ∀ (ids : List DeclId) (steps : List Step) (maps : List Term) (programs : List Program) (startTerm : Term)
      (start : Program) (outputTerms : List Term) (outputs : List Program),
      ids.length = steps.length →
      (∀ id step, (id, step) ∈ ids.zip steps → StepDeclaredAs module site id step.kind) →
      (∀ step ∈ steps, StepFormed step) →
      StepMaps module values bound steps maps programs →
      Stable module values bound startTerm (smoothValue start) →
      AllPairs (fun term point => Stable module values bound term (smoothValue point)) outputTerms outputs →
      outputs.length = steps.length →
      AllPairs (PullDenotes module site values bound) (appPulls ids steps maps (startTerm :: outputTerms))
        (stepPoints steps programs start outputs)
  | _, [], [], [], _, _, [], [], _, _, _, _, _, _, _ => by simp [appPulls, stepPoints, AllPairs]
  | id :: ids, step :: steps, map :: maps, program :: programs, startTerm, start, outputTerm :: outputTerms,
      output :: outputs, length, declared, formed, maps', startS, outputsS, count =>
    ⟨⟨rfl, declared id step (by simp), formed step (by simp), maps'.1, startS, outputsS.1⟩,
      appPulls_denote ids steps maps programs outputTerm output outputTerms outputs (by simpa using length)
        (fun id' step' member => declared id' step' (by simp [member])) (fun step' member => formed step' (by simp [member]))
        maps'.2 outputsS.1 outputsS.2 (by simpa using count)⟩
  | [], _ :: _, _, _, _, _, _, _, length, _, _, _, _, _, _ => by simp at length
  | _, _ :: _, [], _, _, _, _, _, _, _, _, maps', _, _, _ => maps'.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, _, _, _, maps', _, _, _ => maps'.elim
  | _, _ :: _, _ :: _, _ :: _, _, _, _, [], _, _, _, _, _, _, count => by simp at count
  | _, _ :: _, _ :: _, _ :: _, _, _, [], _ :: _, _, _, _, _, _, outputsS, _ => outputsS.elim
  | _, [], _, _, _, _, _ :: _, _, _, _, _, _, _, outputsS, count => by
    cases outputsS.length ▸ count
  | _, [], _ :: _, _, _, _, [], [], _, _, _, maps', _, _, _ => maps'.elim
  | _, [], [], _ :: _, _, _, [], [], _, _, _, maps', _, _, _ => maps'.elim

theorem stepPrograms_ne_nil {steps : List Step} (nonempty : steps ≠ []) (opaques : List Program) :
    stepPrograms steps opaques ≠ [] := by
  intro empty
  have length := stepPrograms_length steps opaques
  rw [empty] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length.symm)

/-- **The backward chain of a site.** The backward Core that `backwardBody`
builds from map, point and seed terms evaluates to `backwardPass`: the opaque
terms evaluate to the opaque values, the point terms to the points, the seed
term to the seed, and the chain binds its covectors at or above `bound`, which
no term reads. -/
theorem siteChain_evaluates {module : Module} {names : Names} {site : Site} {values : Values} (bound : Nat)
    (declared : StepsDeclared module names site) (length : names.steps.length = site.steps.length)
    (formed : ∀ step ∈ site.steps, StepFormed step) (nonempty : site.steps ≠ [])
    {opaqueTerms : List Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = site.opaqueSteps.length)
    {startTerm : Term} {start : Program} (startEval : Stable module values bound startTerm (smoothValue start))
    {outputTerms : List Term} {outputs : List Program}
    (outputEval : AllPairs (fun term point => Stable module values bound term (smoothValue point)) outputTerms outputs)
    (outputCount : outputs.length = site.steps.length)
    {seedTerm : Term} {variance : Variance} {seed : FiberValue}
    (seedEval : Evaluates module values seedTerm (.indexed (.fiber variance seed))) :
    Evaluates module values
      (backwardChain site (pulls names site (mapTerms site.steps opaqueTerms) (startTerm :: outputTerms)) seedTerm bound)
      (.indexed (.fiber .cotangent (backwardPass site.steps (stepPrograms site.steps opaques) start outputs seed))) := by
  have maps := stepMaps_mapTerms (module := module) (values := values) (bound := bound) site.steps opaqueTerms
    opaques opaqueEval count
  have denote := appPulls_denote names.steps site.steps (mapTerms site.steps opaqueTerms)
    (stepPrograms site.steps opaques) startTerm start outputTerms outputs length declared formed maps startEval
    outputEval outputCount
  have pointsLength := stepPoints_length site.steps (stepPrograms site.steps opaques) start outputs
    (stepPrograms_length _ _) outputCount
  have nonemptyPulls : (appPulls names.steps site.steps (mapTerms site.steps opaqueTerms)
      (startTerm :: outputTerms)).reverse ≠ [] := by
    intro empty
    have lengths := denote.length
    rw [List.reverse_eq_nil_iff.mp empty, pointsLength] at lengths
    exact nonempty (List.eq_nil_of_length_eq_zero lengths.symm)
  have chainEval := backwardChain_evaluates _ _ values bound seedTerm variance seed denote.reverse nonemptyPulls
    seedEval
  rw [List.foldl_reverse] at chainEval
  rw [pulls_eq]
  exact chainEval

/-! ## The generated function -/

/-- The arguments of a generated function: the opaque map values, the points
and the seed, in the order of `functionParameters`. -/
def functionArguments (opaques points : List Program) (variance : Variance) (seed : FiberValue) : List Value :=
  opaques.map smoothValue ++ points.map smoothValue ++ [.indexed (.fiber variance seed)]

theorem functionArguments_opaque (opaques points : List Program) (variance : Variance) (seed : FiberValue)
    (i : Nat) (h : i < opaques.length) :
    (functionArguments opaques points variance seed)[i]? = some (smoothValue opaques[i]) := by
  unfold functionArguments
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp [h]

theorem functionArguments_point (opaques points : List Program) (variance : Variance) (seed : FiberValue)
    (i : Nat) (h : i < points.length) :
    (functionArguments opaques points variance seed)[opaques.length + i]? = some (smoothValue points[i]) := by
  unfold functionArguments
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
  simp [h]

theorem functionArguments_seed (opaques points : List Program) (variance : Variance) (seed : FiberValue) :
    (functionArguments opaques points variance seed)[opaques.length + points.length]? =
      some (.indexed (.fiber variance seed)) := by
  unfold functionArguments
  rw [List.getElem?_append_right (by simp)]
  simp

theorem functionParameters_length_saved {site : Site} (saved : site.mode = .saved) :
    (functionParameters site).length = site.opaqueSteps.length + (site.steps.length + 1) + 1 := by
  simp [functionParameters, saved] <;> omega

theorem functionParameters_length_recomputed {site : Site} (recomputed : site.mode = .recomputed) :
    (functionParameters site).length = site.opaqueSteps.length + 1 + 1 := by
  simp [functionParameters, recomputed]

/-- The opaque map parameters of a generated function, as `backwardBody`
reads them. -/
def opaqueVariables (site : Site) : List Core.Term :=
  (site.opaqueSteps.zipIdx).map fun (step, symbol) =>
    Core.Term.variable symbol (Reverse.mapResult site step.source step.target)

/-- The saved points after the input point, as the saved `backwardBody` reads
them. -/
def savedVariables (site : Site) : List Core.Term :=
  (site.steps.zipIdx).map fun (step, index) =>
    Core.Term.variable (site.opaqueSteps.length + 1 + index) (Reverse.pointResult site step.target)

/-- The point symbols of a recomputing function or a saved site: `first,
first + 1, …`, one per step. -/
def pointSymbols (first count : Nat) : List Nat := (List.range count).map fun offset => first + offset

/-- The variables of the points after the input point at the given symbols, as
`compileSite` and the recomputing `backwardBody` build them. -/
def pointVariables (site : Site) (symbols : List Nat) : List Core.Term :=
  (site.steps.zip symbols).map fun (step, symbol) => Core.Term.variable symbol (Reverse.pointResult site step.target)

/-- The body of a saved generated function. -/
theorem backwardBody_saved (names : Names) {site : Site} (saved : site.mode = .saved) :
    backwardBody names site =
      backwardChain site (pulls names site (mapTerms site.steps (opaqueVariables site))
          (.variable site.opaqueSteps.length (Reverse.pointResult site site.input) :: savedVariables site))
        (.variable (site.opaqueSteps.length + site.steps.length + 1) (Reverse.fiberResult site site.output))
        (site.opaqueSteps.length + site.steps.length + 2) := by
  unfold backwardBody
  rw [saved]
  rfl

/-- The input point parameter of a generated function. -/
def startVariable (site : Site) : Core.Term := .variable site.opaqueSteps.length (Reverse.pointResult site site.input)

/-- The number of images that a recomputing function binds: every image, or
every image but the last when the last step is opaque. -/
def boundImages (site : Site) : Nat := if site.lastOpaque then site.steps.length - 1 else site.steps.length

/-- The point terms of a recomputing function: the input point and the bound
images, then, after a last opaque step, the input point again at the output
position that step does not read. -/
def recomputedPoints (site : Site) : List Core.Term :=
  let points := startVariable site :: pointVariables site (pointSymbols (site.opaqueSteps.length + 2) (boundImages site))
  if site.lastOpaque then points ++ [startVariable site] else points

/-- The body of a recomputing generated function. -/
theorem backwardBody_recomputed (names : Names) {site : Site} (recomputed : site.mode = .recomputed) :
    backwardBody names site =
      forwardLets names site (site.steps.take (boundImages site))
        ((mapTerms site.steps (opaqueVariables site)).take (boundImages site)) (startVariable site)
        (pointSymbols (site.opaqueSteps.length + 2) (boundImages site))
        (backwardChain site (pulls names site (mapTerms site.steps (opaqueVariables site)) (recomputedPoints site))
          (.variable (site.opaqueSteps.length + 1) (Reverse.fiberResult site site.output))
          (site.opaqueSteps.length + site.steps.length + 2)) := by
  unfold backwardBody
  rw [recomputed]
  rfl

/-- A last opaque step: the steps end in an opaque one. -/
theorem lastOpaque_iff {site : Site} : site.lastOpaque = true ↔ site.steps.getLast?.map Step.kind = some .opaque := by
  unfold Reverse.Site.lastOpaque
  exact beq_iff_eq

theorem opaqueVariables_length (site : Site) : (opaqueVariables site).length = site.opaqueSteps.length := by
  simp [opaqueVariables]

theorem opaqueVariables_getElem (site : Site) (i : Nat) (h : i < (opaqueVariables site).length) :
    ∃ result, (opaqueVariables site)[i] = .variable i result := by
  simp [opaqueVariables]

theorem savedVariables_length (site : Site) : (savedVariables site).length = site.steps.length := by
  simp [savedVariables]

theorem savedVariables_getElem (site : Site) (i : Nat) (h : i < (savedVariables site).length) :
    ∃ result, (savedVariables site)[i] = .variable (site.opaqueSteps.length + 1 + i) result := by
  simp [savedVariables]

theorem pointSymbols_length (first count : Nat) : (pointSymbols first count).length = count := by
  simp [pointSymbols]

theorem pointSymbols_nodup (first count : Nat) : (pointSymbols first count).Nodup := by
  unfold pointSymbols List.Nodup
  exact List.Pairwise.map _ (fun a b (different : a ≠ b) => by omega) List.nodup_range

theorem pointSymbols_getElem (first count i : Nat) (h : i < (pointSymbols first count).length) :
    (pointSymbols first count)[i] = first + i := by
  simp [pointSymbols]

theorem pointSymbols_high {first count : Nat} : ∀ symbol ∈ pointSymbols first count, first ≤ symbol := by
  intro symbol member
  simp only [pointSymbols, List.mem_map, List.mem_range] at member
  obtain ⟨offset, _, rfl⟩ := member
  omega

theorem pointVariables_length (site : Site) (symbols : List Nat) (count : symbols.length = site.steps.length) :
    (pointVariables site symbols).length = site.steps.length := by
  simp [pointVariables, count]

theorem pointVariables_getElem (site : Site) (symbols : List Nat) (i : Nat) (h : i < (pointVariables site symbols).length) :
    ∃ (result : Result) (hs : i < symbols.length), (pointVariables site symbols)[i] = .variable symbols[i] result := by
  simp only [pointVariables, List.length_map, List.length_zip] at h
  exact ⟨Reverse.pointResult site (site.steps[i]'(by omega)).target, by omega, by simp [pointVariables]⟩

/-- The opaque map variables of a generated function read its first
arguments. -/
theorem opaqueVariables_stable {module : Module} {site : Site} {opaques points : List Program} {variance : Variance}
    {seed : FiberValue} {bound : Nat} (count : opaques.length = site.opaqueSteps.length)
    (enough : site.opaqueSteps.length ≤ bound) :
    AllPairs (fun term program => Stable module (fun symbol => (functionArguments opaques points variance seed)[symbol]?)
      bound term (smoothValue program)) (opaqueVariables site) opaques := by
  apply allPairs_of_getElem (by rw [opaqueVariables_length, count])
  intro i hi ho
  obtain ⟨result, equal⟩ := opaqueVariables_getElem site i hi
  rw [equal]
  rw [opaqueVariables_length] at hi
  exact stable_variable module result (by omega) (functionArguments_opaque opaques points variance seed i ho)

/-- Point variables at distinct symbols, read after binding the images to
those symbols, evaluate to the images. -/
theorem pointVariables_stable {module : Module} {site : Site} {values : Values} {bound first : Nat}
    {points : List Program} (count : points.length = site.steps.length) (enough : first + site.steps.length ≤ bound) :
    AllPairs (fun term point => Stable module
        (bindAll values (pointSymbols first site.steps.length) (points.map smoothValue)) bound term (smoothValue point))
      (pointVariables site (pointSymbols first site.steps.length)) points := by
  apply allPairs_of_getElem (by rw [pointVariables_length _ _ (pointSymbols_length _ _), count])
  intro i hi ho
  obtain ⟨result, hs, equal⟩ := pointVariables_getElem site _ i hi
  rw [equal]
  rw [pointVariables_length _ _ (pointSymbols_length _ _)] at hi
  refine stable_variable module result (by rw [pointSymbols_getElem]; omega) ?_
  rw [bindAll_getElem values _ _ (pointSymbols_nodup _ _) (by simp [pointSymbols_length, count]) i hs (by simp; omega)]
  simp

/-- The same for the first `count` images, `count` at most the number of
steps. -/
theorem pointVariables_stable_of_le {module : Module} {site : Site} {values : Values} {bound first count : Nat}
    {points : List Program} (length : points.length = count) (le : count ≤ site.steps.length)
    (enough : first + count ≤ bound) :
    AllPairs (fun term point => Stable module
        (bindAll values (pointSymbols first count) (points.map smoothValue)) bound term (smoothValue point))
      (pointVariables site (pointSymbols first count)) points := by
  have variables : (pointVariables site (pointSymbols first count)).length = count := by
    simp [pointVariables, pointSymbols_length]
    omega
  apply allPairs_of_getElem (by rw [variables, length])
  intro i hi ho
  obtain ⟨result, hs, equal⟩ := pointVariables_getElem site _ i hi
  rw [equal]
  rw [variables] at hi
  refine stable_variable module result (by rw [pointSymbols_getElem]; omega) ?_
  rw [bindAll_getElem values _ _ (pointSymbols_nodup _ _) (by simp [pointSymbols_length, length]) i hs
    (by simp; omega)]
  simp

/-- **The saved backward function, for any points.** Let the module declare
the backward step of every map under its name (`StepsDeclared`), with map
types that name two objects (`StepFormed`), and let the site have a step. For
every activation that `bindArguments` builds from one value per opaque step,
the input point `start`, one saved point per step and a seed, the body of the
saved generated function evaluates to `backwardPass`: the seed pulled back by
the Jacobian table step or the saved reference pass of each map, last map
first, at the given points. No relation between the points is assumed. -/
theorem saved_function_evaluates {module : Module} {names : Names} {site : Site}
    (saved : site.mode = .saved) (declared : StepsDeclared module names site)
    (length : names.steps.length = site.steps.length) (formed : ∀ step ∈ site.steps, StepFormed step)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (start : Program) {outputs : List Program} (outputCount : outputs.length = site.steps.length)
    (variance : Variance) (seed : FiberValue) {activation : Values}
    (bound : bindArguments (functionParameters site) (functionArguments opaques (start :: outputs) variance seed) =
      some activation) :
    Evaluates module activation (backwardBody names site)
      (.indexed (.fiber .cotangent (backwardPass site.steps (stepPrograms site.steps opaques) start outputs seed))) := by
  rw [bindArguments_functionParameters site _
    (by rw [functionParameters_length_saved saved]; simp [functionArguments, count, outputCount] <;> omega)] at bound
  obtain rfl := Option.some.inj bound
  rw [backwardBody_saved names saved]
  refine siteChain_evaluates _ declared length formed nonempty (variance := variance) (seed := seed)
    (opaqueVariables_stable count (by omega)) count
    (stable_variable module _ (by omega) ?_) ?_ outputCount (IndexedEvaluation.variable_value ?_)
  · have found := functionArguments_point opaques (start :: outputs) variance seed 0 (by simp)
    simpa [count] using found
  · apply allPairs_of_getElem (by rw [savedVariables_length, outputCount])
    intro i hi ho
    obtain ⟨result, equal⟩ := savedVariables_getElem site i hi
    rw [equal]
    rw [savedVariables_length] at hi
    refine stable_variable module result (by omega) ?_
    have found := functionArguments_point opaques (start :: outputs) variance seed (i + 1) (by simp; omega)
    rw [count, show site.opaqueSteps.length + (i + 1) = site.opaqueSteps.length + 1 + i by omega] at found
    simpa using found
  · have found := functionArguments_seed opaques (start :: outputs) variance seed
    rw [count, show site.opaqueSteps.length + (start :: outputs).length =
      site.opaqueSteps.length + site.steps.length + 1 by simp [outputCount]; omega] at found
    exact found

/-- **(B) The saved backward function is the pullback, without the chain
rule.** Under the premises of `saved_function_evaluates`, when the step
programs are composable and the saved points satisfy the residual relation,
the body evaluates to the saved-mode pullback of the seed along
`chain (stepPrograms site.steps opaques)` at the input point. The proof uses
`backwardPass_eq_pullback`: table steps, `pullback_stepwise` and evaluated
points, not `cot_compose` or `backward_eq_cot`. -/
theorem saved_function_pullback {module : Module} {names : Names} {site : Site}
    (saved : site.mode = .saved) (declared : StepsDeclared module names site)
    (length : names.steps.length = site.steps.length) (formed : ∀ step ∈ site.steps, StepFormed step)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (composable : Composable (stepPrograms site.steps opaques))
    (start : Program) {outputs : List Program} (residual : ResidualRel (stepPrograms site.steps opaques) start outputs)
    (variance : Variance) (seed : FiberValue) {activation : Values}
    (bound : bindArguments (functionParameters site) (functionArguments opaques (start :: outputs) variance seed) =
      some activation) :
    Evaluates module activation (backwardBody names site)
      (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms site.steps opaques)) start seed))) := by
  have outputCount : outputs.length = site.steps.length := by
    rw [← residual_length residual, stepPrograms_length]
  rw [← backwardPass_eq_pullback site.steps _ start outputs seed (matches_stepPrograms _ _)
    (stepPrograms_ne_nil nonempty opaques) composable residual]
  exact saved_function_evaluates saved declared length formed nonempty count start outputCount variance seed bound

/-- **A seed over another point.** Under the premises of
`saved_function_evaluates` and the residual relation, a seed that does not lie
over the last saved point gives the failure value. Neither composability nor
the chain rule is needed. -/
theorem saved_function_foreign_seed {module : Module} {names : Names} {site : Site}
    (saved : site.mode = .saved) (declared : StepsDeclared module names site)
    (length : names.steps.length = site.steps.length) (formed : ∀ step ∈ site.steps, StepFormed step)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (start : Program) {outputs : List Program} (residual : ResidualRel (stepPrograms site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber) (foreign : seed.point ≠ coordinates (outputs.getLastD start))
    {activation : Values}
    (bound : bindArguments (functionParameters site)
      (functionArguments opaques (start :: outputs) variance (some seed)) = some activation) :
    Evaluates module activation (backwardBody names site) (.indexed (.fiber .cotangent none)) := by
  have outputCount : outputs.length = site.steps.length := by
    rw [← residual_length residual, stepPrograms_length]
  rw [← backwardPass_foreign_seed site.steps _ start outputs seed (matches_stepPrograms _ _)
    (stepPrograms_ne_nil nonempty opaques) residual foreign]
  exact saved_function_evaluates saved declared length formed nonempty count start outputCount variance _ bound

/-- **(D) The saved backward function in coordinates (uses the chain rule).**
Under the premises of `saved_function_evaluates` and the residual relation,
when the chain is well typed from dimension `source` to `target` and the seed
lies over the chain's image of the input point with `target` components, the
body evaluates to the covector at the input point whose components are `cot`
of the composite map. This uses `SmoothCalculus.backward_eq_cot`. -/
theorem saved_function_cot {module : Module} {names : Names} {site : Site}
    (saved : site.mode = .saved) (declared : StepsDeclared module names site)
    (length : names.steps.length = site.steps.length) (formed : ∀ step ∈ site.steps, StepFormed step)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    {source target : Nat} (typed : (chain (stepPrograms site.steps opaques)).wellTyped source target = true)
    (start : Program) {outputs : List Program} (residual : ResidualRel (stepPrograms site.steps opaques) start outputs)
    (variance : Variance) (seed : Fiber)
    (over : seed.point = (chain (stepPrograms site.steps opaques)).eval (coordinates start))
    (components : seed.components.length = target) {activation : Values}
    (bound : bindArguments (functionParameters site)
      (functionArguments opaques (start :: outputs) variance (some seed)) = some activation) :
    Evaluates module activation (backwardBody names site)
      (.indexed (.fiber .cotangent (some ⟨coordinates start, VastitasKernel.SmoothRuntime.cot
        (chain (stepPrograms site.steps opaques)).denote (coordinates start) seed.components⟩))) := by
  rw [← pullback_chain_cot .saved typed start seed over components]
  exact saved_function_pullback saved declared length formed nonempty count (composable_of_wellTyped _ typed) start
    residual variance _ bound

/-! ## Forward Core -/

/-- **(F) The forward Core.** Let the module declare `names.apply` as
`smoothApply`. Let the map terms evaluate to programs, reading no symbol at or
above `bound`, let every symbol be at or above `bound`, and let `previous`
evaluate to the point `start`. Then `forwardLets` evaluates to a value exactly
when its body evaluates to that value in the activation extended, symbol by
symbol, with the evaluated images `r₁ = applyPoint m₁ start, r₂ = applyPoint
m₂ r₁, …` (`images`). The symbols need not be distinct. -/
theorem forwardLets_evaluates {module : Module} {names : Names} {site : Site}
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth)) :
    ∀ (steps : List Step) (maps : List Term) (programs : List Program) (symbols : List Nat) (values : Values)
      (bound : Nat) (previous : Term) (start : Program) (body : Term) (value : Value),
      AllPairs (fun map program => Stable module values bound map (smoothValue program)) maps programs →
      steps.length = maps.length → symbols.length = maps.length → (∀ symbol ∈ symbols, bound ≤ symbol) →
      Evaluates module values previous (smoothValue start) →
      (Evaluates module values (forwardLets names site steps maps previous symbols body) value ↔
        Evaluates module (bindAll values symbols ((images programs start).map smoothValue)) body value) := by
  intro steps
  induction steps with
  | nil =>
    intro maps programs symbols values bound previous start body value pairs stepCount symbolCount _ _
    rcases maps with _ | ⟨map, maps⟩
    · rcases programs with _ | ⟨program, programs⟩
      · rcases symbols with _ | ⟨symbol, symbols⟩
        · exact Iff.rfl
        · simp at symbolCount
      · exact pairs.elim
    · simp at stepCount
  | cons step steps ih =>
    intro maps programs symbols values bound previous start body value pairs stepCount symbolCount high previousEval
    rcases maps with _ | ⟨map, maps⟩
    · simp at stepCount
    rcases programs with _ | ⟨program, programs⟩
    · exact pairs.elim
    rcases symbols with _ | ⟨symbol, symbols⟩
    · simp at symbolCount
    have image := applyTerm_evaluates apply step pairs.1.evaluates previousEval
    have agrees := agrees_bindValue (values := values) (smoothValue (applyPoint program start))
      (high symbol (by simp))
    have rest := ih maps programs symbols (bindValue values symbol (smoothValue (applyPoint program start))) bound
      (.variable symbol (Reverse.pointResult site step.target)) (applyPoint program start) body value
      (pairs.2.imp fun _ _ stable => stable.extend agrees (Nat.le_refl _)) (by simpa using stepCount)
      (by simpa using symbolCount) (fun other member => high other (by simp [member]))
      (IndexedEvaluation.variable_value (by simp [bindValue]))
    simp only [forwardLets]
    rw [letE_iff image]
    exact rest

/-- **(F) The primal value and the residuals.** Under the premises of
`forwardLets_evaluates`, the forward Core binds the evaluated images, these
satisfy the residual relation, and the last of them has the coordinates of
the primal value: the chain of the programs at the input point. No chain rule
is used. -/
theorem forwardLets_primal {module : Module} {names : Names} {site : Site}
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth))
    (steps : List Step) (maps : List Term) (programs : List Program) (symbols : List Nat) (values : Values)
    (bound : Nat) (previous : Term) (start : Program) (body : Term) (value : Value)
    (pairs : AllPairs (fun map program => Stable module values bound map (smoothValue program)) maps programs)
    (stepCount : steps.length = maps.length) (symbolCount : symbols.length = maps.length)
    (high : ∀ symbol ∈ symbols, bound ≤ symbol) (previousEval : Evaluates module values previous (smoothValue start))
    (nonempty : programs ≠ []) :
    (Evaluates module values (forwardLets names site steps maps previous symbols body) value ↔
      Evaluates module (bindAll values symbols ((images programs start).map smoothValue)) body value) ∧
    ResidualRel programs start (images programs start) ∧
    coordinates ((images programs start).getLastD start) = (chain programs).eval (coordinates start) :=
  ⟨forwardLets_evaluates apply steps maps programs symbols values bound previous start body value pairs stepCount
    symbolCount high previousEval, residualRel_images programs start,
    residual_last programs start _ nonempty (residualRel_images programs start)⟩

/-! ## The recomputing backward function -/

/-- **The recomputing backward function, for any input point.** Let the
module declare `names.apply` as `smoothApply`, the backward step of every map
(`StepsDeclared`, `StepFormed`), and every declared map through its rule
(`MorphismsDeclared`), and let the site have a step. For every activation
that `bindArguments` builds from one value per opaque step, the input point
and a seed, the body of the recomputing generated function evaluates to
`backwardPass` at the evaluated images of the input point. -/
theorem recomputed_function_evaluates {module : Module} {names : Names} {site : Site}
    (recomputed : site.mode = .recomputed)
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth))
    (declared : StepsDeclared module names site) (length : names.steps.length = site.steps.length)
    (formed : ∀ step ∈ site.steps, StepFormed step) (morphisms : MorphismsDeclared module site.steps)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (start : Program) (variance : Variance) (seed : FiberValue) {activation : Values}
    (bound : bindArguments (functionParameters site) (functionArguments opaques [start] variance seed) =
      some activation) :
    Evaluates module activation (backwardBody names site)
      (.indexed (.fiber .cotangent (backwardPass site.steps (stepPrograms site.steps opaques) start
        (images (stepPrograms site.steps opaques) start) seed))) := by
  rw [bindArguments_functionParameters site _
    (by rw [functionParameters_length_recomputed recomputed]; simp [functionArguments, count])] at bound
  obtain rfl := Option.some.inj bound
  rw [backwardBody_recomputed names recomputed]
  have opaqueEval := opaqueVariables_stable (module := module) (site := site) (points := [start])
    (variance := variance) (seed := seed) (bound := site.opaqueSteps.length + 2) count (by omega)
  have startStable : Stable module (fun symbol => (functionArguments opaques [start] variance seed)[symbol]?)
      (site.opaqueSteps.length + 2) (startVariable site) (smoothValue start) := by
    refine stable_variable module _ (by omega) ?_
    have found := functionArguments_point opaques [start] variance seed 0 (by simp)
    simpa [count] using found
  have seedStable : Stable module (fun symbol => (functionArguments opaques [start] variance seed)[symbol]?)
      (site.opaqueSteps.length + 2) (.variable (site.opaqueSteps.length + 1) (Reverse.fiberResult site site.output))
      (.indexed (.fiber variance seed)) := by
    refine stable_variable module _ (by omega) ?_
    have found := functionArguments_seed opaques [start] variance seed
    simpa [count] using found
  have maps := allPairs_mapTerms site.steps morphisms _ opaques opaqueEval count
  have imagesCount : (images (stepPrograms site.steps opaques) start).length = site.steps.length := by
    rw [images_length, stepPrograms_length]
  -- The forward Core binds the first `boundImages site` images.
  have boundLe : boundImages site ≤ site.steps.length := by
    unfold boundImages
    split <;> omega
  have boundCount : ((images (stepPrograms site.steps opaques) start).take (boundImages site)).length =
      boundImages site := by
    rw [List.length_take, imagesCount]
    omega
  have agrees := bindAll_agrees (bound := site.opaqueSteps.length + 2)
    (fun symbol => (functionArguments opaques [start] variance seed)[symbol]?)
    (pointSymbols (site.opaqueSteps.length + 2) (boundImages site))
    (((images (stepPrograms site.steps opaques) start).take (boundImages site)).map smoothValue)
    (fun _ member => pointSymbols_high _ member)
  have enough : site.opaqueSteps.length + 2 ≤ site.opaqueSteps.length + site.steps.length + 2 := by omega
  have pointsStable := pointVariables_stable_of_le (module := module) (site := site)
    (bound := site.opaqueSteps.length + site.steps.length + 2) (first := site.opaqueSteps.length + 2)
    (values := fun symbol => (functionArguments opaques [start] variance seed)[symbol]?) boundCount boundLe
    (by omega)
  refine (forwardLets_evaluates apply (site.steps.take (boundImages site))
    ((mapTerms site.steps (opaqueVariables site)).take (boundImages site))
    ((stepPrograms site.steps opaques).take (boundImages site))
    (pointSymbols (site.opaqueSteps.length + 2) (boundImages site)) _ (site.opaqueSteps.length + 2) _ start _ _
    (maps.take (boundImages site)) (by simp [mapTerms_length])
    (by simp only [pointSymbols_length, List.length_take, mapTerms_length]; omega)
    (fun _ member => pointSymbols_high _ member) startStable.evaluates).mpr ?_
  rw [images_take]
  cases last : site.lastOpaque
  · -- Every image is bound.
    have boundIs : boundImages site = site.steps.length := by simp [boundImages, last]
    have pointsIs : recomputedPoints site =
        startVariable site :: pointVariables site (pointSymbols (site.opaqueSteps.length + 2) (boundImages site)) := by
      simp [recomputedPoints, last]
    rw [pointsIs]
    have chainEval := siteChain_evaluates (names := names) (site.opaqueSteps.length + site.steps.length + 2)
      declared length formed nonempty
      (opaqueEval.imp fun _ _ stable => stable.extend agrees enough) count
      (startStable.extend agrees enough) pointsStable (by rw [boundCount, boundIs])
      (seedStable.extend agrees enough).evaluates
    have full : (images (stepPrograms site.steps opaques) start).take (boundImages site) =
        images (stepPrograms site.steps opaques) start :=
      List.take_of_length_le (Nat.le_of_eq (by rw [imagesCount, boundIs]))
    rw [full] at chainEval ⊢
    exact chainEval
  · -- The image of the last, opaque step is not bound; the input point stands at its output.
    have lastKind := lastOpaque_iff.mp last
    have positive : 0 < site.steps.length := List.length_pos_iff.mpr nonempty
    have boundIs : boundImages site = site.steps.length - 1 := by simp [boundImages, last]
    have pointsIs : recomputedPoints site =
        startVariable site :: (pointVariables site (pointSymbols (site.opaqueSteps.length + 2) (boundImages site)) ++
          [startVariable site]) := by
      simp [recomputedPoints, last]
    rw [pointsIs]
    have chainEval := siteChain_evaluates (names := names) (site.opaqueSteps.length + site.steps.length + 2)
      declared length formed nonempty
      (opaqueEval.imp fun _ _ stable => stable.extend agrees enough) count
      (startStable.extend agrees enough)
      (AllPairs.append (as' := [startVariable site]) (bs' := [start]) pointsStable
        ⟨startStable.extend agrees enough, trivial⟩)
      (by rw [List.length_append, boundCount, boundIs, List.length_singleton]; omega)
      (seedStable.extend agrees enough).evaluates
    rwa [backwardPass_last_opaque site.steps (stepPrograms site.steps opaques) start
      ((images (stepPrograms site.steps opaques) start).take (boundImages site) ++ [start])
      (images (stepPrograms site.steps opaques) start) seed lastKind
      (by rw [List.length_append, boundCount, boundIs, List.length_singleton]; omega) imagesCount
      (by rw [List.dropLast_concat, List.dropLast_eq_take, imagesCount, boundIs])] at chainEval

/-- **(R) The recomputing backward function is the recomputing pullback.**
Under the premises of `recomputed_function_evaluates`, when the step programs
are composable, the body evaluates to the recomputing pullback of the seed
along `chain (stepPrograms site.steps opaques)` at the input point. The proof
uses `backwardPass_eq_pullback` and `pullback_saved_eq_recomputed`, not the
chain rule. -/
theorem recomputed_function_pullback {module : Module} {names : Names} {site : Site}
    (recomputed : site.mode = .recomputed)
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth))
    (declared : StepsDeclared module names site) (length : names.steps.length = site.steps.length)
    (formed : ∀ step ∈ site.steps, StepFormed step) (morphisms : MorphismsDeclared module site.steps)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (composable : Composable (stepPrograms site.steps opaques))
    (start : Program) (variance : Variance) (seed : FiberValue) {activation : Values}
    (bound : bindArguments (functionParameters site) (functionArguments opaques [start] variance seed) =
      some activation) :
    Evaluates module activation (backwardBody names site)
      (.indexed (.fiber .cotangent (pullback .recomputed (chain (stepPrograms site.steps opaques)) start seed))) := by
  rw [← VastitasOracle.SmoothRuntime.pullback_saved_eq_recomputed,
    ← backwardPass_eq_pullback site.steps _ start _ seed (matches_stepPrograms _ _)
      (stepPrograms_ne_nil nonempty opaques) composable (residualRel_images _ _)]
  exact recomputed_function_evaluates recomputed apply declared length formed morphisms nonempty count start variance
    seed bound

/-- **Saved and recomputing generated functions agree.** For a saved site and
the same site with the recomputing policy, under the premises of
`saved_function_pullback` and `recomputed_function_pullback`, the two
generated bodies evaluate to the same value: the saved function on the input
point and saved points that satisfy the residual relation, the recomputing
function on the input point alone. The proof uses
`pullback_saved_eq_recomputed`, not the chain rule. -/
theorem saved_eq_recomputed {module : Module} {names : Names} {site : Site}
    (saved : site.mode = .saved)
    (apply : module.declarations.primitive? names.apply = some (.smoothApply site.smooth))
    (declared : StepsDeclared module names site) (length : names.steps.length = site.steps.length)
    (formed : ∀ step ∈ site.steps, StepFormed step) (morphisms : MorphismsDeclared module site.steps)
    (nonempty : site.steps ≠ []) {opaques : List Program} (count : opaques.length = site.opaqueSteps.length)
    (composable : Composable (stepPrograms site.steps opaques))
    (start : Program) {outputs : List Program} (residual : ResidualRel (stepPrograms site.steps opaques) start outputs)
    (variance : Variance) (seed : FiberValue) {savedActivation recomputedActivation : Values}
    (savedBound : bindArguments (functionParameters site)
      (functionArguments opaques (start :: outputs) variance seed) = some savedActivation)
    (recomputedBound : bindArguments (functionParameters { site with mode := .recomputed })
      (functionArguments opaques [start] variance seed) = some recomputedActivation)
    {savedValue recomputedValue : Value}
    (savedEval : Evaluates module savedActivation (backwardBody names site) savedValue)
    (recomputedEval : Evaluates module recomputedActivation (backwardBody names { site with mode := .recomputed })
      recomputedValue) :
    savedValue = recomputedValue := by
  have savedPull := saved_function_pullback saved declared length formed nonempty count composable start residual
    variance seed savedBound
  have recomputedPull := recomputed_function_pullback (site := { site with mode := .recomputed }) rfl apply declared
    length formed morphisms nonempty count composable start variance seed recomputedBound
  rw [IndexedEvaluation.evaluates_unique savedEval savedPull,
    IndexedEvaluation.evaluates_unique recomputedEval recomputedPull,
    VastitasOracle.SmoothRuntime.pullback_saved_eq_recomputed]

/-! ## Composition trees -/

/-- `program` is a tree of `compose` nodes whose leaves, in application
order, are `leaves`, and the dimensions agree at every node. The theorems of
this module take it as a premise. `SmoothReverseCompiled.resolve_factors`
proves that the value of a map operand that `Reverse.resolve` reads has this
shape, when the value is well typed and the `let` definitions that `resolve`
reads through agree with the activation. -/
inductive Factors : Program → List Program → Prop
  | leaf (program : Program) : Factors program [program]
  | node {after before : Program} {afterLeaves beforeLeaves : List Program} :
      Factors after afterLeaves → Factors before beforeLeaves → after.inputArity = before.outputArity →
      Factors (.compose after before) (beforeLeaves ++ afterLeaves)

/-- The evaluated point that maps reach from `point`, one map at a time. -/
def reach : List Program → Program → Program
  | [], point => point
  | map :: maps, point => reach maps (applyPoint map point)

/-- The pullback along maps one at a time, at their evaluated points: the last
map first. -/
def pullAlong (mode : PullbackMode) : List Program → Program → FiberValue → FiberValue
  | [], _, seed => seed
  | map :: maps, point, seed => pullback mode map point (pullAlong mode maps (applyPoint map point) seed)

section Trees

open VastitasOracle.SmoothJacobian

theorem reach_append : ∀ (first second : List Program) (point : Program),
    reach (first ++ second) point = reach second (reach first point)
  | [], _, _ => rfl
  | map :: maps, second, point => reach_append maps second (applyPoint map point)

theorem pullAlong_append (mode : PullbackMode) : ∀ (first second : List Program) (point : Program)
    (seed : FiberValue),
    pullAlong mode (first ++ second) point seed =
      pullAlong mode first point (pullAlong mode second (reach first point) seed)
  | [], _, _, _ => rfl
  | map :: maps, second, point, seed => by
    simp only [List.cons_append, pullAlong, reach]
    rw [pullAlong_append mode maps second]

theorem pullAlong_congr (mode : PullbackMode) : ∀ (maps : List Program) {point point' : Program},
    coordinates point = coordinates point' → ∀ seed, pullAlong mode maps point seed = pullAlong mode maps point' seed
  | [], _, _, _, _ => rfl
  | map :: maps, point, point', same, seed => by
    simp only [pullAlong]
    rw [pullAlong_congr mode maps (point := applyPoint map point) (point' := applyPoint map point')
      (by rw [coordinates_applyPoint, coordinates_applyPoint, same]) seed, pullback_congr_point mode map same]

theorem Factors.ne_nil {program : Program} {leaves : List Program} (factors : Factors program leaves) :
    leaves ≠ [] := by
  induction factors with
  | leaf => simp
  | node _ _ _ _ beforeIh =>
    intro empty
    exact beforeIh (List.append_eq_nil_iff.mp empty).1

/-- The leaves of a tree reach the point that the tree evaluates to. -/
theorem Factors.coordinates_reach {program : Program} {leaves : List Program} (factors : Factors program leaves) :
    ∀ point, coordinates (reach leaves point) = program.eval (coordinates point) := by
  induction factors with
  | leaf program => intro point; exact coordinates_applyPoint program point
  | node _ _ _ afterIh beforeIh =>
    intro point
    rw [reach_append, afterIh, beforeIh]
    rfl

/-- Pulling back along a composition tree is pulling back along its leaves,
one at a time, in either mode, for every seed. The proof uses
`pullback_stepwise_applyPoint`, not the chain rule. -/
theorem Factors.pullback_eq (mode : PullbackMode) {program : Program} {leaves : List Program}
    (factors : Factors program leaves) :
    ∀ point seed, pullback mode program point seed = pullAlong mode leaves point seed := by
  induction factors with
  | leaf program => intro point seed; rfl
  | @node after before afterLeaves beforeLeaves _ beforeFactors arity afterIh beforeIh =>
    intro point seed
    rw [pullback_stepwise_applyPoint mode after before point seed arity, pullAlong_append, beforeIh, afterIh]
    congr 1
    exact pullAlong_congr mode afterLeaves (by rw [coordinates_applyPoint, beforeFactors.coordinates_reach]) seed

/-- Composable maps are the leaves of their chain. -/
theorem factors_chain : ∀ (programs : List Program), programs ≠ [] → Composable programs →
    Factors (chain programs) programs
  | [], nonempty, _ => absurd rfl nonempty
  | [program], _, _ => .leaf program
  | first :: second :: rest, _, composable =>
    Factors.node (beforeLeaves := [first]) (factors_chain (second :: rest) (by simp) composable.2) (.leaf first)
      (by rw [chain_inputArity]; exact composable.1)

/-- **Any tree is its chain.** The pullback along a composition tree is the
pullback along the chain of its leaves, in either mode, for every point and
seed, when the leaves compose. No chain rule is used. -/
theorem Factors.pullback_chain (mode : PullbackMode) {program : Program} {leaves : List Program}
    (factors : Factors program leaves) (composable : Composable leaves) (point : Program) (seed : FiberValue) :
    pullback mode program point seed = pullback mode (chain leaves) point seed := by
  rw [factors.pullback_eq, (factors_chain leaves factors.ne_nil composable).pullback_eq]

theorem composable_append : ∀ (first second : List Program), Composable first → Composable second →
    (∀ last head, first.getLast? = some last → second.head? = some head → head.inputArity = last.outputArity) →
    Composable (first ++ second)
  | [], _, _, composable, _ => composable
  | [_], [], _, _, _ => trivial
  | [last], head :: _, _, composable, junction => ⟨junction last head rfl rfl, composable⟩
  | _ :: next :: rest, second, composable, composableSecond, junction =>
    ⟨composable.1, composable_append (next :: rest) second composable.2 composableSecond
      fun last head isLast isHead => junction last head (by simpa using isLast) isHead⟩

theorem Factors.head_inputArity {program : Program} {leaves : List Program} (factors : Factors program leaves) :
    ∀ head, leaves.head? = some head → head.inputArity = program.inputArity := by
  induction factors with
  | leaf program =>
    intro head found
    cases found
    rfl
  | @node after before afterLeaves beforeLeaves _ beforeFactors _ _ beforeIh =>
    intro head found
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil beforeFactors.ne_nil
    rw [List.cons_append, List.head?_cons] at found
    rw [← Option.some.inj found]
    exact beforeIh first rfl

theorem Factors.last_outputArity {program : Program} {leaves : List Program} (factors : Factors program leaves) :
    ∀ last, leaves.getLast? = some last → last.outputArity = program.outputArity := by
  induction factors with
  | leaf program =>
    intro last found
    cases found
    rfl
  | @node after before afterLeaves beforeLeaves afterFactors _ _ afterIh _ =>
    intro last found
    rw [List.getLast?_append] at found
    cases isLast : afterLeaves.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp isLast) afterFactors.ne_nil
    | some other =>
      rw [isLast] at found
      simp only [Option.some_or, Option.some.injEq] at found
      rw [← found]
      exact afterIh other isLast

/-- **The leaves of a tree compose.** The dimension condition at every node
makes adjacent leaves agree in dimension. -/
theorem Factors.composable {program : Program} {leaves : List Program} (factors : Factors program leaves) :
    Composable leaves := by
  induction factors with
  | leaf => trivial
  | @node after before afterLeaves beforeLeaves afterFactors beforeFactors arity afterIh beforeIh =>
    refine composable_append beforeLeaves afterLeaves beforeIh afterIh fun last head isLast isHead => ?_
    rw [afterFactors.head_inputArity head isHead, beforeFactors.last_outputArity last isLast]
    exact arity

end Trees

/-! ## The site -/

/-- The point terms of a saved site, as `compileSite` builds them: the input
point term and one variable per step. -/
def sitePoints (site : Site) (startTerm : Core.Term) (symbols : List Nat) : List Core.Term :=
  startTerm :: pointVariables site symbols

theorem entry_names_steps_length (entry : Reverse.Entry) : entry.names.steps.length = entry.site.steps.length := by
  simp [Reverse.Entry.names]

theorem Agrees.mono {values values' : Values} {bound bound' : Nat} (agrees : Agrees values values' bound')
    (le : bound ≤ bound') : Agrees values values' bound := fun symbol low => agrees symbol (by omega)

theorem Agrees.trans {values values' values'' : Values} {bound : Nat} (first : Agrees values values' bound)
    (second : Agrees values' values'' bound) : Agrees values values'' bound := fun symbol low => by
  rw [second symbol low, first symbol low]

theorem AllPairs.map_right {α β γ : Type} {relation : α → γ → Prop} {f : β → γ} :
    ∀ {as : List α} {bs : List β}, AllPairs (fun a b => relation a (f b)) as bs → AllPairs relation as (bs.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, pairs => ⟨pairs.1, AllPairs.map_right pairs.2⟩
  | [], _ :: _, pairs => pairs.elim
  | _ :: _, [], pairs => pairs.elim

theorem arguments_of_allPairs {module : Module} {values : Values} :
    ∀ {terms : List Core.Term} {results : List Value},
      AllPairs (fun term value => Evaluates module values term value) terms results →
      ArgumentsEvaluate module values terms results
  | [], [], _ => IndexedEvaluation.arguments_nil module values
  | _ :: _, _ :: _, pairs => IndexedEvaluation.arguments_cons pairs.1 (arguments_of_allPairs pairs.2)
  | [], _ :: _, pairs => pairs.elim
  | _ :: _, [], pairs => pairs.elim

theorem arguments_append {module : Module} {values : Values} {terms terms' : List Core.Term}
    {results results' : List Value} (first : ArgumentsEvaluate module values terms results)
    (second : ArgumentsEvaluate module values terms' results') :
    ArgumentsEvaluate module values (terms ++ terms') (results ++ results') := by
  obtain ⟨a, ha⟩ := first
  obtain ⟨b, hb⟩ := second
  refine ⟨max a b, fun fuel enough => ?_⟩
  rw [List.mapM_append, ha fuel (by omega), hb fuel (by omega)]
  rfl

/-- The call of the generated function: on arguments that evaluate to one
value per opaque step, the points and a seed, it evaluates as the body. -/
theorem call_evaluates {module : Module} {entry : Reverse.Entry} {values : Values}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    {arguments : List Core.Term} {opaques points : List Program} {variance : Variance} {seed : FiberValue}
    (argumentsEval : ArgumentsEvaluate module values arguments (functionArguments opaques points variance seed))
    (length : (functionParameters entry.site).length = (functionArguments opaques points variance seed).length)
    (substitution : List (VastitasKernel.Indexed.ObjectRef × VastitasKernel.Indexed.ObjectRef)) (result : Result) {value : Value}
    (bodyEval : ∀ activation, bindArguments (functionParameters entry.site)
      (functionArguments opaques points variance seed) = some activation →
      Evaluates module activation (backwardBody entry.names entry.site) value) :
    Evaluates module values (.call entry.function arguments substitution result) value :=
  IndexedEvaluation.call function argumentsEval (bindArguments_functionParameters entry.site _ length)
    (bodyEval _ (bindArguments_functionParameters entry.site _ length))

/-- The source site `pullback(M, x, η)` evaluates to the pullback of the
values of its operands. -/
theorem source_pullback_evaluates {module : Module} {values : Values} {id smooth cotangent : DeclId}
    {mode : PullbackMode} (found : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    {mapTerm pointTerm seedTerm : Core.Term} {map point : Program} {variance : Variance} {seed : FiberValue}
    (mapEval : Evaluates module values mapTerm (smoothValue map))
    (pointEval : Evaluates module values pointTerm (smoothValue point))
    (seedEval : Evaluates module values seedTerm (.indexed (.fiber variance seed))) (result : Result) :
    Evaluates module values (.primitive id [mapTerm, pointTerm, seedTerm] result)
      (.indexed (.fiber .cotangent (pullback mode map point seed))) :=
  IndexedEvaluation.primitive found (IndexedEvaluation.arguments_cons mapEval (IndexedEvaluation.arguments_cons
    pointEval (IndexedEvaluation.arguments_cons seedEval (IndexedEvaluation.arguments_nil _ _)))) rfl

/-! ## Source calls by their derivative rules -/

/-- A declaration whose derivative rule is not `none` is declared with a
binding of that rule. -/
theorem ruleOf_found {env : Declarations} {id : DeclId} {rule : ReverseRule} (found : Reverse.ruleOf env id = rule)
    (proper : rule ≠ .none) : ∃ binding, env.primitive? id = some binding ∧ binding.contract.reverse = rule := by
  unfold Reverse.ruleOf at found
  split at found
  · rename_i binding declared
    exact ⟨binding, declared, found⟩
  · exact absurd found.symm proper

/-- A call whose rule is a pullback pass evaluates to the pullback of the
values of its operands (`ReverseSound`). -/
theorem pass_pullback_evaluates {module : Module} {values : Values} {id : DeclId} {mode : PullbackMode}
    (rule : Reverse.ruleOf module.declarations id = .pass (.pullback mode)) {mapTerm pointTerm seedTerm : Core.Term}
    {map x : Program} {variance : Variance} {seed : FiberValue}
    (mapEval : Evaluates module values mapTerm (smoothValue map))
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Evaluates module values seedTerm (.indexed (.fiber variance seed))) (result : Result) :
    Evaluates module values (.primitive id [mapTerm, pointTerm, seedTerm] result)
      (.indexed (.fiber .cotangent (pullback mode map x seed))) := by
  obtain ⟨binding, found, reverse⟩ := ruleOf_found rule (by intro same; cases same)
  have sound := SmoothJacobian.registry_reverse_sound binding
  unfold SmoothJacobian.ReverseSound at sound
  rw [reverse] at sound
  exact IndexedEvaluation.primitive found (IndexedEvaluation.arguments_cons mapEval
    (IndexedEvaluation.arguments_cons pointEval (IndexedEvaluation.arguments_cons seedEval
      (IndexedEvaluation.arguments_nil _ _)))) ((sound _ _ _).mpr ⟨map, x, variance, seed, rfl, rfl⟩)

/-- A call whose rule is the differential pass evaluates to the differential. -/
theorem pass_differential_evaluates {module : Module} {values : Values} {id : DeclId}
    (rule : Reverse.ruleOf module.declarations id = .pass .differential) {functionTerm pointTerm : Core.Term}
    {map x : Program} (mapEval : Evaluates module values functionTerm (smoothValue map))
    (pointEval : Evaluates module values pointTerm (smoothValue x)) (result : Result) :
    Evaluates module values (.primitive id [functionTerm, pointTerm] result)
      (.indexed (.fiber .cotangent (VastitasKernel.SmoothRuntime.differential map x))) := by
  obtain ⟨binding, found, reverse⟩ := ruleOf_found rule (by intro same; cases same)
  have sound := SmoothJacobian.registry_reverse_sound binding
  unfold SmoothJacobian.ReverseSound at sound
  rw [reverse] at sound
  exact IndexedEvaluation.primitive found (IndexedEvaluation.arguments_cons mapEval
    (IndexedEvaluation.arguments_cons pointEval (IndexedEvaluation.arguments_nil _ _)))
    ((sound _ _ _).mpr ⟨map, x, rfl, rfl⟩)

/-- A call whose rule is `tape` evaluates to the tape of its map and point. -/
theorem tape_evaluates {module : Module} {values : Values} {id : DeclId}
    (rule : Reverse.ruleOf module.declarations id = .tape) {mapTerm pointTerm : Core.Term} {map x : Program}
    (mapEval : Evaluates module values mapTerm (smoothValue map))
    (pointEval : Evaluates module values pointTerm (smoothValue x)) (result : Result) :
    Evaluates module values (.primitive id [mapTerm, pointTerm] result)
      (.indexed (.tape (VastitasKernel.SmoothRuntime.linearize map x))) := by
  obtain ⟨binding, found, reverse⟩ := ruleOf_found rule (by intro same; cases same)
  have sound := SmoothJacobian.registry_reverse_sound binding
  unfold SmoothJacobian.ReverseSound at sound
  rw [reverse] at sound
  exact IndexedEvaluation.primitive found (IndexedEvaluation.arguments_cons mapEval
    (IndexedEvaluation.arguments_cons pointEval (IndexedEvaluation.arguments_nil _ _)))
    ((sound _ _ _).mpr ⟨map, x, rfl, rfl⟩)

/-- A call whose rule is the `backward` pass evaluates to the reverse pass
over the tape. -/
theorem pass_backward_evaluates {module : Module} {values : Values} {id : DeclId}
    (rule : Reverse.ruleOf module.declarations id = .pass .backward) {tapeTerm seedTerm : Core.Term}
    {tape : VastitasKernel.SmoothRuntime.Tape} {variance : Variance} {seed : FiberValue}
    (tapeEval : Evaluates module values tapeTerm (.indexed (.tape tape)))
    (seedEval : Evaluates module values seedTerm (.indexed (.fiber variance seed))) (result : Result) :
    Evaluates module values (.primitive id [tapeTerm, seedTerm] result)
      (.indexed (.fiber .cotangent (VastitasKernel.SmoothRuntime.backward tape seed))) := by
  obtain ⟨binding, found, reverse⟩ := ruleOf_found rule (by intro same; cases same)
  have sound := SmoothJacobian.registry_reverse_sound binding
  unfold SmoothJacobian.ReverseSound at sound
  rw [reverse] at sound
  exact IndexedEvaluation.primitive found (IndexedEvaluation.arguments_cons tapeEval
    (IndexedEvaluation.arguments_cons seedEval (IndexedEvaluation.arguments_nil _ _)))
    ((sound _ _ _).mpr ⟨tape, variance, seed, rfl, rfl⟩)

/-- **The compiled Core of a saved site.** The Core that `compileSite` builds
for a saved site with a seed operand, after the `let`s of the compound opaque
leaves: `let start := point; let seed := seed; forwardLets …
(call f (opaques ++ points ++ [seed]))`. Let the module hold the generated
function of `entry` and its declarations (`apply`, `StepsDeclared`,
`StepFormed`, `MorphismsDeclared`), and let the site have a step. Let the
opaque terms evaluate to programs that compose, the point to `x` and the seed
term to `η`, all reading no symbol at or above `bound`, and let the symbols of
the site be fresh: `bound ≤ start < seed < firstPoint`. Then the Core
evaluates to the saved-mode pullback of `η` along the chain of the step
programs at `x`. No chain rule is used. -/
theorem site_saved_core {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (saved : entry.site.mode = .saved)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ [])
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques))
    {startSymbol seedSymbol firstPoint : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    (firstHigh : seedSymbol < firstPoint)
    {pointTerm seedTerm : Core.Term} {x : Program} {variance : Variance} {seed : FiberValue}
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Stable module values bound seedTerm (.indexed (.fiber variance seed))) (result : Result) :
    Evaluates module values
        (.letE startSymbol pointTerm (.letE seedSymbol seedTerm
          (forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
            (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length)
            (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable startSymbol pointTerm.result)
              (pointSymbols firstPoint entry.site.steps.length) ++ [.variable seedSymbol seedTerm.result]) [] result))))
      (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms entry.site.steps opaques)) x seed))) := by
  have agrees₁ := agrees_bindValue (values := values) (smoothValue x) startHigh
  have agrees₂ := agrees_bindValue (values := bindValue values startSymbol (smoothValue x))
    (.indexed (.fiber variance seed)) (Nat.le_of_lt (Nat.lt_of_le_of_lt startHigh seedHigh))
  have agrees₁₂ := agrees₁.trans agrees₂
  refine IndexedEvaluation.letE pointEval (IndexedEvaluation.letE (seedEval _ agrees₁) ?_)
  have startFound : bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol
      (.indexed (.fiber variance seed)) startSymbol = some (smoothValue x) := by
    simp [bindValue, Nat.ne_of_lt seedHigh]
  have seedFound : bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol
      (.indexed (.fiber variance seed)) seedSymbol = some (.indexed (.fiber variance seed)) := by
    simp [bindValue]
  have high : ∀ symbol ∈ pointSymbols firstPoint entry.site.steps.length, firstPoint ≤ symbol :=
    fun _ member => pointSymbols_high _ member
  have maps := allPairs_mapTerms (bound := firstPoint) entry.site.steps morphisms opaqueTerms opaques
    (opaqueEval.imp fun _ _ stable => stable.extend agrees₁₂ (by omega)) count
  refine (forwardLets_evaluates apply entry.site.steps _ (stepPrograms entry.site.steps opaques)
    (pointSymbols firstPoint entry.site.steps.length) _ firstPoint _ x _ _ maps (by rw [mapTerms_length])
    (by rw [pointSymbols_length, mapTerms_length]) high (IndexedEvaluation.variable_value startFound)).mpr ?_
  have imagesCount : (images (stepPrograms entry.site.steps opaques) x).length = entry.site.steps.length := by
    rw [images_length, stepPrograms_length]
  have agrees₃ := bindAll_agrees (bound := firstPoint)
    (bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol (.indexed (.fiber variance seed)))
    (pointSymbols firstPoint entry.site.steps.length)
    ((images (stepPrograms entry.site.steps opaques) x).map smoothValue) high
  have notPoint : ∀ symbol, symbol < firstPoint → symbol ∉ pointSymbols firstPoint entry.site.steps.length :=
    fun symbol low member => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le low (high symbol member))
  have opaqueArgs := (opaqueEval.imp fun _ _ stable =>
    (stable.extend (agrees₁₂.trans (agrees₃.mono (by omega))) (Nat.le_refl _)).evaluates).map_right
    (f := smoothValue)
  have pointsArgs : AllPairs (fun term value => Evaluates module
      (bindAll (bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol (.indexed (.fiber variance seed)))
        (pointSymbols firstPoint entry.site.steps.length) ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
      term value)
      (sitePoints entry.site (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length))
      ((x :: images (stepPrograms entry.site.steps opaques) x).map smoothValue) := by
    refine AllPairs.map_right ⟨IndexedEvaluation.variable_value ?_, ?_⟩
    · rw [bindAll_not_mem _ _ _ _ (notPoint _ (by omega))]
      exact startFound
    · exact (pointVariables_stable (first := firstPoint) imagesCount (Nat.le_refl _)).imp
        fun _ _ stable => stable.evaluates
  have seedArg : Evaluates module
      (bindAll (bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol (.indexed (.fiber variance seed)))
        (pointSymbols firstPoint entry.site.steps.length) ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
      (.variable seedSymbol seedTerm.result) (.indexed (.fiber variance seed)) :=
    IndexedEvaluation.variable_value (by rw [bindAll_not_mem _ _ _ _ (notPoint _ firstHigh)]; exact seedFound)
  refine call_evaluates function (opaques := opaques) (points := x :: images (stepPrograms entry.site.steps opaques) x)
    (arguments_append (arguments_append (arguments_of_allPairs opaqueArgs) (arguments_of_allPairs pointsArgs))
      (IndexedEvaluation.arguments_cons seedArg (IndexedEvaluation.arguments_nil _ _)))
    (by rw [functionParameters_length_saved saved]; simp [functionArguments, count, imagesCount] <;> omega) [] result
    fun activation bound => ?_
  exact saved_function_pullback saved declared (entry_names_steps_length entry) formed nonempty count composable x
    (residualRel_images _ _) variance seed bound

/-- **The compiled Core of a recomputing site.** The Core that `compileSite`
builds for a recomputing site, after the `let`s of the compound opaque leaves:
`let start := point; let seed := seed; call f (opaques ++ [start, seed])`.
Under the premises of `site_saved_core` with the recomputing policy, it
evaluates to the recomputing pullback of the seed along the chain of the step
programs at `x`. No chain rule is used. -/
theorem site_recomputed_core {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (recomputed : entry.site.mode = .recomputed)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ [])
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques))
    {startSymbol seedSymbol : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    {pointTerm seedTerm : Core.Term} {x : Program} {variance : Variance} {seed : FiberValue}
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Stable module values bound seedTerm (.indexed (.fiber variance seed))) (result : Result) :
    Evaluates module values
        (.letE startSymbol pointTerm (.letE seedSymbol seedTerm
          (.call entry.function (opaqueTerms ++ [.variable startSymbol pointTerm.result,
            .variable seedSymbol seedTerm.result]) [] result)))
      (.indexed (.fiber .cotangent
        (pullback .recomputed (chain (stepPrograms entry.site.steps opaques)) x seed))) := by
  have agrees₁ := agrees_bindValue (values := values) (smoothValue x) startHigh
  have agrees₂ := agrees_bindValue (values := bindValue values startSymbol (smoothValue x))
    (.indexed (.fiber variance seed)) (Nat.le_of_lt (Nat.lt_of_le_of_lt startHigh seedHigh))
  have agrees₁₂ := agrees₁.trans agrees₂
  refine IndexedEvaluation.letE pointEval (IndexedEvaluation.letE (seedEval _ agrees₁) ?_)
  have startFound : bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol
      (.indexed (.fiber variance seed)) startSymbol = some (smoothValue x) := by
    simp [bindValue, Nat.ne_of_lt seedHigh]
  have seedFound : bindValue (bindValue values startSymbol (smoothValue x)) seedSymbol
      (.indexed (.fiber variance seed)) seedSymbol = some (.indexed (.fiber variance seed)) := by
    simp [bindValue]
  have opaqueArgs := (opaqueEval.imp fun _ _ stable =>
    (stable.extend agrees₁₂ (Nat.le_refl _)).evaluates).map_right (f := smoothValue)
  have arguments := arguments_append (arguments_of_allPairs opaqueArgs)
    (arguments_of_allPairs (module := module)
      (terms := [.variable startSymbol pointTerm.result, .variable seedSymbol seedTerm.result])
      (results := [smoothValue x, .indexed (.fiber variance seed)])
      ⟨IndexedEvaluation.variable_value startFound, IndexedEvaluation.variable_value seedFound, trivial⟩)
  refine call_evaluates function (opaques := opaques) (points := [x]) (variance := variance) (seed := seed)
    (by simpa [functionArguments] using arguments)
    (by rw [functionParameters_length_recomputed recomputed]; simp [functionArguments, count]) [] result
    fun activation bound => ?_
  exact recomputed_function_pullback recomputed apply declared (entry_names_steps_length entry) formed morphisms
    nonempty count composable x variance seed bound

/-- The unit seed of a differential site, as `compileSite` builds it: the
covector `[1]` at the last point. -/
def unitSeed (entry : Reverse.Entry) (points : List Core.Term) (startTerm : Core.Term) : Core.Term :=
  .primitive entry.names.seed [(points.getLast?).getD startTerm, .integer 1]
    (Reverse.fiberResult entry.site entry.site.output)

theorem AllPairs.getLastD {α β : Type} {relation : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {a : α} {b : β}, AllPairs relation as bs → relation a b →
      relation (as.getLastD a) (bs.getLastD b)
  | [], [], _, _, _, head => head
  | _ :: _, _ :: _, _, _, pairs, _ => by
    rw [List.getLastD_cons, List.getLastD_cons]
    exact AllPairs.getLastD pairs.2 pairs.1
  | [], _ :: _, _, _, pairs, _ => pairs.elim
  | _ :: _, [], _, _, pairs, _ => pairs.elim

theorem getLast?_getD_cons {α : Type} (fallback : α) : ∀ (a : α) (l : List α),
    (a :: l).getLast?.getD fallback = l.getLastD a
  | _, [] => rfl
  | a, b :: l => by rw [List.getLast?_cons_cons, getLast?_getD_cons fallback b l, List.getLastD_cons]

theorem reach_eq_getLastD : ∀ (maps : List Program) (point : Program),
    reach maps point = (images maps point).getLastD point
  | [], _ => rfl
  | map :: maps, point => by rw [reach, images, List.getLastD_cons, reach_eq_getLastD maps]

/-- Point variables evaluate to the points when the activation holds them at
their symbols. -/
theorem pointVariables_evaluate {module : Module} {site : Site} {values : Values} {first : Nat}
    {points : List Program} (count : points.length = site.steps.length)
    (found : ∀ i (h : i < points.length), values (first + i) = some (smoothValue points[i])) :
    AllPairs (fun term point => Evaluates module values term (smoothValue point))
      (pointVariables site (pointSymbols first site.steps.length)) points := by
  apply allPairs_of_getElem (by rw [pointVariables_length _ _ (pointSymbols_length _ _), count])
  intro i hi ho
  obtain ⟨result, hs, equal⟩ := pointVariables_getElem site _ i hi
  rw [equal, pointSymbols_getElem]
  exact IndexedEvaluation.variable_value (found i ho)

/-- **The compiled Core of a differential site.** The Core that `compileSite`
builds for a differential, after the `let`s of the compound opaque leaves:
`let start := point; forwardLets … (let seed := unit(last point); call f
(opaques ++ points ++ [seed]))`. Under the premises of `site_saved_core`, with
the seed declaration `fiberVector` of the site's cotangent family (whose
variance is `seedVariance`), it evaluates to the saved-mode pullback, along
the chain of the step programs at `x`, of the coordinate covector `[1]` at the
last image. No chain rule is used. -/
theorem site_differential_core {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (saved : entry.site.mode = .saved)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ []) {seedVariance : Variance}
    (seedDeclared : module.declarations.primitive? entry.names.seed =
      some (.fiberVector entry.site.cotangent entry.site.smooth entry.site.output))
    (seedFamily : fiberVariance? module.declarations.indexed entry.site.cotangent = some seedVariance)
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    (composable : Composable (stepPrograms entry.site.steps opaques))
    {startSymbol seedSymbol firstPoint : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    (firstHigh : seedSymbol < firstPoint)
    {pointTerm : Core.Term} {x : Program} (pointEval : Evaluates module values pointTerm (smoothValue x))
    (result : Result) :
    Evaluates module values
        (.letE startSymbol pointTerm
          (forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
            (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length)
            (.letE seedSymbol (unitSeed entry (sitePoints entry.site (.variable startSymbol pointTerm.result)
                (pointSymbols firstPoint entry.site.steps.length)) (.variable startSymbol pointTerm.result))
              (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable startSymbol pointTerm.result)
                (pointSymbols firstPoint entry.site.steps.length) ++
                [.variable seedSymbol (Reverse.fiberResult entry.site entry.site.output)]) [] result))))
      (.indexed (.fiber .cotangent (pullback .saved (chain (stepPrograms entry.site.steps opaques)) x
        (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x), [1]⟩)))) := by
  have agrees₁ := agrees_bindValue (values := values) (smoothValue x) startHigh
  have startFound : bindValue values startSymbol (smoothValue x) startSymbol = some (smoothValue x) := by
    simp [bindValue]
  refine IndexedEvaluation.letE pointEval ?_
  have high : ∀ symbol ∈ pointSymbols firstPoint entry.site.steps.length, firstPoint ≤ symbol :=
    fun _ member => pointSymbols_high _ member
  have maps := allPairs_mapTerms (bound := firstPoint) entry.site.steps morphisms opaqueTerms opaques
    (opaqueEval.imp fun _ _ stable => stable.extend agrees₁ (by omega)) count
  refine (forwardLets_evaluates apply entry.site.steps _ (stepPrograms entry.site.steps opaques)
    (pointSymbols firstPoint entry.site.steps.length) _ firstPoint _ x _ _ maps (by rw [mapTerms_length])
    (by rw [pointSymbols_length, mapTerms_length]) high (IndexedEvaluation.variable_value startFound)).mpr ?_
  have imagesCount : (images (stepPrograms entry.site.steps opaques) x).length = entry.site.steps.length := by
    rw [images_length, stepPrograms_length]
  have agrees₃ := bindAll_agrees (bound := firstPoint) (bindValue values startSymbol (smoothValue x))
    (pointSymbols firstPoint entry.site.steps.length)
    ((images (stepPrograms entry.site.steps opaques) x).map smoothValue) high
  have notPoint : ∀ symbol, symbol < firstPoint → symbol ∉ pointSymbols firstPoint entry.site.steps.length :=
    fun symbol low member => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le low (high symbol member))
  have imageFound : ∀ i (h : i < (images (stepPrograms entry.site.steps opaques) x).length),
      bindAll (bindValue values startSymbol (smoothValue x)) (pointSymbols firstPoint entry.site.steps.length)
        ((images (stepPrograms entry.site.steps opaques) x).map smoothValue) (firstPoint + i) =
        some (smoothValue (images (stepPrograms entry.site.steps opaques) x)[i]) := by
    intro i h
    have found := bindAll_getElem (bindValue values startSymbol (smoothValue x))
      (pointSymbols firstPoint entry.site.steps.length)
      ((images (stepPrograms entry.site.steps opaques) x).map smoothValue) (pointSymbols_nodup _ _)
      (by simp [pointSymbols_length, imagesCount]) i (by rw [pointSymbols_length]; omega) (by simp; omega)
    rw [pointSymbols_getElem] at found
    simpa using found
  have startEval : Evaluates module (bindAll (bindValue values startSymbol (smoothValue x))
      (pointSymbols firstPoint entry.site.steps.length)
      ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
      (.variable startSymbol pointTerm.result) (smoothValue x) :=
    IndexedEvaluation.variable_value (by rw [bindAll_not_mem _ _ _ _ (notPoint _ (by omega))]; exact startFound)
  have lastEval := AllPairs.getLastD (relation := fun term point => Evaluates module
      (bindAll (bindValue values startSymbol (smoothValue x)) (pointSymbols firstPoint entry.site.steps.length)
        ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
      term (smoothValue point))
    (pointVariables_evaluate imagesCount imageFound) startEval
  rw [← getLast?_getD_cons (.variable startSymbol pointTerm.result)] at lastEval
  have seedEval : Evaluates module
      (bindAll (bindValue values startSymbol (smoothValue x)) (pointSymbols firstPoint entry.site.steps.length)
        ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
      (unitSeed entry (sitePoints entry.site (.variable startSymbol pointTerm.result)
      (pointSymbols firstPoint entry.site.steps.length)) (.variable startSymbol pointTerm.result))
      (.indexed (.fiber seedVariance (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x),
        [1]⟩))) :=
    IndexedEvaluation.primitive seedDeclared (IndexedEvaluation.arguments_cons lastEval
      (IndexedEvaluation.arguments_cons (IndexedEvaluation.integer _ _ 1) (IndexedEvaluation.arguments_nil _ _)))
      (by simp [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, fiberVectorValue, seedFamily,
        VastitasKernel.SmoothRuntime.vector, Value.integer?])
  refine IndexedEvaluation.letE seedEval ?_
  have agrees₄ := agrees_bindValue (values := bindAll (bindValue values startSymbol (smoothValue x))
      (pointSymbols firstPoint entry.site.steps.length)
      ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
    (.indexed (.fiber seedVariance (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x),
      [1]⟩))) (Nat.le_of_lt (Nat.lt_of_le_of_lt startHigh seedHigh))
  have opaqueArgs := (opaqueEval.imp fun _ _ stable =>
    (stable.extend ((agrees₁.trans (agrees₃.mono (by omega))).trans agrees₄) (Nat.le_refl _)).evaluates).map_right
    (f := smoothValue)
  have pointsArgs : AllPairs (fun term value => Evaluates module
      (bindValue (bindAll (bindValue values startSymbol (smoothValue x)) (pointSymbols firstPoint entry.site.steps.length)
        ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
        seedSymbol (.indexed (.fiber seedVariance
          (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x), [1]⟩))))
      term value)
      (sitePoints entry.site (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length))
      ((x :: images (stepPrograms entry.site.steps opaques) x).map smoothValue) := by
    refine AllPairs.map_right ⟨IndexedEvaluation.variable_value ?_, pointVariables_evaluate imagesCount ?_⟩
    · simp only [bindValue]
      rw [ite_eq_right (Nat.ne_of_lt seedHigh), bindAll_not_mem _ _ _ _ (notPoint _ (by omega))]
      exact startFound
    · intro i h
      simp only [bindValue]
      rw [ite_eq_right (by omega)]
      exact imageFound i h
  have seedArg : Evaluates module
      (bindValue (bindAll (bindValue values startSymbol (smoothValue x)) (pointSymbols firstPoint entry.site.steps.length)
        ((images (stepPrograms entry.site.steps opaques) x).map smoothValue))
        seedSymbol (.indexed (.fiber seedVariance
          (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x), [1]⟩))))
      (.variable seedSymbol (Reverse.fiberResult entry.site entry.site.output))
      (.indexed (.fiber seedVariance (some ⟨coordinates ((images (stepPrograms entry.site.steps opaques) x).getLastD x),
        [1]⟩))) :=
    IndexedEvaluation.variable_value (by simp [bindValue])
  refine call_evaluates function (opaques := opaques) (points := x :: images (stepPrograms entry.site.steps opaques) x)
    (arguments_append (arguments_append (arguments_of_allPairs opaqueArgs) (arguments_of_allPairs pointsArgs))
      (IndexedEvaluation.arguments_cons seedArg (IndexedEvaluation.arguments_nil _ _)))
    (by rw [functionParameters_length_saved saved]; simp [functionArguments, count, imagesCount] <;> omega) [] result
    fun activation bound => ?_
  exact saved_function_pullback saved declared (entry_names_steps_length entry) formed nonempty count composable x
    (residualRel_images _ _) seedVariance _ bound

/-- **(S) A saved site, locally.** The source site `pullback(M, point, seed)`
in either mode and the Core of `site_saved_core` evaluate to the same
covector, when the map operand `M` evaluates to a composition tree whose
leaves are the step programs (`Factors`). `compiled_site_evaluates` in
`SmoothReverseCompiled` states this for the term that `compileSite` returns.
No chain rule is used. -/
theorem site_saved_rewrite {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (saved : entry.site.mode = .saved)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ [])
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    {startSymbol seedSymbol firstPoint : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    (firstHigh : seedSymbol < firstPoint)
    {mapTerm pointTerm seedTerm : Core.Term} {x : Program} {variance : Variance} {seed : FiberValue}
    {map : Program} (mapEval : Evaluates module values mapTerm (smoothValue map))
    (factors : Factors map (stepPrograms entry.site.steps opaques))
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Stable module values bound seedTerm (.indexed (.fiber variance seed)))
    {id smooth cotangent : DeclId} {mode : PullbackMode}
    (source : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (sourceResult result : Result) :
    Evaluates module values (.primitive id [mapTerm, pointTerm, seedTerm] sourceResult)
        (.indexed (.fiber .cotangent (pullback mode map x seed))) ∧
      Evaluates module values
        (.letE startSymbol pointTerm (.letE seedSymbol seedTerm
          (forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
            (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length)
            (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable startSymbol pointTerm.result)
              (pointSymbols firstPoint entry.site.steps.length) ++ [.variable seedSymbol seedTerm.result]) [] result))))
        (.indexed (.fiber .cotangent (pullback mode map x seed))) := by
  refine ⟨source_pullback_evaluates source mapEval pointEval seedEval.evaluates sourceResult, ?_⟩
  rw [factors.pullback_chain mode factors.composable, ← pullback_saved_eq mode]
  exact site_saved_core function saved apply declared formed morphisms nonempty opaqueEval count factors.composable
    startHigh seedHigh firstHigh pointEval seedEval result

/-- **(S) A recomputing site, locally.** Under the premises of
`site_saved_rewrite` with the recomputing policy, the source site
`pullback(M, point, seed)` and the Core of `site_recomputed_core` evaluate to
the same covector. No chain rule is used. -/
theorem site_recomputed_rewrite {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (recomputed : entry.site.mode = .recomputed)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ [])
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    {startSymbol seedSymbol : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    {mapTerm pointTerm seedTerm : Core.Term} {x : Program} {variance : Variance} {seed : FiberValue}
    {map : Program} (mapEval : Evaluates module values mapTerm (smoothValue map))
    (factors : Factors map (stepPrograms entry.site.steps opaques))
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Stable module values bound seedTerm (.indexed (.fiber variance seed)))
    {id smooth cotangent : DeclId} {mode : PullbackMode}
    (source : module.declarations.primitive? id = some (.cotangentPullback smooth cotangent mode))
    (sourceResult result : Result) :
    Evaluates module values (.primitive id [mapTerm, pointTerm, seedTerm] sourceResult)
        (.indexed (.fiber .cotangent (pullback mode map x seed))) ∧
      Evaluates module values
        (.letE startSymbol pointTerm (.letE seedSymbol seedTerm
          (.call entry.function (opaqueTerms ++ [.variable startSymbol pointTerm.result,
            .variable seedSymbol seedTerm.result]) [] result)))
        (.indexed (.fiber .cotangent (pullback mode map x seed))) := by
  refine ⟨source_pullback_evaluates source mapEval pointEval seedEval.evaluates sourceResult, ?_⟩
  rw [factors.pullback_chain mode factors.composable, ← pullback_saved_eq mode,
    VastitasOracle.SmoothRuntime.pullback_saved_eq_recomputed]
  exact site_recomputed_core function recomputed apply declared formed morphisms nonempty opaqueEval count
    factors.composable startHigh seedHigh pointEval seedEval result

/-- **(S) A differential site, locally.** Under the premises of
`site_saved_rewrite`, with the seed declaration `fiberVector` of the site's
cotangent family, the source site `differential(φ, point)`, with `φ`
evaluating to a composition tree of the step programs, and the Core of
`site_differential_core` evaluate to the same covector. No chain rule is
used. -/
theorem site_differential_rewrite {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (saved : entry.site.mode = .saved)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ []) {seedVariance : Variance}
    (seedDeclared : module.declarations.primitive? entry.names.seed =
      some (.fiberVector entry.site.cotangent entry.site.smooth entry.site.output))
    (seedFamily : fiberVariance? module.declarations.indexed entry.site.cotangent = some seedVariance)
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    {startSymbol seedSymbol firstPoint : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    (firstHigh : seedSymbol < firstPoint)
    {functionTerm pointTerm : Core.Term} {map x : Program}
    (mapEval : Evaluates module values functionTerm (smoothValue map))
    (factors : Factors map (stepPrograms entry.site.steps opaques))
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    {id smooth cotangent line : DeclId}
    (source : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (sourceResult result : Result) :
    Evaluates module values (.primitive id [functionTerm, pointTerm] sourceResult)
        (.indexed (.fiber .cotangent (VastitasKernel.SmoothRuntime.differential map x))) ∧
      Evaluates module values
        (.letE startSymbol pointTerm
          (forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
            (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length)
            (.letE seedSymbol (unitSeed entry (sitePoints entry.site (.variable startSymbol pointTerm.result)
                (pointSymbols firstPoint entry.site.steps.length)) (.variable startSymbol pointTerm.result))
              (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable startSymbol pointTerm.result)
                (pointSymbols firstPoint entry.site.steps.length) ++
                [.variable seedSymbol (Reverse.fiberResult entry.site entry.site.output)]) [] result))))
        (.indexed (.fiber .cotangent (VastitasKernel.SmoothRuntime.differential map x))) := by
  refine ⟨IndexedEvaluation.primitive source (IndexedEvaluation.arguments_cons mapEval
    (IndexedEvaluation.arguments_cons pointEval (IndexedEvaluation.arguments_nil _ _))) rfl, ?_⟩
  rw [VastitasOracle.SmoothRuntime.differential_eq_pullback, factors.pullback_chain .saved factors.composable,
    ← factors.coordinates_reach, reach_eq_getLastD]
  exact site_differential_core function saved apply declared formed morphisms nonempty seedDeclared seedFamily
    opaqueEval count factors.composable startHigh seedHigh firstHigh pointEval result

/-- **(S) A tape site, locally.** The reverse pass of a tape that `linearize`
builds, `backward(linearize(M, point), seed)`, compiles to the Core of a saved
site. With a declaration `builder` whose derivative rule is `tape` and a
declaration `id` whose rule is the `backward` pass, the source call and the
Core of `site_saved_core` evaluate to the same covector, under the premises of
`site_saved_rewrite`. `SmoothRuntime.backward_linearize` relates the two
passes. No chain rule is used. -/
theorem site_tape_rewrite {module : Module} {entry : Reverse.Entry}
    (function : module.functions.find? (fun function => function.id == entry.function) = some entry.generated)
    (saved : entry.site.mode = .saved)
    (apply : module.declarations.primitive? entry.names.apply = some (.smoothApply entry.site.smooth))
    (declared : StepsDeclared module entry.names entry.site)
    (formed : ∀ step ∈ entry.site.steps, StepFormed step) (morphisms : MorphismsDeclared module entry.site.steps)
    (nonempty : entry.site.steps ≠ [])
    {values : Values} {bound : Nat} {opaqueTerms : List Core.Term} {opaques : List Program}
    (opaqueEval : AllPairs (fun term program => Stable module values bound term (smoothValue program))
      opaqueTerms opaques)
    (count : opaques.length = entry.site.opaqueSteps.length)
    {startSymbol seedSymbol firstPoint : Nat} (startHigh : bound ≤ startSymbol) (seedHigh : startSymbol < seedSymbol)
    (firstHigh : seedSymbol < firstPoint)
    {mapTerm pointTerm seedTerm : Core.Term} {x : Program} {variance : Variance} {seed : FiberValue}
    {map : Program} (mapEval : Evaluates module values mapTerm (smoothValue map))
    (factors : Factors map (stepPrograms entry.site.steps opaques))
    (pointEval : Evaluates module values pointTerm (smoothValue x))
    (seedEval : Stable module values bound seedTerm (.indexed (.fiber variance seed)))
    {builder id : DeclId} (tape : Reverse.ruleOf module.declarations builder = .tape)
    (pass : Reverse.ruleOf module.declarations id = .pass .backward)
    (tapeResult sourceResult result : Result) :
    Evaluates module values
        (.primitive id [.primitive builder [mapTerm, pointTerm] tapeResult, seedTerm] sourceResult)
        (.indexed (.fiber .cotangent (pullback .saved map x seed))) ∧
      Evaluates module values
        (.letE startSymbol pointTerm (.letE seedSymbol seedTerm
          (forwardLets entry.names entry.site entry.site.steps (mapTerms entry.site.steps opaqueTerms)
            (.variable startSymbol pointTerm.result) (pointSymbols firstPoint entry.site.steps.length)
            (.call entry.function (opaqueTerms ++ sitePoints entry.site (.variable startSymbol pointTerm.result)
              (pointSymbols firstPoint entry.site.steps.length) ++ [.variable seedSymbol seedTerm.result]) [] result))))
        (.indexed (.fiber .cotangent (pullback .saved map x seed))) := by
  refine ⟨?_, ?_⟩
  · rw [← VastitasOracle.SmoothRuntime.backward_linearize]
    exact pass_backward_evaluates pass (tape_evaluates tape mapEval pointEval tapeResult) seedEval.evaluates
      sourceResult
  · rw [factors.pullback_chain .saved factors.composable]
    exact site_saved_core function saved apply declared formed morphisms nonempty opaqueEval count
      factors.composable startHigh seedHigh firstHigh pointEval seedEval result

end VastitasOracle.SmoothReverseCore
