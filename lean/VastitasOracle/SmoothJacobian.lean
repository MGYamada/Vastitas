import VastitasKernel.IndexedSemantics
import VastitasOracle.SmoothRuntime
import VastitasOracle.SmoothCanonical
import VastitasOracle.SmoothPrimitives
import VastitasOracle.SmoothFibers
import VastitasOracle.IndexedAssociations
import VastitasOracle.IndexedPrimitiveSoundness

set_option autoImplicit false

/-! The steps of compiled reverse Core and the derivative rules (#623).

Compiled reverse Core replaces a reverse pass by forward and backward Core
that the kernel generates. The kernel declares two bindings for it, which no
source or wire form names. The forward Core calls `smoothApply`. It evaluates
each map at the point the previous step produced and keeps the image as an
evaluated point, `SmoothRuntime.applyPoint`. The backward Core calls
`cotangentJacobian` once per declared map. The step evaluates the map's
Jacobian table at the saved input point, `SmoothRuntime.jacobianStep`.

The runtime theorems state what the two operations compute:

- an evaluated point has the coordinates it was built from
  (`coordinates_ratPoint`), so the image of a point has the coordinates of the
  map's value (`coordinates_applyPoint`);
- a Jacobian table applied to a seed is `cot` (`transposeApply_jacobian`);
- one table step along a declared map is the pullback along that map, in
  either mode, whenever the saved output point has the coordinates of the
  map's image (`jacobianStep_eq_of_output`, `jacobianStep_eq`);
- a pullback reads its point only through the point's coordinates
  (`pullback_congr_point`), so a pullback along a composite runs through the
  evaluated intermediate point (`pullback_stepwise_applyPoint`).

None of them needs a well-typedness premise. The registry section proves the
association, shape, totality and erasure lemmas of the two bindings and their
`Sound` instances; `IndexedSemantics.registry_sound` dispatches to them.

The last section states what the derivative rule of a descriptor promises
about its logical evaluator (`ReverseSound`), and proves the promise for
every registry entry by name (`registry_reverse_sound`). A rule other than
`none` characterizes the evaluator exactly: the call evaluates on the operand
values the rule names and on no other list, and its value is the value the
rule names. -/
namespace VastitasOracle.SmoothJacobian

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.SmoothPrimitives VastitasOracle.SmoothFibers VastitasOracle.IndexedPrimitiveSoundness

/-! ## Evaluated points and Jacobian tables -/

section Runtime

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

/-- A constant polynomial in no coordinate takes its value at the empty point. -/
theorem evalAt_const_zero (value : Rat) : evalAt (Poly.const 0 value) [] = value := by
  unfold Poly.const
  split
  · rename_i zero
    simp only [beq_iff_eq] at zero
    simp [evalAt, zero]
  · simp [evalAt, monomialValue, Monomial.one, Rat.add_zero]

/-- An evaluated point has the coordinates it is built from. -/
theorem coordinates_ratPoint (values : List Rat) : coordinates (ratPoint values) = values := by
  simp [coordinates, ratPoint, Program.eval, apply, List.map_map, Function.comp_def, evalAt_const_zero]

/-- An evaluated point with `n` coordinates is a well-typed point of `ℝⁿ`: a
program from `ℝ⁰` to `ℝⁿ`. -/
theorem ratPoint_wellTyped (values : List Rat) : (ratPoint values).wellTyped 0 values.length = true := by
  simp only [ratPoint, Program.wellTyped, VastitasOracle.SmoothCanonical.wellFormed_iff, List.length_map,
    true_and]
  intro image member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact VastitasOracle.SmoothCanonical.const_canonical 0 _

/-- The image of a point under a program has the coordinates of the program's
value at the point's coordinates. -/
theorem coordinates_applyPoint (map point : Program) :
    coordinates (applyPoint map point) = map.eval (coordinates point) :=
  coordinates_ratPoint _

/-- The image of any point under a program checked as `ℝⁿ → ℝᵐ` is a
well-typed point of `ℝᵐ`. -/
theorem applyPoint_wellTyped {map : Program} {n m : Nat} (hmap : map.wellTyped n m = true) (point : Program) :
    (applyPoint map point).wellTyped 0 m = true := by
  have typed := ratPoint_wellTyped (map.eval (coordinates point))
  rwa [VastitasOracle.SmoothRuntime.eval_length, VastitasOracle.SmoothRuntime.wellTyped_outputArity hmap]
    at typed

/-- The Jacobian table of a map, applied to a seed at a point, is `cot`: the
transpose of the map's Jacobian at the point, applied to the seed. -/
theorem transposeApply_jacobian (map : Map) (point seed : List Rat) :
    transposeApply (jacobian map) point seed = cot map point seed := by
  simp [transposeApply, jacobian, cot, List.map_map, Function.comp_def]

/-- A Jacobian table applied to a seed has one component per source
coordinate of the map. -/
theorem transposeApply_jacobian_length (map : Map) (point seed : List Rat) :
    (transposeApply (jacobian map) point seed).length = map.arity := by
  rw [transposeApply_jacobian, VastitasOracle.SmoothRuntime.cot_length]

/-- **One table step is the pullback along its map.** Let `output` be a saved
point whose coordinates are the image of `input`'s coordinates under `map`.
Then the table step along `map` from `input` and `output` is the pullback
along the declared map `map` at `input`, in either mode, for every seed:
a covector over the image, a seed over another point or with another
component count, and the failure value. -/
theorem jacobianStep_eq_of_output (mode : PullbackMode) (map : Map) (input output : Program)
    (saved : coordinates output = apply map (coordinates input)) (seed : FiberValue) :
    jacobianStep map.images.length (jacobian map) input output seed = pullback mode (.primitive map) input seed := by
  cases seed with
  | none => rw [VastitasOracle.SmoothRuntime.pullback_none]; rfl
  | some seed =>
    rw [VastitasOracle.SmoothRuntime.pullback_spec]
    simp only [jacobianStep, saved, transposeApply_jacobian, Program.eval, Program.outputArity, Program.reverse,
      beq_iff_eq, Bool.and_eq_true]
    by_cases over : seed.point = apply map (coordinates input) ∧ seed.components.length = map.images.length
    · rw [ite_eq_left over]
      exact (ite_eq_left over).symm
    · rw [ite_eq_right over]
      exact (ite_eq_right over).symm

/-- **The table step on the evaluated image.** The table step along a
declared map from a point and its evaluated image, `applyPoint`, is the
saved-mode pullback along the map at the point, for every seed. -/
theorem jacobianStep_eq (map : Map) (point : Program) (seed : FiberValue) :
    jacobianStep map.images.length (jacobian map) point (applyPoint (.primitive map) point) seed =
      pullback .saved (.primitive map) point seed :=
  jacobianStep_eq_of_output .saved map point _ (coordinates_applyPoint _ _) seed

/-- A pullback reads its point only through the point's coordinates: two
points with the same coordinates give the same pullback, in either mode, for
every seed. -/
theorem pullback_congr_point (mode : PullbackMode) (map : Program) {point point' : Program}
    (same : coordinates point = coordinates point') (seed : FiberValue) :
    pullback mode map point seed = pullback mode map point' seed := by
  cases seed with
  | none => rw [VastitasOracle.SmoothRuntime.pullback_none, VastitasOracle.SmoothRuntime.pullback_none]
  | some seed => rw [VastitasOracle.SmoothRuntime.pullback_spec, VastitasOracle.SmoothRuntime.pullback_spec, same]

/-- **Stepwise pullback through an evaluated point.** When the source
dimension of `outer` is the target dimension of `inner`, the pullback along
`outer ∘ inner` at `point` is the pullback along `outer` at the evaluated
image `applyPoint inner point`, followed by the pullback along `inner` at
`point`, in either mode, for every seed. -/
theorem pullback_stepwise_applyPoint (mode : PullbackMode) (outer inner point : Program) (seed : FiberValue)
    (arity : outer.inputArity = inner.outputArity) :
    pullback mode (.compose outer inner) point seed =
      pullback mode inner point (pullback mode outer (applyPoint inner point) seed) := by
  rw [VastitasOracle.SmoothRuntime.pullback_stepwise mode outer inner point seed arity,
    pullback_congr_point mode outer (point := .compose inner point) (point' := applyPoint inner point)
      (by rw [coordinates_applyPoint]; rfl)]

/-- A table step along a map checked as `ℝⁿ → ℝᵐ` from a point of `ℝⁿ`
returns the failure value or a fiber whose point and components both have `n`
entries, whatever the saved output point. -/
theorem jacobianStep_typed {map : Map} {n m : Nat} (hmap : wellFormed n m map = true) {input : Program}
    (hinput : input.wellTyped 0 n = true) (output : Program) (seed : FiberValue) :
    FiberTyped n (jacobianStep map.images.length (jacobian map) input output seed) := by
  obtain ⟨arity, -⟩ := (VastitasOracle.SmoothCanonical.wellFormed_iff n m map).mp hmap
  cases seed with
  | none => trivial
  | some seed =>
    simp only [jacobianStep]
    split
    · exact ⟨coordinates_length hinput, by rw [transposeApply_jacobian_length, arity]⟩
    · trivial

end Runtime

/-! ## The registry entries of the two steps -/

theorem smoothApply_total {env : Indexed.Environment} {world : World} {smooth mf pf point : DeclId}
    {x y x' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {output : ValueType}
    {values : List Value}
    (rule : PrimitiveTyped env (.smoothApply smooth) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩]) :
    SmoothOutcome env world (.smoothApply smooth) values output := by
  have valid : smoothApplyValid env smooth = true := rule.bindingValid
  obtain ⟨rfl, rfl, rfl, pointZero, rfl⟩ := IndexedAssociations.smoothApply_association.mp rule.association
  have smoothRepresentation := smooth_family valid
  obtain ⟨mapValue, pointValue, rfl, mapTyped, pointTyped⟩ := values_pair typed
  obtain ⟨map, program, a, b, n, m, rfl, rfl, rfl, rfl, _, hb, mapWellTyped, _⟩ :=
    map_and_point smoothRepresentation pointZero mapTyped pointTyped
  exact ⟨_, rfl, smooth_typed smoothRepresentation rule.resultValid rfl pointZero hb
    (applyPoint_wellTyped mapWellTyped program)⟩

/-- Typed totality of a backward step on the operand list of an accepted
call, for a map whose type names two objects: the input is a point of the
map's source `X`, so the step returns a covector of `X` or the failure value. -/
theorem cotangentJacobian_total {env : Indexed.Environment} {world : World} {cotangent family point : DeclId}
    {map : AlgebraRuntime.Map} {source target p : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (rule : PrimitiveTyped env (.cotangentJacobian cotangent ⟨family, [.object source, .object target]⟩ map)
      allowed brand
      [.indexed ⟨family, [.object p, .object source]⟩, .indexed ⟨family, [.object (.global point), .object target]⟩,
        .indexed ⟨cotangent, [.object target]⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨family, [.object p, .object source]⟩, .indexed ⟨family, [.object (.global point), .object target]⟩,
        .indexed ⟨cotangent, [.object target]⟩]) :
    SmoothOutcome env world (.cotangentJacobian cotangent ⟨family, [.object source, .object target]⟩ map) values
      output := by
  have valid : cotangentJacobianValid env cotangent ⟨family, [.object source, .object target]⟩ map = true :=
    rule.bindingValid
  obtain ⟨-, -, -, -, -, -, rfl, pointZero, rfl⟩ :=
    IndexedAssociations.cotangentJacobian_association.mp rule.association
  unfold cotangentJacobianValid smoothConstantValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨smoothFamily, _⟩, endpoints⟩, cotangentFamily⟩, _⟩ := valid
  cases found : smoothEndpoints? env ⟨family, [.object source, .object target]⟩ with
  | none => simp [found] at endpoints
  | some dimensions =>
    obtain ⟨n, m⟩ := dimensions
    simp only [found] at endpoints
    obtain ⟨s, t, indices, hs, _⟩ := endpoints_spec found
    simp only [List.cons.injEq, Index.object.injEq, and_true] at indices
    obtain ⟨rfl, rfl⟩ := indices
    have smoothRepresentation : familyRepresentation env family = some .smooth := smooth_family smoothFamily
    have cotangentRepresentation := fiber_family_cotangent cotangentFamily
    obtain ⟨inputValue, outputValue, seedValue, rfl, inputTyped, outputTyped, seedTyped⟩ := values_triple typed
    obtain ⟨input, n', rfl, hs', inputWellTyped⟩ := point_value smoothRepresentation pointZero inputTyped
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    obtain ⟨output, _, _, _, _, rfl, _⟩ := smooth_value smoothRepresentation outputTyped
    obtain ⟨seed, _, _, rfl, _⟩ := fiber_value cotangentRepresentation seedTyped
    exact ⟨_, rfl, fiber_typed cotangentRepresentation rule.resultValid rfl hs
      (jacobianStep_typed endpoints inputWellTyped output seed)⟩

/-- A successful backward step erases to the runtime step on the erased
operands. -/
theorem cotangentJacobian_erasure {env : Indexed.Environment} {cotangent : DeclId} {application : Application}
    {map : AlgebraRuntime.Map} {values : List Value} {value : Value}
    (evaluated : evalPrimitive env (.cotangentJacobian cotangent application map) values = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧ erasePrimitiveValue value = some output ∧
      evalRuntimePrimitive (.cotangentJacobian cotangent application map) inputs = some output := by
  simp only [evalPrimitive, PrimitiveBinding.contract] at evaluated
  simp only [evalRuntimePrimitive, PrimitiveBinding.contract]
  split at evaluated
  · simp only [PrimitiveDescriptor.ofBool] at evaluated ⊢
    split at evaluated
    · cases evaluated
      exact ⟨_, _, rfl, rfl, rfl⟩
    · contradiction
  · simp [PrimitiveDescriptor.ofBool] at evaluated

theorem smoothApply_sound (smooth : DeclId) : Sound (PrimitiveBinding.smoothApply smooth).contract :=
  .ofPure rfl
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨x, y, point, x', rfl⟩ := IndexedAssociations.smoothApply_shape rule.association
      exact smoothApply_total rule typed)
    (by
      intro env values value evaluated
      erase_matched evaluated)

theorem cotangentJacobian_sound (cotangent : DeclId) (application : Application) (map : AlgebraRuntime.Map) :
    Sound (PrimitiveBinding.cotangentJacobian cotangent application map).contract :=
  .ofPure (by simp only [PrimitiveBinding.contract]; split <;> rfl)
    (by
      intro env world allowed brand arguments output values rule typed
      obtain ⟨family, indices⟩ := application
      obtain ⟨source, target, p, point, equal, rfl⟩ := IndexedAssociations.cotangentJacobian_shape rule.association
      change indices = _ at equal
      subst equal
      exact cotangentJacobian_total rule typed)
    (by
      intro env values value evaluated
      exact cotangentJacobian_erasure evaluated)

/-! ## Derivative rules -/

/-- What the derivative rule of a descriptor promises about its logical
evaluator. `none` promises nothing. Every other rule names the operand values
a call evaluates on and the value it returns; the call evaluates on those
operand lists and on no other.

- `morphism map`: the call has no operands, and its value is the declared
  map `map` as one program node.
- `chain after before`: the operand list has the shape's operand count, it
  holds programs `first` at position `after` and `second` at position
  `before`, and the value is the program node `compose first second`.
- `tape`: the operands are a map and a point, and the value is their tape.
- `pass (pullback mode)`: the operands are a map, a point and a fiber, and the
  value is the pullback in mode `mode`, as a covector.
- `pass differential`: the operands are a function and a point, and the value
  is the differential, as a covector.
- `pass backward`: the operands are a tape and a fiber, and the value is the
  reverse pass over the tape, as a covector. -/
def ReverseSound (descriptor : PrimitiveDescriptor) : Prop :=
  match descriptor.reverse with
  | .none => True
  | .morphism map => ∀ env values value,
      descriptor.eval env values = some value ↔ values = [] ∧ value = .indexed (.smooth (.primitive map))
  | .chain after before => ∀ env values value,
      descriptor.eval env values = some value ↔
        ∃ first second, values.length = descriptor.shape.operands.length ∧
          values[after]? = some (.indexed (.smooth first)) ∧ values[before]? = some (.indexed (.smooth second)) ∧
          value = .indexed (.smooth (.compose first second))
  | .tape => ∀ env values value,
      descriptor.eval env values = some value ↔
        ∃ map point, values = [.indexed (.smooth map), .indexed (.smooth point)] ∧
          value = .indexed (.tape (SmoothRuntime.linearize map point))
  | .pass (.pullback mode) => ∀ env values value,
      descriptor.eval env values = some value ↔
        ∃ map point variance seed,
          values = [.indexed (.smooth map), .indexed (.smooth point), .indexed (.fiber variance seed)] ∧
          value = .indexed (.fiber .cotangent (SmoothRuntime.pullback mode map point seed))
  | .pass .differential => ∀ env values value,
      descriptor.eval env values = some value ↔
        ∃ function point, values = [.indexed (.smooth function), .indexed (.smooth point)] ∧
          value = .indexed (.fiber .cotangent (SmoothRuntime.differential function point))
  | .pass .backward => ∀ env values value,
      descriptor.eval env values = some value ↔
        ∃ tape variance seed, values = [.indexed (.tape tape), .indexed (.fiber variance seed)] ∧
          value = .indexed (.fiber .cotangent (SmoothRuntime.backward tape seed))

/-- A declared smooth map evaluates, with no operands, to its own map as one
program node. -/
theorem smoothConstant_reverse (application : Application) (map : AlgebraRuntime.Map) :
    ReverseSound (PrimitiveBinding.smoothConstant application map).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨rfl, rfl⟩
    · contradiction
  · rintro ⟨rfl, rfl⟩
    rfl

/-- `compose` evaluates exactly on two programs, to the program node that
composes them: the first operand runs after the second. -/
theorem smoothCompose_reverse (family : DeclId) :
    ReverseSound (PrimitiveBinding.smoothCompose family).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · contradiction
  · rintro ⟨first, second, length, atAfter, atBefore, rfl⟩
    rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at atAfter
    · simp at atBefore
    · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at atAfter atBefore
      subst atAfter atBefore
      rfl
    · simp at length

/-- `linearize` evaluates exactly on a map and a point, to their tape. -/
theorem linearize_reverse (smooth tape : DeclId) : ReverseSound (PrimitiveBinding.linearize smooth tape).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨_, _, rfl, rfl⟩
    · contradiction
  · rintro ⟨map, point, rfl, rfl⟩
    rfl

/-- `cotangent_pullback` in mode `mode` evaluates exactly on a map, a point
and a fiber, to the pullback in that mode. -/
theorem cotangentPullback_reverse (smooth cotangent : DeclId) (mode : SmoothRuntime.PullbackMode) :
    ReverseSound (PrimitiveBinding.cotangentPullback smooth cotangent mode).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨_, _, _, _, rfl, rfl⟩
    · contradiction
  · rintro ⟨map, point, variance, seed, rfl, rfl⟩
    rfl

/-- `differential` evaluates exactly on a function and a point, to the
differential. -/
theorem differential_reverse (smooth cotangent line : DeclId) :
    ReverseSound (PrimitiveBinding.differential smooth cotangent line).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨_, _, rfl, rfl⟩
    · contradiction
  · rintro ⟨function, point, rfl, rfl⟩
    rfl

/-- `cotangent_backward` evaluates exactly on a tape and a fiber, to the
reverse pass over the tape. -/
theorem cotangentBackward_reverse (tape cotangent : DeclId) :
    ReverseSound (PrimitiveBinding.cotangentBackward tape cotangent).contract := by
  simp only [ReverseSound, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool]
  intro env values value
  constructor
  · intro evaluated
    split at evaluated
    · cases evaluated
      exact ⟨_, _, _, rfl, rfl⟩
    · contradiction
  · rintro ⟨record, variance, seed, rfl, rfl⟩
    rfl

/-- A backward step states the rule `none`, whatever its map type: the
compilation does not open it. -/
theorem cotangentJacobian_reverse (cotangent : DeclId) (application : Application) (map : AlgebraRuntime.Map) :
    ReverseSound (PrimitiveBinding.cotangentJacobian cotangent application map).contract := by
  have rule : (PrimitiveBinding.cotangentJacobian cotangent application map).contract.reverse = .none := by
    simp only [PrimitiveBinding.contract]
    split <;> rfl
  unfold ReverseSound
  rw [rule]
  trivial

/-- **Every registry entry keeps the promise of its derivative rule.** The
proof names every binding. The entries with rule `none` hold trivially. -/
theorem registry_reverse_sound : ∀ binding : PrimitiveBinding, ReverseSound binding.contract
  | .descriptor _ => trivial
  | .global _ => trivial
  | .origin _ _ _ => trivial
  | .identity _ _ => trivial
  | .dimension _ => trivial
  | .compose _ => trivial
  | .apply _ _ => trivial
  | .relativeConstant _ _ => trivial
  | .relativeCompose _ => trivial
  | .relativeView _ _ _ => trivial
  | .relativeEqual _ => trivial
  | .relativeCoefficient _ _ _ _ _ => trivial
  | .relativeIntPoint _ _ _ => trivial
  | .relativePair _ _ => trivial
  | .relativeIso _ _ => trivial
  | .relativeCartesian _ _ _ _ => trivial
  | .smoothConstant application map => smoothConstant_reverse application map
  | .smoothCompose family => smoothCompose_reverse family
  | .smoothEqual _ => trivial
  | .smoothIntPoint _ _ _ => trivial
  | .smoothComposite _ => trivial
  | .fiberVector _ _ _ => trivial
  | .fiberAt _ _ => trivial
  | .fiberEqual _ => trivial
  | .fiberComponent _ _ _ => trivial
  | .fiberPairing _ _ => trivial
  | .cotangentPullback smooth cotangent mode => cotangentPullback_reverse smooth cotangent mode
  | .differential smooth cotangent line => differential_reverse smooth cotangent line
  | .linearize smooth tape => linearize_reverse smooth tape
  | .cotangentBackward tape cotangent => cotangentBackward_reverse tape cotangent
  | .smoothApply _ => trivial
  | .cotangentJacobian cotangent application map => cotangentJacobian_reverse cotangent application map
  | .metricFlat _ _ _ _ _ => trivial
  | .metricSharp _ _ _ _ _ _ _ => trivial
  | .frameEncode _ _ _ _ => trivial
  | .frameDecode _ _ _ _ => trivial
  | .frameVector _ _ _ _ => trivial
  | .frameMatrix _ _ _ _ => trivial
  | .frameTransition _ _ _ _ => trivial
  | .frameApply _ _ => trivial
  | .frameCoapply _ _ => trivial
  | .frameCompose _ => trivial
  | .framePairing _ _ => trivial
  | .frameComponent _ _ => trivial
  | .frameEntry _ _ _ => trivial
  | .frameEqual _ => trivial
  | .frameAt _ _ => trivial

end VastitasOracle.SmoothJacobian
