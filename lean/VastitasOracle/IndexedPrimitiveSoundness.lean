import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! Soundness of one primitive descriptor (#622).

`Sound` states the two semantic obligations of a registry entry on the
entry's own data. Typed totality: an accepted call on typed operand values
evaluates to a value of the checked result type, in a world that keeps every
prior binding and differs from the old one only at the brand an allocating
call binds. Runtime erasure: a successful logical evaluation erases to the
runtime evaluator on the erased operands. `IndexedSemantics.registry_sound`
proves `Sound` for every registry entry by name, and
`primitive_total_and_typed` and `primitive_runtime_erasure` are its
corollaries. A new binding proves its own instance in the module of its
totality lemma, with `Sound.ofBinding`, or `Sound.ofPure` when it does not
allocate, and adds its case to `registry_sound`. -/
namespace VastitasOracle.IndexedPrimitiveSoundness

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

/-- The logical world after a call: an allocating descriptor binds the
returned object to the result's brand, every other call leaves the world
unchanged. Runtime execution does not inspect brands; the update records only
the declared fresh slot. -/
def descriptorWorld (descriptor : PrimitiveDescriptor) (world : World) (output : ValueType)
    (value : Value) : World :=
  if descriptor.shape.allocates then
    match output, value with
    | .object _ (.local _ brand), .object object => bindLocal world brand object
    | _, _ => world
  else world

theorem descriptorWorld_pure {descriptor : PrimitiveDescriptor} (pure : descriptor.shape.allocates = false)
    (world : World) (output : ValueType) (value : Value) :
    descriptorWorld descriptor world output value = world := by
  simp [descriptorWorld, pure]

theorem descriptorWorld_allocating {descriptor : PrimitiveDescriptor}
    (allocates : descriptor.shape.allocates = true) (world : World) (output : ValueType) (value : Value) :
    descriptorWorld descriptor world output value =
      match output, value with
      | .object _ (.local _ brand), .object object => bindLocal world brand object
      | _, _ => world := by
  simp [descriptorWorld, allocates]

/-- The semantic obligations of a descriptor. -/
structure Sound (descriptor : PrimitiveDescriptor) : Prop where
  /-- Typed totality. The fresh slot of an allocating call is a premise; the
  module's allocation audit establishes it. -/
  total : ∀ {env : Indexed.Environment} {world : World} {allowed : List Indexed.ObjectRef} {brand : Nat}
    {arguments : List ValueType} {output : ValueType} {values : List Value},
    descriptor.validProp env → (∀ argument ∈ arguments, argument.Valid env) → output.Valid env →
    Shape.Association env descriptor.shape allowed brand arguments output →
    PrimitiveValuesHaveTypes env world values arguments →
    (descriptor.shape.allocates = true → world brand = none) →
    ∃ after value, descriptor.eval env values = some value ∧ WorldExtends world after ∧
      PrimitiveValueHasType env after value output ∧ after = descriptorWorld descriptor world output value
  /-- Runtime erasure. -/
  erasure : ∀ {env : Indexed.Environment} {values : List Value} {value : Value},
    descriptor.eval env values = some value →
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧ descriptor.evalRuntime inputs = some output

/-- The instance of a binding, from a totality lemma stated on the binding with
`PrimitiveTyped` and `PrimitiveFresh`, and its erasure lemma. -/
theorem Sound.ofBinding {binding : PrimitiveBinding}
    (totality : ∀ {env : Indexed.Environment} {world : World} {allowed : List Indexed.ObjectRef} {brand : Nat}
      {arguments : List ValueType} {output : ValueType} {values : List Value},
      PrimitiveTyped env binding allowed brand arguments output →
      PrimitiveValuesHaveTypes env world values arguments → PrimitiveFresh binding world brand →
      ∃ after value, evalPrimitive env binding values = some value ∧ WorldExtends world after ∧
        PrimitiveValueHasType env after value output ∧ after = descriptorWorld binding.contract world output value)
    (erasing : ∀ {env : Indexed.Environment} {values : List Value} {value : Value},
      evalPrimitive env binding values = some value →
      ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
        erasePrimitiveValue value = some output ∧ evalRuntimePrimitive binding inputs = some output) :
    Sound binding.contract where
  total valid argumentsValid resultValid association typed fresh :=
    totality ⟨valid, argumentsValid, resultValid, association⟩ typed fresh
  erasure := erasing

/-- The instance of a binding that does not allocate, from a totality lemma
that leaves the world unchanged. -/
theorem Sound.ofPure {binding : PrimitiveBinding} (pure : binding.contract.shape.allocates = false)
    (totality : ∀ {env : Indexed.Environment} {world : World} {allowed : List Indexed.ObjectRef} {brand : Nat}
      {arguments : List ValueType} {output : ValueType} {values : List Value},
      PrimitiveTyped env binding allowed brand arguments output →
      PrimitiveValuesHaveTypes env world values arguments →
      ∃ value, evalPrimitive env binding values = some value ∧ PrimitiveValueHasType env world value output)
    (erasing : ∀ {env : Indexed.Environment} {values : List Value} {value : Value},
      evalPrimitive env binding values = some value →
      ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
        erasePrimitiveValue value = some output ∧ evalRuntimePrimitive binding inputs = some output) :
    Sound binding.contract :=
  .ofBinding
    (by
      intro env world allowed brand arguments output values rule typed _
      obtain ⟨value, evaluated, valueTyped⟩ := totality rule typed
      exact ⟨world, value, evaluated, fun _ _ found => found, valueTyped,
        (descriptorWorld_pure pure world output value).symm⟩)
    erasing

/-- Erasure of a registry entry whose evaluators match one operand pattern:
expose the entry's match in the hypothesis, split it, and erase the matched
operand values and the result by computation. -/
scoped macro "erase_matched" h:ident : tactic =>
  `(tactic| (simp only [evalPrimitive, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool] at $h:ident;
             split at $h:ident <;> first | contradiction | (cases $h:ident; exact ⟨_, _, rfl, rfl, rfl⟩)))

end VastitasOracle.IndexedPrimitiveSoundness
