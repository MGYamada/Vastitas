import VastitasKernel.IndexedPrimitiveShapes

set_option autoImplicit false

/-! One checked descriptor per indexed primitive (#622).

A `PrimitiveDescriptor` holds what the kernel derives for one bound primitive.
The registry (`IndexedPrimitiveRegistry`) builds one descriptor per
`PrimitiveBinding` constructor from the binding's own data; `IndexedPrimitives`
derives the binding validity contract, the operand association, result
inference and the operand count from it, `IndexedCore` the argument hints and
`IndexedSourceDiagnostics` the role table. Evaluation, lowering and the wire
decoder are still per-constructor tables; the later steps of #622 move them
here, so a new constructor today still needs a case in each of them.

The validity contract is a `Bool` that the checker runs together with the
`Prop` that the proofs use; the descriptor carries the proof that they agree,
so the two cannot drift apart. The association is a `Shape`, one datum for the
contract, the inference and the diagnostics. A descriptor grants no
authority: the all-body audits and the public acceptance path are unchanged. -/
namespace VastitasKernel.Indexed

structure PrimitiveDescriptor where
  /-- The operands, their agreements and the result type. -/
  shape : Shape
  /-- The binding contract as the proofs state it. -/
  validProp : Environment → Prop
  /-- The binding contract as the checker decides it. -/
  validBool : Environment → Bool
  /-- The two contracts agree; the registry entry proves it once. -/
  valid_iff : ∀ env, validBool env = true ↔ validProp env

/-- A descriptor whose contract is one executable check. -/
def PrimitiveDescriptor.ofBool (shape : Shape) (check : Environment → Bool) : PrimitiveDescriptor where
  shape := shape
  validProp env := check env = true
  validBool := check
  valid_iff _ := Iff.rfl

end VastitasKernel.Indexed
