import VastitasKernel.Indexed

/-! One checked descriptor per indexed primitive (#622).

A `PrimitiveDescriptor` holds what the kernel derives for one bound primitive.
The registry (`IndexedPrimitiveRegistry`) builds one descriptor per
`PrimitiveBinding` constructor from the binding's own data, and
`IndexedPrimitives` derives the binding validity contract from it. The operand
count, the operand association, result inference, evaluation and lowering are
still per-constructor tables with catch-all arms; the later steps of #622 move
them here one table at a time, so a new constructor today still needs a case
in each of them.

The validity contract is a `Bool` that the checker runs together with the
`Prop` that the proofs use; the descriptor carries the proof that they agree,
so the two cannot drift apart. A descriptor grants no authority: the all-body
audits and the public acceptance path are unchanged. -/
namespace VastitasKernel.Indexed

structure PrimitiveDescriptor where
  /-- The binding contract as the proofs state it. -/
  validProp : Environment → Prop
  /-- The binding contract as the checker decides it. -/
  validBool : Environment → Bool
  /-- The two contracts agree; the registry entry proves it once. -/
  valid_iff : ∀ env, validBool env = true ↔ validProp env

/-- A descriptor whose contract is one executable check. -/
def PrimitiveDescriptor.ofBool (check : Environment → Bool) : PrimitiveDescriptor where
  validProp env := check env = true
  validBool := check
  valid_iff _ := Iff.rfl

end VastitasKernel.Indexed
