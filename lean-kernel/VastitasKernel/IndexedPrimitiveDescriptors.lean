import VastitasKernel.IndexedPrimitiveShapes
import VastitasKernel.IndexedPrimitiveValues

set_option autoImplicit false

/-! One checked descriptor per indexed primitive (#622).

A `PrimitiveDescriptor` holds what the kernel derives for one bound primitive.
The registry (`IndexedPrimitiveRegistry`) builds one descriptor per
`PrimitiveBinding` constructor from the binding's own data; `IndexedPrimitives`
derives the binding validity contract, the operand association, result
inference, the operand count and whether a call allocates from it,
`IndexedCore` the argument hints, `IndexedSourceDiagnostics` the role table
and `IndexedSemantics` the two evaluators. Lowering and the wire decoder are
still per-constructor tables; the later steps of #622 move them here, so a
new constructor today still needs a case in each of them.

The validity contract is a `Bool` that the checker runs together with the
`Prop` that the proofs use; the descriptor carries the proof that they agree,
so the two cannot drift apart. The association is a `Shape`, one datum for the
contract, the inference and the diagnostics. The evaluators take the operand
values the shape admits and return `none` on any other list: the logical one
builds the values of `IndexedPrimitiveValues`, the erased one the runtime
structures of generated programs. The oracle states their obligations once,
for any descriptor (`VastitasOracle.IndexedPrimitiveSoundness`). A descriptor
grants no authority: the all-body audits and the public acceptance path are
unchanged. -/
namespace VastitasKernel.Indexed
open VastitasKernel.Indexed.Core.Semantics (Value PrimitiveRuntimeValue)

structure PrimitiveDescriptor where
  /-- The operands, their agreements and the result type. -/
  shape : Shape
  /-- The binding contract as the proofs state it. -/
  validProp : Environment → Prop
  /-- The binding contract as the checker decides it. -/
  validBool : Environment → Bool
  /-- The two contracts agree; the registry entry proves it once. -/
  valid_iff : ∀ env, validBool env = true ↔ validProp env
  /-- The logical evaluator: the value of a call on operand values of the Core
  semantics, or `none` outside the shape. -/
  eval : Environment → List Value → Option Value
  /-- The erased evaluator: the same call on the runtime structures that
  generated programs link. -/
  evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue

/-- A descriptor whose contract is one executable check. -/
def PrimitiveDescriptor.ofBool (shape : Shape) (check : Environment → Bool)
    (eval : Environment → List Value → Option Value)
    (evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue) : PrimitiveDescriptor where
  shape := shape
  validProp env := check env = true
  validBool := check
  valid_iff _ := Iff.rfl
  eval := eval
  evalRuntime := evalRuntime

/-- The descriptor of an evidence binding: its contract is one executable
check, no call is well formed and none evaluates. -/
def PrimitiveDescriptor.evidence (check : Environment → Bool) : PrimitiveDescriptor :=
  .ofBool .uncallable check (fun _ _ => none) (fun _ => none)

end VastitasKernel.Indexed
