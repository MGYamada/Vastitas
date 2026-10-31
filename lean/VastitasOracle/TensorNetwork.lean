import VastitasOracle.StorageNumerical
import VastitasOracle.ResourceSource

/-! Acceptance and lowering for the actual two-map network compiler. These
are graph/typing/resource facts, not float field laws or native refinement. -/
namespace VastitasOracle.TensorNetwork
open VastitasKernel Storage Numerical Storage.TensorNetwork

theorem ports_used_once {env resources values graph output policy}
    (checked : Checked env resources values graph output policy)
    (port : Port) (member : port ∈ graph.ports) : graph.uses.count port = 1 := by
  have upper := List.nodup_iff_count.mp checked.wellFormed.2.2.1 port
  have lower := List.count_pos_iff.mpr (checked.wellFormed.2.2.2.2 port member)
  omega

theorem admitted_bilinear_edge {env resources values graph output policy}
    (checked : Checked env resources values graph output policy) :
    graph.edges = [checked.edge] ∧
    portType values graph checked.edge.dual = some ⟨checked.middle, .input⟩ ∧
    portType values graph checked.edge.primal = some ⟨checked.middle, .output⟩ :=
  ⟨checked.edgeFrom, checked.edgeTypes⟩

/-- The checked graph's middle is the inner coordinate basis of the actual
product, not a detached same-size edge certificate. -/
theorem edge_product_basis {env resources values graph output policy}
    (checked : Checked env resources values graph output policy) :
    checked.product.product.left.source = checked.middle ∧
    checked.product.product.right.target = checked.middle := by
  constructor
  · simpa [portType, checked.leftFrom, checked.product.leftFrom, checked.roles.1]
      using congrArg (Option.map PortType.basis) checked.edgeTypes.1
  · simpa [portType, checked.rightFrom, checked.product.rightFrom, checked.roles.2]
      using congrArg (Option.map PortType.basis) checked.edgeTypes.2

/-- Boundary direction and the destination's exact nominal bases are both
retained. Dimensions alone cannot discharge these equalities. -/
theorem output_boundary {env resources values graph output policy}
    (checked : Checked env resources values graph output policy) :
    graph.inputs = [⟨checked.right.name, .input⟩] ∧
    graph.outputs = [⟨checked.left.name, .output⟩] ∧
    checked.product.product.output.source = checked.product.product.right.source ∧
    checked.product.product.output.target = checked.product.product.left.target :=
  ⟨checked.boundaries.1, checked.boundaries.2, checked.product.composable.2⟩

/-- No conjugation is added by contraction. A transformed operand retains only
the flags admitted by the existing independent map-origin checker. -/
theorem no_implicit_conjugation {env resources values graph output policy}
    (checked : Checked env resources values graph output policy) :
    checked.request.conjugateLeft = checked.product.product.left.conjugate ∧
    checked.request.conjugateRight = checked.product.product.right.conjugate := ⟨rfl, rfl⟩

theorem same_input_plan {env resources values graph output policy}
    (first second : Checked env resources values graph output policy)
    (a : check env resources values graph output policy = .ok first)
    (b : check env resources values graph output policy = .ok second) :
    first.request = second.request := by
  have same : first = second := Except.ok.inj (a.symm.trans b)
  exact congrArg Checked.request same

/-- The exact accepted graph is connected to the exact emitted, independently
rechecked GEMM; occurrence ports never become additional storage owners. -/
theorem actual_lowering (receipt : Functions.NetworkReceipt) :
    check receipt.environment receipt.resources receipt.values receipt.graph receipt.output receipt.policy = .ok receipt.checked ∧
    receipt.priorCode ++ [.action (.gemm receipt.checked.request)] = receipt.code ∧
    checkAction receipt.resources (.gemm receipt.checked.request) = .ok receipt.after ∧
    checkGemm receipt.resources receipt.checked.request = .ok receipt.checked.product.storage :=
  ⟨receipt.accepted, receipt.emitted, receipt.transitioned, receipt.checked.product.storageAccepted⟩

theorem public_network_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NetworkReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.networks.toList) :
    receipt.environment = VastitasKernel.ResourceSource.numericalEnvironment input.checked.pureProgram ∧
    check receipt.environment receipt.resources receipt.values receipt.graph receipt.output receipt.policy = .ok receipt.checked ∧
    receipt.priorCode ++ [.action (.gemm receipt.checked.request)] = receipt.code :=
  ⟨(input.checked.execution entry found).networkOrigins receipt member, receipt.accepted, receipt.emitted⟩

end VastitasOracle.TensorNetwork
