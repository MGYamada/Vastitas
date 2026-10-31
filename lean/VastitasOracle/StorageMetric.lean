import VastitasKernel.ResourceProtocol

/-! Structural and representation guarantees of the actual diagonal metric
checkers. Ideal field/involution laws are separate, as is native refinement. -/
namespace VastitasOracle.StorageMetric
open VastitasKernel Storage Numerical

theorem realized_coefficients {metric : Metric} (realized : RealizedMetric metric) :
    realized.diagonal.valid metric.basis.space.dimension = true :=
  by
    have exact := realized.exact
    simp only [Gram.realizes, Bool.and_eq_true] at exact
    exact exact.1

theorem actual_adjoint (receipt : Functions.AdjointIntoReceipt) :
    checkAdjointInto receipt.environment receipt.resources receipt.values receipt.input receipt.output
      receipt.source receipt.target receipt.policy = .ok receipt.checked := receipt.accepted

theorem adjoint_uses_declared_forms {env resources values input output source target policy}
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    value? values source = some (.metric checked.source) ∧
    value? values target = some (.metric checked.target) ∧
    checked.source.basis = checked.input.source ∧ checked.target.basis = checked.input.target ∧
    checked.source.involution = checked.target.involution :=
  ⟨checked.sourceFrom, checked.targetFrom, checked.forms⟩

theorem adjoint_exact_realization {env resources values input output source target policy}
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    checked.source.gram.realizes checked.source.basis.space.dimension checked.sourceRealization.diagonal = true ∧
    checked.target.gram.realizes checked.target.basis.space.dimension checked.targetRealization.diagonal = true :=
  ⟨checked.sourceRealization.exact, checked.targetRealization.exact⟩

theorem adjoint_destination {env resources values input output source target policy}
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    checked.output.source = checked.input.target ∧ checked.output.target = checked.input.source ∧
    checked.output.conjugate = false := checked.endpoints

theorem adjoint_transition {env resources values input output source target policy}
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    checkAction resources (.diagonalAdjoint (adjointIntoRequest checked.input checked.output
      checked.sourceRealization.diagonal checked.targetRealization.diagonal policy)) = .ok checked.after :=
  checked.accepted

theorem adjoint_preserves_loans {env resources values input output source target policy}
    (checked : CheckedAdjointInto env resources values input output source target policy) :
    checked.input.Live checked.after ∧ checked.output.Live checked.after ∧
    (checked.after.allocation? checked.output.loan.allocation).any
      (fun allocation => allocation.initialization.covers allocation.scalar checked.output.loan.layout) = true :=
  ⟨checked.inputRestored, checked.outputRestored, checked.initialized⟩

theorem adjoint_flags (input output : MapView) (source target : Diagonal) (policy : NumericalPolicy) :
    (adjointIntoRequest input output source target policy).conjugate = !input.conjugate := rfl

theorem adjoint_exact_emission (receipt : Functions.AdjointIntoReceipt) :
    receipt.priorCode ++ [.action (.diagonalAdjoint (adjointIntoRequest receipt.checked.input receipt.checked.output
      receipt.checked.sourceRealization.diagonal receipt.checked.targetRealization.diagonal receipt.policy))] = receipt.code :=
  receipt.emitted

theorem actual_pairing (receipt : Functions.DiagonalPairingReceipt) :
    checkDiagonalPairing receipt.environment receipt.resources receipt.values receipt.left receipt.right
      receipt.output receipt.metric receipt.scratch receipt.writeLoan receipt.readLoan receipt.leftChild
      receipt.layout receipt.policy = .ok receipt.checked := receipt.accepted

theorem pairing_uses_declared_form {env resources values left right output metric scratch writeLoan readLoan child layout policy}
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch writeLoan readLoan child layout policy) :
    value? values metric = some (.metric checked.metric) ∧ checked.metric.basis = checked.right.basis ∧
    checked.left.basis.parent = some checked.right.basis.brand ∧
    checked.left.basis.space.origin = .conjugate checked.right.basis.space.brand checked.metric.selected :=
  ⟨checked.metricFrom, checked.form⟩

theorem pairing_exact_realization {env resources values left right output metric scratch writeLoan readLoan child layout policy}
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch writeLoan readLoan child layout policy) :
    checked.metric.gram.realizes checked.metric.basis.space.dimension checked.realization.diagonal = true :=
  checked.realization.exact

/-- This is an actual accepted eight-step resource execution, not permission
inferred from a later initialized flag. Write release precedes the fresh read. -/
theorem pairing_scratch_replay {env resources values left right output metric scratch writeLoan readLoan child layout policy}
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch writeLoan readLoan child layout policy) :
    run 4096 resources (diagonalPairCode checked.left checked.right
      (diagonalPairRequest checked.left checked.right output scratch writeLoan readLoan child layout
        checked.realization.diagonal policy)) = .ok checked.after := checked.replayed

theorem pairing_returns_resources {env resources values left right output metric scratch writeLoan readLoan child layout policy}
    (checked : CheckedDiagonalPairing env resources values left right output metric scratch writeLoan readLoan child layout policy) :
    checked.after.loans = resources.loans ∧
    (checked.after.allocations.map fun allocation => (allocation.owner, allocation.identity)) =
      (resources.allocations.map fun allocation => (allocation.owner, allocation.identity)) ∧
    scalarOutputReady checked.after output checked.right.basis.space.scalar = true :=
  ⟨checked.loansRestored, checked.ownersRestored, checked.initialized⟩

theorem pairing_exact_emission (receipt : Functions.DiagonalPairingReceipt) :
    receipt.priorCode ++ [.action (.diagonalPair (diagonalPairRequest receipt.checked.left receipt.checked.right
      receipt.output receipt.scratch receipt.writeLoan receipt.readLoan receipt.leftChild receipt.layout
      receipt.checked.realization.diagonal receipt.policy))] = receipt.code := receipt.emitted

theorem public_adjoint_origins {functions entry environment}
    (execution : ResourceSource.Execution functions entry environment)
    (receipt : Functions.AdjointIntoReceipt) (member : receipt ∈ execution.checked.context.adjoints.toList) :
    receipt.environment = environment := execution.adjointOrigins receipt member

theorem public_pairing_origins {functions entry environment}
    (execution : ResourceSource.Execution functions entry environment)
    (receipt : Functions.DiagonalPairingReceipt) (member : receipt ∈ execution.checked.context.diagonalPairings.toList) :
    receipt.environment = environment := execution.diagonalPairingOrigins receipt member

end VastitasOracle.StorageMetric
