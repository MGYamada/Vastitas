import VastitasOracle.TensorContraction

/-! Proofs about actual returned contraction-tree receipts, including a
reconstructed connected producer tree. No graph search, categorical rewrite,
float reassociation, or native refinement is assumed or claimed. -/
namespace VastitasOracle.TensorTree
open VastitasKernel Storage Numerical TensorTree

theorem ports_used_once {env numerical resources values graph output plan}
    (checked : Checked env numerical resources values graph output plan) :
    graph.uses.Nodup ∧ graph.uses.Perm (graph.ports values) :=
  ⟨checked.initial.graphValid.2.2.2.1, checked.initial.graphValid.2.2.2.2.1⟩

theorem every_edge_has_actual_dual_origin {env numerical resources values graph output plan}
    (checked : Checked env numerical resources values graph output plan) (edge : Edge) (member : edge ∈ graph.edges) :
    ∃ dual primal : Basis, graph.portBasis values edge.dual = some dual ∧
      graph.portBasis values edge.primal = some primal ∧
      dual.parent = some primal.brand ∧ dual.space.origin = .dual primal.space.brand := by
  have typed := (checked.initial.graphValid.2.2.2.2.2.1 edge member).1
  unfold Graph.edgeTyped at typed
  split at typed
  · rename_i dual primal hd hp
    exact ⟨dual, primal, hd, hp, typed⟩
  · contradiction

/-- This is stronger than edge counts and port coverage: the returned binary
producer tree covers every occurrence and declared edge exactly once, and each
internal node joins disjoint leaf sets through its actual declared edge. -/
theorem reconstructed_connected_tree {env numerical resources values graph output plan}
    (checked : Checked env numerical resources values graph output plan) :
    checked.result.producer.Valid graph ∧
    checked.result.producer.leaves.Perm (graph.occurrences.map (·.name)) ∧
    checked.result.producer.edges.Perm (graph.edges.map (·.name)) := by
  obtain ⟨_, _, _, partition, _, _, _, origins, edges⟩ := checked.valid
  have member : checked.result ∈ checked.finalState.components := by simp [checked.soleResult]
  have result := origins checked.result member
  have leaves : checked.result.members = checked.result.producer.leaves := result.2.2.1
  refine ⟨result.2.2.2, ?_, ?_⟩
  · simpa [checked.soleResult, leaves] using partition
  · have produced : checked.result.producer.edges.Perm checked.finalState.consumed := by
      simpa [checked.soleResult] using edges
    exact produced.trans checked.complete

/-- The ordered boundary consists of the original port bases, not merely
basis dimensions or a fabricated product-space identity. -/
theorem ordered_boundary_basis {env numerical resources values graph output plan}
    (checked : Checked env numerical resources values graph output plan) :
    graph.boundary.map (graph.portBasis values) = checked.output.axes.map some := by
  obtain ⟨_, _, _, _, _, _, _, origins, _⟩ := checked.valid
  have member : checked.result ∈ checked.finalState.components := by simp [checked.soleResult]
  simpa [checked.boundary, checked.outputExact] using (origins checked.result member).1

theorem exact_submitted_order {env numerical resources values graph output plan}
    (checked : Checked env numerical resources values graph output plan) :
    checked.receipts.map (·.event) = plan ∧
    replay env numerical graph values 1024 checked.initial.runtime plan = .ok (checked.finalState, checked.receipts) :=
  ⟨checked.eventCoverage, checked.executed⟩

/-- Every receipt refers to the same actual before/after event check and exact
resource replay, including explicit borrow/release transitions. -/
theorem actual_event {env numerical graph original}
    (receipt : StepReceipt env numerical graph original) :
    executeEvent env numerical graph receipt.before receipt.event = .ok ⟨receipt.after, receipt.operation⟩ ∧
    run 4096 receipt.before.resources (receipt.actions.map Storage.Statement.action) = .ok receipt.after.resources ∧
    receipt.before.code ++ receipt.actions = receipt.after.code :=
  ⟨receipt.accepted, receipt.replayed, receipt.emitted⟩

/-- A retained regroup witness names the actual checked nominal axes, action,
and resulting state, not a separately constructed coordinate certificate. -/
theorem actual_regroup {env numerical graph original}
    (receipt : StepReceipt env numerical graph original) (input output : Tensor.View)
    (checked : Tensor.CheckedRegroup env numerical receipt.before.resources input output)
    (accepted : Tensor.checkRegroup env numerical receipt.before.resources input output = .ok checked)
    (operation : receipt.operation = .regroup input output checked accepted) :
    output.axes = input.axes ∧
    checkAction receipt.before.resources (Tensor.regroupAction input output) = .ok receipt.after.resources := by
  have after := receipt.operationAfter
  rw [operation] at after
  exact ⟨checked.axes, after.symm ▸ checked.accepted⟩

/-- The selected one-axis contraction retained by an actual tree step emits
that exact GEMM and preserves the written left/right operand ordering. -/
theorem actual_contraction {env numerical graph original}
    (receipt : StepReceipt env numerical graph original) (left right output : Tensor.View) (la ra : Nat)
    (checked : Tensor.CheckedSingle env numerical receipt.before.resources left right output la ra .nativeFast)
    (accepted : Tensor.checkSingle env numerical receipt.before.resources left right output la ra .nativeFast = .ok checked)
    (operation : receipt.operation = .contraction left right output la ra checked accepted) :
    output.axes = Tensor.resultAxes left right la ra ∧
    checked.storage.operands.left = left.loan ∧ checked.storage.operands.right = right.loan ∧
    checkAction receipt.before.resources (.gemm (Tensor.contractionRequest left right output .nativeFast)) = .ok receipt.after.resources := by
  have after := receipt.operationAfter
  rw [operation] at after
  have operands := TensorContraction.actual_single_operands checked
  exact ⟨checked.axes, operands.1, operands.2.1, after.symm ▸ checked.accepted⟩

theorem actual_tree_lowering (receipt : Functions.TreeReceipt) :
    TensorTree.check receipt.environment receipt.numerical receipt.resources receipt.values receipt.graph receipt.output receipt.plan = .ok receipt.checked ∧
    run 4096 receipt.resources (receipt.checked.finalState.code.map Storage.Statement.action) = .ok receipt.after ∧
    receipt.priorCode ++ receipt.checked.finalState.code.map Storage.Statement.action = receipt.code ∧
    receipt.after.loans = receipt.resources.loans := by
  exact ⟨receipt.accepted, receipt.transitioned.symm ▸ receipt.checked.resourceReplay,
    receipt.emitted, receipt.transitioned.symm ▸ receipt.checked.restoredLoans⟩

theorem public_tree_origin {json : Lean.Json}
    (input : ResourceSource.Wire.CheckedInput json requireMain) (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TreeReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.trees.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram :=
  (input.checked.execution entry found).treeOrigins receipt member

end VastitasOracle.TensorTree
