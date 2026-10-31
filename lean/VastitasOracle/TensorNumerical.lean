import VastitasOracle.StorageGemm
import VastitasKernel.ResourceProtocol

/-! Actual coordinate grouping, packing receipts and fixed-axis contraction.
The finite reference theorem preserves summation order and assumes no field
laws. It is not a proof of floating arithmetic or C/BLAS native refinement. -/
namespace VastitasOracle.TensorNumerical
open VastitasKernel Storage Numerical Tensor

private theorem mixed_bound {x y a b : Nat} (hx : x < a) (hy : y < b) : x + a * y < a * b := by
  have upper := Nat.mul_le_mul_left a (show y + 1 ≤ b by omega)
  simp only [Nat.mul_add, Nat.mul_one] at upper
  omega

theorem grouped_indices_injective {x y x' y' extent : Nat}
    (xBound : x < extent) (xBound' : x' < extent)
    (same : x + extent * y = x' + extent * y') : x = x' ∧ y = y' := by
  have first := congrArg (· % extent) same
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt xBound, Nat.mod_eq_of_lt xBound'] at first
  have second : extent * y = extent * y' := by omega
  exact ⟨first, Nat.mul_left_cancel (by omega) second⟩

theorem packing_coordinates {env numerical resources values source target}
    (checked : CheckedPack env numerical resources values source target) (x z y : Nat) :
    checked.input.coordinate [x, z, y] = (x, z + checked.input.dimension 1 * y) ∧
    checked.output.coordinate [x, z, y] = (x + checked.input.dimension 0 * y, z) := by
  constructor
  · simp [View.coordinate, View.flatten, checked.grouping.1, unpacked]
  · have same : checked.output.dimension 0 = checked.input.dimension 0 := by
      simp [View.dimension, checked.axes]
    simp [View.coordinate, View.flatten, checked.grouping.2, packed, same]

/-- Both coordinates are cells of the actual accepted rectangular loan. No
padding byte is an axis coordinate, and no dimension identifies two bases. -/
theorem packing_coordinates_in_bounds {env numerical resources values source target}
    (checked : CheckedPack env numerical resources values source target) {x z y : Nat}
    (hx : x < checked.input.dimension 0) (hz : z < checked.input.dimension 1)
    (hy : y < checked.input.dimension 2) :
    checked.input.loan.layout.InDomain x (z + checked.input.dimension 1 * y) ∧
    checked.output.loan.layout.InDomain (x + checked.input.dimension 0 * y) z := by
  have input := checked.inputLive.2.2.2.2
  have output := checked.outputLive.2.2.2.2
  simp [View.rows, View.columns, View.extent, checked.grouping.1, unpacked] at input
  simp [View.rows, View.columns, View.extent, checked.grouping.2, packed,
    View.dimension, checked.axes] at output
  constructor
  · simpa [Layout.InDomain, Layout.logicalRows, Layout.logicalColumns,
      checked.inputLive.2.2.2.1, input.1, input.2] using And.intro hx (mixed_bound hz hy)
  · change checked.output.loan.layout.InDomain (x + checked.input.dimension 0 * y) z
    have rows : checked.output.loan.layout.rows = checked.input.dimension 0 * checked.input.dimension 2 := output.1
    have columns : checked.output.loan.layout.columns = checked.input.dimension 1 := output.2
    simpa [Layout.InDomain, Layout.logicalRows, Layout.logicalColumns,
      checked.outputLive.2.2.2.1, rows, columns] using And.intro (mixed_bound hx hy) hz

theorem packing_initializes_actual_bytes {env numerical resources values source target}
    (checked : CheckedPack env numerical resources values source target) (allocation : Allocation)
    (found : checked.after.allocation? checked.output.loan.allocation = some allocation)
    {byte : Nat} (inside : StorageRegions.ContainsByte checked.output.loan.layout allocation.scalar byte) :
    StorageRegions.Initialized allocation.scalar byte allocation.initialization := by
  have initialized : allocation.initialization.covers allocation.scalar checked.output.loan.layout = true := by
    simpa [View.Initialized, found] using checked.outputInitialized
  exact StorageRegions.initialization_bytes initialized inside

/-- The packing coordinate reference follows the exact native descriptor's
row grouping. The accepted coordinate theorem above relates it to actual loans. -/
def packedReference (input : Nat → Nat → Nat → α) (extent row column : Nat) : α :=
  input (row % extent) column (row / extent)

theorem packed_reference_coordinate (input : Nat → Nat → Nat → α) {extent x : Nat}
    (bound : x < extent) (z y : Nat) :
    packedReference input extent (x + extent * y) z = input x z y := by
  simp [packedReference, Nat.add_mul_div_left _ _ (show 0 < extent by omega),
    Nat.div_eq_of_lt bound, Nat.add_mod, Nat.mod_eq_of_lt bound]

/-- These are the actual five ordered input axes and three output axes. The
contracted leg carries the corresponding dual origin of the actual right basis. -/
theorem contraction_nominal_axes {env numerical resources values leftName rightName outputName policy}
    (checked : CheckedContraction env numerical resources values leftName rightName outputName policy) :
    ∃ a d b v c : Basis, checked.left.axes = [a, d, b] ∧ checked.right.axes = [v, c] ∧
      checked.output.axes = [a, b, c] ∧ d.parent = some v.brand ∧ d.space.origin = .dual v.space.brand := by
  have axes := checked.axes
  unfold ContractionAxes at axes
  split at axes
  · rename_i a d b v c left right
    exact ⟨a, d, b, v, c, left, right, axes.1, axes.2⟩
  · contradiction

/-- Actual accepted groupings place precisely the corresponding tensor
coordinates at the GEMM row/inner/column coordinates. -/
theorem contraction_matrix_coordinates {env numerical resources values leftName rightName outputName policy}
    (checked : CheckedContraction env numerical resources values leftName rightName outputName policy)
    (x z y column : Nat) :
    checked.left.coordinate [x, z, y] = (x + checked.left.dimension 0 * y, z) ∧
    checked.right.coordinate [z, column] = (z, column) ∧
    checked.output.coordinate [x, y, column] = (x + checked.left.dimension 0 * y, column) := by
  obtain ⟨a, d, b, v, c, left, right, output, _⟩ := contraction_nominal_axes checked
  have outer : checked.output.dimension 0 = checked.left.dimension 0 := by simp [View.dimension, left, output]
  simp [View.coordinate, View.flatten, checked.grouping.1, checked.grouping.2.1,
    checked.grouping.2.2, packed, matrix, boundary, outer]

/-- The raw GEMM receives these exact tensor loans. In particular its actual
inner extent is the selected axis, not an independently chosen reference size. -/
theorem contraction_gemm_operands {env numerical resources values leftName rightName outputName policy}
    (checked : CheckedContraction env numerical resources values leftName rightName outputName policy) :
    checked.storage.operands.left = checked.left.loan ∧
    checked.storage.operands.right = checked.right.loan ∧
    checked.storage.operands.output = checked.output.loan ∧
    checked.storage.operands.left.layout.logicalRows = checked.left.dimension 0 * checked.left.dimension 2 ∧
    checked.storage.operands.left.layout.logicalColumns = checked.left.dimension 1 := by
  have valid := checked.storage.valid
  simp only [GemmOperands.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  have leftLive := checked.leftLive
  have rightLive := checked.rightLive
  have outputLive := checked.outputLive
  simp only [View.Live] at leftLive rightLive outputLive
  have foundLeft : checked.storage.operands.left = checked.left.loan := by
    simp_all [contractionRequest]
  have foundRight : checked.storage.operands.right = checked.right.loan := by
    simp_all [contractionRequest]
  have foundOutput : checked.storage.operands.output = checked.output.loan := by
    simp_all [contractionRequest]
  refine ⟨foundLeft, foundRight, foundOutput, ?_, ?_⟩ <;>
    simp [foundLeft, Layout.logicalRows, Layout.logicalColumns, leftLive.2.2.2.1,
      leftLive.2.2.2.2.1, leftLive.2.2.2.2.2, View.rows, View.columns, View.extent,
      checked.grouping.1, packed]

/-- A finite left fold fixes exactly the same summation order on both sides.
No associativity, exact float field law, or contraction-order rewrite is used. -/
def contractionReference (zero : α) (add mul : α → α → α)
    (left : Nat → Nat → Nat → α) (right : Nat → Nat → α) (count x y column : Nat) : α :=
  (List.range count).foldl (fun sum k => add sum (mul (left x k y) (right k column))) zero

def gemmReference (zero : α) (add mul : α → α → α)
    (left right : Nat → Nat → α) (count row column : Nat) : α :=
  (List.range count).foldl (fun sum k => add sum (mul (left row k) (right k column))) zero

/-- The dimensions come from the actual accepted tensor axes; the result is the
ordered [left[0], left[2], right[1]] boundary, not a fabricated product basis. -/
theorem accepted_contraction_coordinates {env numerical resources values leftName rightName outputName policy}
    (checked : CheckedContraction env numerical resources values leftName rightName outputName policy)
    (zero : α) (add mul : α → α → α) (left : Nat → Nat → Nat → α) (right : Nat → Nat → α)
    {x : Nat} (xBound : x < checked.left.dimension 0) (y column : Nat) :
    gemmReference zero add mul (packedReference left (checked.left.dimension 0)) right
        checked.storage.operands.left.layout.logicalColumns (x + checked.left.dimension 0 * y) column =
      contractionReference zero add mul left right (checked.left.dimension 1) x y column := by
  simp [(contraction_gemm_operands checked).2.2.2.2,
    gemmReference, contractionReference, packed_reference_coordinate left xBound]

theorem actual_packing (receipt : Functions.TensorPackReceipt) :
    Tensor.checkPack receipt.environment receipt.numerical receipt.resources receipt.values receipt.source receipt.target = .ok receipt.checked ∧
    checkAction receipt.resources (packAction receipt.checked.input receipt.checked.output) = .ok receipt.after ∧
    receipt.priorCode ++ [.action (packAction receipt.checked.input receipt.checked.output)] = receipt.code :=
  ⟨receipt.accepted, receipt.transitioned ▸ receipt.checked.accepted, receipt.emitted⟩

theorem actual_contraction (receipt : Functions.TensorContractionReceipt) :
    Tensor.checkContraction receipt.environment receipt.numerical receipt.resources receipt.values
      receipt.left receipt.right receipt.output receipt.policy = .ok receipt.checked ∧
    checkAction receipt.resources (.gemm (contractionRequest receipt.checked.left receipt.checked.right receipt.checked.output receipt.policy)) = .ok receipt.after ∧
    receipt.priorCode ++ [.action (.gemm (contractionRequest receipt.checked.left receipt.checked.right receipt.checked.output receipt.policy))] = receipt.code :=
  ⟨receipt.accepted, receipt.transitioned ▸ receipt.checked.accepted, receipt.emitted⟩

theorem public_tensor_view_origin {json : Lean.Json}
    (input : ResourceSource.Wire.CheckedInput json requireMain) (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TensorViewReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.tensorViews.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram ∧
    Tensor.lookup receipt.values receipt.name = some receipt.checked.view :=
  ⟨(input.checked.execution entry found).tensorViewOrigins receipt member, receipt.bound⟩

theorem public_tensor_packing_origin {json : Lean.Json}
    (input : ResourceSource.Wire.CheckedInput json requireMain) (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TensorPackReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.tensorPacks.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram :=
  (input.checked.execution entry found).tensorPackOrigins receipt member

theorem public_tensor_contraction_origin {json : Lean.Json}
    (input : ResourceSource.Wire.CheckedInput json requireMain) (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TensorContractionReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.tensorContractions.toList) :
    receipt.environment = ResourceSource.numericalEnvironment input.checked.pureProgram :=
  (input.checked.execution entry found).tensorContractionOrigins receipt member

end VastitasOracle.TensorNumerical
