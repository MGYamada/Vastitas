import VastitasOracle.TensorNumerical
import VastitasOracle.StorageDependencies

/-! Actual bounded regrouping and one-axis contraction certificates. Coordinate
references use the written multiplication and finite summation order. They do
not equate different parenthesizations or refine C/BLAS floating execution. -/
namespace VastitasOracle.TensorContraction
open VastitasKernel Storage Numerical Tensor

private theorem extent_cons (view : View) (axis : Nat) (axes : List Nat) :
    view.extent (axis :: axes) = view.dimension axis * view.extent axes := by
  simp only [View.extent, ← List.prod_eq_foldl, List.map_cons, List.prod_cons]

private theorem flatten_bound (view : View) (indices axes : List Nat)
    (bounded : ∀ axis ∈ axes, (indices[axis]?).getD 0 < view.dimension axis) :
    view.flatten indices axes < view.extent axes := by
  induction axes with
  | nil => simp [View.flatten, View.extent]
  | cons axis axes ih =>
    have first := bounded axis (by simp)
    have rest := ih (fun a ha => bounded a (by simp [ha]))
    have upper := Nat.mul_le_mul_left (view.dimension axis) (show view.flatten indices axes + 1 ≤ view.extent axes by omega)
    rw [extent_cons]
    simp only [View.flatten, List.foldr_cons] at *
    simp only [Nat.mul_add, Nat.mul_one] at upper
    omega

private theorem flatten_injective (view : View) (indices other axes : List Nat)
    (bounded : ∀ axis ∈ axes, (indices[axis]?).getD 0 < view.dimension axis)
    (otherBounded : ∀ axis ∈ axes, (other[axis]?).getD 0 < view.dimension axis)
    (same : view.flatten indices axes = view.flatten other axes) :
    ∀ axis ∈ axes, (indices[axis]?).getD 0 = (other[axis]?).getD 0 := by
  induction axes with
  | nil => simp
  | cons axis axes ih =>
    have first := bounded axis (by simp)
    have second := otherBounded axis (by simp)
    have equality := TensorNumerical.grouped_indices_injective first second (by simpa [View.flatten] using same)
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact equality.1
    · exact ih (fun b hb => bounded b (by simp [hb]))
        (fun b hb => otherBounded b (by simp [hb])) equality.2 a ha

/-- Every logical coordinate lies in the actual admitted loan rectangle, never
in its padding. The bound is on actual ordered axes, including zero extents. -/
theorem coordinate_in_bounds {view : View} {resources : State} (live : view.Live resources)
    (indices : List Nat)
    (bounded : ∀ axis ∈ view.grouping.order, (indices[axis]?).getD 0 < view.dimension axis) :
    view.loan.layout.InDomain (view.coordinate indices).1 (view.coordinate indices).2 := by
  have row := flatten_bound view indices (view.grouping.order.take view.grouping.split)
    (fun axis member => bounded axis (List.mem_of_mem_take member))
  have column := flatten_bound view indices (view.grouping.order.drop view.grouping.split)
    (fun axis member => bounded axis (List.mem_of_mem_drop member))
  simpa [View.coordinate, View.rows, View.columns, Layout.InDomain, Layout.logicalRows,
    Layout.logicalColumns, live.2.2.2.1, live.2.2.2.2.1, live.2.2.2.2.2] using And.intro row column

/-- Legal grouping cannot collapse two logical coordinates. Together with
bounds and raw-cell copying, this is the coordinate permutation obligation. -/
theorem coordinate_injective (view : View) (indices other : List Nat)
    (bounded : ∀ axis ∈ view.grouping.order, (indices[axis]?).getD 0 < view.dimension axis)
    (otherBounded : ∀ axis ∈ view.grouping.order, (other[axis]?).getD 0 < view.dimension axis)
    (same : view.coordinate indices = view.coordinate other) :
    ∀ axis ∈ view.grouping.order, (indices[axis]?).getD 0 = (other[axis]?).getD 0 := by
  have rows := flatten_injective view indices other (view.grouping.order.take view.grouping.split)
    (fun axis member => bounded axis (List.mem_of_mem_take member))
    (fun axis member => otherBounded axis (List.mem_of_mem_take member)) (congrArg Prod.fst same)
  have columns := flatten_injective view indices other (view.grouping.order.drop view.grouping.split)
    (fun axis member => bounded axis (List.mem_of_mem_drop member))
    (fun axis member => otherBounded axis (List.mem_of_mem_drop member)) (congrArg Prod.snd same)
  intro axis member
  rw [← List.take_append_drop view.grouping.split view.grouping.order] at member
  rcases List.mem_append.mp member with member | member
  · exact rows axis member
  · exact columns axis member

/-- The actual explicit regroup destination has identical nominal axes. Every
byte of its mapped cell belongs to its initialized physical footprint. -/
theorem regroup_cell_bytes {env numerical resources input output}
    (checked : CheckedRegroup env numerical resources input output) (indices : List Nat)
    (bounded : ∀ axis ∈ output.grouping.order, (indices[axis]?).getD 0 < output.dimension axis)
    (allocation : Allocation) (found : checked.after.allocation? output.loan.allocation = some allocation)
    {offset : Nat} (offsetBound : offset < allocation.scalar.width) :
    output.axes = input.axes ∧ StorageRegions.Initialized allocation.scalar
      (output.address allocation.scalar indices + offset) allocation.initialization := by
  refine ⟨checked.axes, ?_⟩
  have inside := StorageRegions.cell_bytes (coordinate_in_bounds checked.outputLive indices bounded) offsetBound
  have initialized : allocation.initialization.covers allocation.scalar output.loan.layout = true := by
    simpa [View.Initialized, found] using checked.outputInitialized
  exact StorageRegions.initialization_bytes initialized inside

/-- Generic and optimized regrouping both invalidate every dependency that
mentions the actual written allocation, even through a disjoint subregion. -/
theorem regroup_invalidates_dependencies {env numerical resources input output}
    (checked : CheckedRegroup env numerical resources input output)
    (name : Symbol) (dependency : Dependency)
    (mentioned : dependency.mentions output.loan.allocation = true) :
    ¬ StorageDependencies.LiveEntry checked.after name dependency := by
  rw [checked.written]
  exact StorageDependencies.written_kills mentioned

/-- Exact native mixed-radix descriptors use the dimensions of these actual
axes, not an independently invented grouped basis. -/
theorem raw_grouping_coordinate (view : View) (indices : List Nat) :
    view.grouping.coordinate view.dimensions indices = view.coordinate indices := by
  have dimension : ∀ axis, (view.dimensions[axis]?).getD 0 = view.dimension axis := by
    intro axis
    simp [View.dimensions, View.dimension, List.getElem?_map]
  simp [Grouping.coordinate, Grouping.flatten, View.coordinate, View.flatten, dimension]

private theorem rank_two_grouping (grouping : Grouping) (valid : grouping.Valid 2) :
    grouping = ⟨[0,1],1⟩ ∨ grouping = ⟨[1,0],1⟩ := by
  have length : grouping.order.length = 2 := by simpa using valid.1.length_eq
  obtain ⟨a, b, shape⟩ : ∃ a b, grouping.order = [a,b] :=
    ⟨grouping.order[0]'(by omega), grouping.order[1]'(by omega), List.eq_getElem_of_length_eq_two _ length⟩
  have ha : a < 2 := List.mem_range.mp (valid.1.mem_iff.mp (by simp [shape]))
  have hb : b < 2 := List.mem_range.mp (valid.1.mem_iff.mp (by simp [shape]))
  have different : a ≠ b := by
    have nodup := valid.1.nodup_iff.mpr (List.nodup_range (n := 2))
    simpa [shape] using nodup
  have split : grouping.split = 1 := by have := valid.2; omega
  have choices : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  rcases choices with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left; cases grouping; simp_all
  · right; cases grouping; simp_all

/-- Embedding a rank-two rectangle in the bounded native descriptor adds only
a unit physical extent. It preserves both exact logical coordinates and axes;
no third nominal basis is constructed or accepted. -/
theorem rank_two_native_embedding (view : View) (numerical : Numerical.Values)
    (valid : view.Valid numerical) (rank : view.axes.length = 2) (x y : Nat) :
    view.regroupGrouping.coordinate view.regroupDimensions [x,y,0] = view.coordinate [x,y] := by
  rcases view with ⟨axes, grouping, loan⟩
  have length : axes.length = 2 := rank
  obtain ⟨a, b, shape⟩ : ∃ a b, axes = [a,b] :=
    ⟨axes[0]'(by omega), axes[1]'(by omega), List.eq_getElem_of_length_eq_two _ length⟩
  subst axes
  have group := rank_two_grouping grouping valid.2.1
  rcases group with rfl | rfl <;>
    simp [View.regroupGrouping, View.regroupDimensions,
      Grouping.coordinate, Grouping.flatten, View.dimensions, View.coordinate,
      View.flatten, View.dimension]

theorem rank_three_native_embedding (view : View) (rank : view.axes.length = 3) (indices : List Nat) :
    view.regroupGrouping.coordinate view.regroupDimensions indices = view.coordinate indices := by
  simpa [View.regroupGrouping, View.regroupDimensions, rank] using raw_grouping_coordinate view indices

theorem selected_axes {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy) :
    ∃ a b : Basis, left.axes[la]? = some a ∧ right.axes[ra]? = some b ∧
      (DualPair a b ∨ DualPair b a) := by
  have selected := checked.selected
  unfold selectedPair at selected
  split at selected
  · rename_i a b leftFound rightFound
    exact ⟨a, b, leftFound, rightFound, selected⟩
  · contradiction

theorem selected_bounds {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy) :
    la < left.axes.length ∧ ra < right.axes.length := by
  obtain ⟨a, b, ha, hb, _⟩ := selected_axes checked
  exact ⟨(List.getElem?_eq_some_iff.mp ha).1, (List.getElem?_eq_some_iff.mp hb).1⟩

private theorem left_inner_group (rank axis : Nat) (ranks : rank = 2 ∨ rank = 3) (bound : axis < rank) :
    (leftGrouping rank axis).order.drop (leftGrouping rank axis).split = [axis] := by
  rcases ranks with rfl | rfl
  · have cases : axis = 0 ∨ axis = 1 := by omega
    rcases cases with rfl | rfl <;> decide
  · have cases : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide

/-- The actual checked GEMM takes exactly the selected logical extent. Written
left/right operands are not swapped when the primal leg is on the left. -/
theorem actual_single_operands {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy) :
    checked.storage.operands.left = left.loan ∧ checked.storage.operands.right = right.loan ∧
    checked.storage.operands.output = output.loan ∧
    checked.storage.operands.left.layout.logicalColumns = left.dimension la := by
  have valid := checked.storage.valid
  simp only [GemmOperands.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  have leftLive := checked.leftLive
  have rightLive := checked.rightLive
  have outputLive := checked.outputLive
  simp only [View.Live] at leftLive rightLive outputLive
  have foundLeft : checked.storage.operands.left = left.loan := by simp_all [contractionRequest]
  have foundRight : checked.storage.operands.right = right.loan := by simp_all [contractionRequest]
  have foundOutput : checked.storage.operands.output = output.loan := by simp_all [contractionRequest]
  refine ⟨foundLeft, foundRight, foundOutput, ?_⟩
  simp [foundLeft, Layout.logicalColumns, leftLive.2.2.2.1, leftLive.2.2.2.2.2,
    View.columns, checked.grouping.1, left_inner_group _ _ checked.leftValid.1 (selected_bounds checked).1,
    View.extent]

private theorem selected_left_coordinate (view : View) (axis : Nat) (indices : List Nat) (inner : Nat)
    (ranks : view.axes.length = 2 ∨ view.axes.length = 3) (bound : axis < view.axes.length)
    (length : indices.length = view.axes.length)
    (grouping : view.grouping = leftGrouping view.axes.length axis) :
    view.coordinate (indices.set axis inner) =
      (view.flatten indices (freeAxes view.axes.length axis), inner) := by
  rcases ranks with rank | rank
  · have shape := List.eq_getElem_of_length_eq_two indices (length.trans rank)
    rw [shape]
    have cases : axis = 0 ∨ axis = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp [View.coordinate, View.flatten, grouping, rank, leftGrouping, freeAxes, List.range_succ]
  · have shape := List.eq_getElem_of_length_eq_three indices (length.trans rank)
    rw [shape]
    have cases : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [View.coordinate, View.flatten, grouping, rank, leftGrouping, freeAxes, List.range_succ]

private theorem selected_right_coordinate (view : View) (axis : Nat) (indices : List Nat) (inner : Nat)
    (ranks : view.axes.length = 2 ∨ view.axes.length = 3) (bound : axis < view.axes.length)
    (length : indices.length = view.axes.length)
    (grouping : view.grouping = rightGrouping view.axes.length axis) :
    view.coordinate (indices.set axis inner) =
      (inner, view.flatten indices (freeAxes view.axes.length axis)) := by
  rcases ranks with rank | rank
  · have shape := List.eq_getElem_of_length_eq_two indices (length.trans rank)
    rw [shape]
    have cases : axis = 0 ∨ axis = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp [View.coordinate, View.flatten, grouping, rank, rightGrouping, freeAxes, List.range_succ]
  · have shape := List.eq_getElem_of_length_eq_three indices (length.trans rank)
    rw [shape]
    have cases : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
    rcases cases with rfl | rfl | rfl <;>
      simp [View.coordinate, View.flatten, grouping, rank, rightGrouping, freeAxes, List.range_succ]

/-- In each accepted rank-two/three orientation, substituting the selected
logical coordinate changes exactly the GEMM inner coordinate. All free axes
retain their written order. -/
theorem actual_selected_coordinates {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy)
    (leftIndices rightIndices : List Nat) (inner : Nat)
    (leftLength : leftIndices.length = left.axes.length)
    (rightLength : rightIndices.length = right.axes.length) :
    left.coordinate (leftIndices.set la inner) =
      (left.flatten leftIndices (freeAxes left.axes.length la), inner) ∧
    right.coordinate (rightIndices.set ra inner) =
      (inner, right.flatten rightIndices (freeAxes right.axes.length ra)) := by
  exact ⟨selected_left_coordinate left la leftIndices inner checked.leftValid.1
      (selected_bounds checked).1 leftLength checked.grouping.1,
    selected_right_coordinate right ra rightIndices inner checked.rightValid.1
      (selected_bounds checked).2 rightLength checked.grouping.2.1⟩

/-- A finite tensor-coordinate reference using actual loan-coordinate readers.
No commutativity or associativity assumptions appear in this statement. -/
def coordinateReference (zero : α) (add mul : α → α → α)
    (left right : View) (leftCells rightCells : Nat → Nat → α)
    (la ra : Nat) (leftIndices rightIndices : List Nat) : α :=
  (List.range (left.dimension la)).foldl (fun sum inner =>
    let l := left.coordinate (leftIndices.set la inner)
    let r := right.coordinate (rightIndices.set ra inner)
    add sum (mul (leftCells l.1 l.2) (rightCells r.1 r.2))) zero

theorem accepted_coordinate_reference {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy)
    (zero : α) (add mul : α → α → α) (leftCells rightCells : Nat → Nat → α)
    (leftIndices rightIndices : List Nat)
    (leftLength : leftIndices.length = left.axes.length)
    (rightLength : rightIndices.length = right.axes.length) :
    TensorNumerical.gemmReference zero add mul leftCells rightCells
      checked.storage.operands.left.layout.logicalColumns
      (left.flatten leftIndices (freeAxes left.axes.length la))
      (right.flatten rightIndices (freeAxes right.axes.length ra)) =
    coordinateReference zero add mul left right leftCells rightCells la ra leftIndices rightIndices := by
  have coordinates := actual_selected_coordinates checked leftIndices rightIndices
  simp only [TensorNumerical.gemmReference, coordinateReference,
    (actual_single_operands checked).2.2.2,
    fun inner => (coordinates inner leftLength rightLength).1,
    fun inner => (coordinates inner leftLength rightLength).2]

/-- A coordinate contraction reference is precisely the finite fold of the
actual matrix operands and actual selected inner extent; there are no field
assumptions or exchanges of the written multiplication order. -/
def singleReference (zero : α) (add mul : α → α → α) (left right : Nat → Nat → α)
    (view : View) (axis row column : Nat) : α :=
  (List.range (view.dimension axis)).foldl (fun sum k => add sum (mul (left row k) (right k column))) zero

theorem actual_single_reference {env numerical resources left right output la ra policy}
    (checked : CheckedSingle env numerical resources left right output la ra policy)
    (zero : α) (add mul : α → α → α) (leftCells rightCells : Nat → Nat → α) (row column : Nat) :
    TensorNumerical.gemmReference zero add mul leftCells rightCells
      checked.storage.operands.left.layout.logicalColumns row column =
    singleReference zero add mul leftCells rightCells left la row column := by
  rw [(actual_single_operands checked).2.2.2]
  rfl

end VastitasOracle.TensorContraction
