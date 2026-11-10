import VastitasOracle.StorageLayout

/-! Actual-byte semantics for the resource checker's canonical rectangles.
These are properties of the exact containment and initialization algorithms;
allocator liveness and native execution correspondence are separate obligations. -/
namespace VastitasOracle.StorageRegions
open VastitasKernel.Storage StorageLayout

/-- A physical column contains its rows, but none of its trailing padding. -/
def ContainsByte (layout : Layout) (scalar : Scalar) (byte : Nat) : Prop :=
  ∃ column, column < layout.columns ∧
    layout.offset + column * (layout.leading * scalar.width) ≤ byte ∧
    byte < layout.offset + column * (layout.leading * scalar.width) + layout.rows * scalar.width

theorem contains_nonempty {layout : Layout} {scalar : Scalar} {byte : Nat}
    (inside : ContainsByte layout scalar byte) : layout.empty = false := by
  obtain ⟨column, hc, lo, hi⟩ := inside
  have rows : layout.rows ≠ 0 := by intro zero; simp [zero] at hi; omega
  simp only [Layout.empty, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem endByte_nonempty {layout : Layout} (scalar : Scalar) (nonempty : layout.empty = false) :
    layout.endByte scalar = layout.offset + (layout.columns - 1) * (layout.leading * scalar.width) +
      layout.rows * scalar.width := by
  have rows : layout.rows - 1 + 1 = layout.rows := by
    simp only [Layout.empty, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at nonempty
    omega
  simp only [Layout.endByte, nonempty, Bool.false_eq_true, ↓reduceIte]
  calc
    _ = layout.offset + (layout.columns - 1) * (layout.leading * scalar.width) +
      (layout.rows - 1 + 1) * scalar.width := by simp only [Nat.add_mul, Nat.one_mul]; omega
    _ = _ := by rw [rows]

theorem byte_bounds {layout : Layout} {scalar : Scalar} {byte : Nat}
    (inside : ContainsByte layout scalar byte) : layout.offset ≤ byte ∧ byte < layout.endByte scalar := by
  have finish := endByte_nonempty scalar (contains_nonempty inside)
  obtain ⟨column, hc, lo, hi⟩ := inside
  have order := Nat.mul_le_mul_right (layout.leading * scalar.width)
    (show column ≤ layout.columns - 1 by omega)
  omega

/-- Every byte of every admitted logical element is in the physical footprint,
including transposed views. -/
theorem cell_bytes {layout : Layout} {scalar : Scalar} {row column offset : Nat}
    (inside : layout.InDomain row column) (offsetBound : offset < scalar.width) :
    ContainsByte layout scalar (layout.address scalar row column + offset) := by
  obtain ⟨hr, hc⟩ := physical_indices inside
  refine ⟨layout.physicalColumn row column, hc, ?_, ?_⟩
  · simp only [Layout.address]; omega
  · have bound := Nat.mul_le_mul_right scalar.width (show layout.physicalRow row column + 1 ≤ layout.rows by omega)
    simp only [Nat.add_mul, Nat.one_mul] at bound
    simp only [Layout.address]
    omega

theorem contiguous_bytes {layout : Layout} {scalar : Scalar} {byte : Nat}
    (contiguous : layout.contiguous = true) (nonempty : layout.empty = false)
    (lo : layout.offset ≤ byte) (hi : byte < layout.endByte scalar) : ContainsByte layout scalar byte := by
  have finish := endByte_nonempty scalar nonempty
  have positive : 0 < layout.rows ∧ 0 < layout.columns := by
    simp only [Layout.empty, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at nonempty
    omega
  simp only [Layout.contiguous, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at contiguous
  rcases contiguous with one | dense
  · have columns : layout.columns = 1 := by omega
    refine ⟨0, by omega, by simpa using lo, ?_⟩
    simpa [finish, columns] using hi
  · let stride := layout.leading * scalar.width
    have width : 0 < scalar.width := by cases scalar <;> decide
    have stridePos : 0 < stride := by dsimp [stride]; rw [dense]; exact Nat.mul_pos positive.1 width
    have total : layout.endByte scalar = layout.offset + layout.columns * stride := by
      rw [finish, dense]
      have columns : layout.columns - 1 + 1 = layout.columns := by omega
      dsimp [stride]
      rw [dense]
      calc
        _ = layout.offset + (layout.columns - 1 + 1) * (layout.rows * scalar.width) := by
          simp only [Nat.add_mul, Nat.one_mul]; omega
        _ = _ := by rw [columns]
    have differenceBound : byte - layout.offset < layout.columns * stride := by omega
    refine ⟨(byte - layout.offset) / stride, (Nat.div_lt_iff_lt_mul stridePos).2 differenceBound, ?_, ?_⟩
    · have lower := Nat.div_mul_le_self (byte - layout.offset) stride
      change layout.offset + (byte - layout.offset) / stride * stride ≤ byte
      omega
    · have remainder := Nat.mod_lt (byte - layout.offset) stridePos
      have split := Nat.mod_add_div' (byte - layout.offset) stride
      change byte < layout.offset + (byte - layout.offset) / stride * stride + layout.rows * scalar.width
      have same : layout.rows * scalar.width = stride := by dsimp [stride]; rw [dense]
      rw [same]
      omega

/-- Accepted containment implies inclusion of actual byte footprints, not just
the envelope. In particular an initialized padded rectangle does not initialize
the gaps between its physical columns. -/
theorem covers_bytes {outer inner : Layout} {scalar : Scalar}
    (covered : outer.covers inner scalar = true) {byte : Nat}
    (inside : ContainsByte inner scalar byte) : ContainsByte outer scalar byte := by
  have nonempty := contains_nonempty inside
  simp only [Layout.covers, nonempty, Bool.false_eq_true, ↓reduceIte] at covered
  split at covered
  · contradiction
  next nonemptyOuter =>
    have outerNonempty : outer.empty = false := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at nonemptyOuter
      exact Bool.eq_false_iff.mpr nonemptyOuter.1
    have offsets : outer.offset ≤ inner.offset := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at nonemptyOuter
      omega
    split at covered <;> try contradiction
    split at covered
    next contiguous =>
      have bounds := byte_bounds inside
      exact contiguous_bytes contiguous outerNonempty (by omega) (by simpa using Nat.lt_of_lt_of_le bounds.2 (of_decide_eq_true covered))
    next padded =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at covered
      rcases covered with ⟨⟨⟨shape, aligned⟩, rows⟩, columns⟩
      obtain ⟨column, hc, lo, hi⟩ := inside
      let difference := inner.offset - outer.offset
      let stride := outer.leading * scalar.width
      have offsetSplit : outer.offset + difference = inner.offset := by dsimp [difference]; omega
      have division := Nat.mod_add_div' difference stride
      have remainderAligned : difference % stride % scalar.width = 0 := by
        simpa [stride, Nat.mod_mul_left_mod] using aligned
      have rowDivision := Nat.mod_add_div' (difference % stride) scalar.width
      have remainder : difference % stride / scalar.width * scalar.width = difference % stride := by omega
      have rowBytes := Nat.mul_le_mul_right scalar.width rows
      simp only [Nat.add_mul] at rowBytes
      have sameStride : column * (inner.leading * scalar.width) = column * stride := by
        rcases shape with one | same
        · have zero : column = 0 := by omega
          simp [zero]
        · simp [stride, same]
      refine ⟨difference / stride + column, by dsimp [difference, stride]; omega, ?_, ?_⟩
      · change outer.offset + (difference / stride + column) * stride ≤ byte
        rw [Nat.add_mul]
        rw [sameStride] at lo
        omega
      · change byte < outer.offset + (difference / stride + column) * stride + outer.rows * scalar.width
        rw [Nat.add_mul]
        rw [sameStride] at hi
        change difference % stride / scalar.width * scalar.width + inner.rows * scalar.width ≤ outer.rows * scalar.width at rowBytes
        rw [remainder] at rowBytes
        omega

theorem disjoint_bytes {left right : Layout} {scalar : Scalar}
    (separate : left.disjoint right scalar = true) {byte : Nat}
    (first : ContainsByte left scalar byte) : ¬ ContainsByte right scalar byte := by
  intro second
  have leftBounds := byte_bounds first
  have rightBounds := byte_bounds second
  simp only [Layout.disjoint, contains_nonempty first, contains_nonempty second,
    Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at separate
  omega

def Initialized (scalar : Scalar) (byte : Nat) : Initialization → Prop
  | .none => False
  | .written layout previous => ContainsByte layout scalar byte ∨ Initialized scalar byte previous
  | .intersection left right => Initialized scalar byte left ∧ Initialized scalar byte right

theorem rectangular_initialization_bytes {initialization : Initialization} {layout : Layout} {scalar : Scalar}
    (covered : initialization.coversRectangle scalar layout = true) {byte : Nat}
    (inside : ContainsByte layout scalar byte) : Initialized scalar byte initialization := by
  induction initialization with
  | none =>
    have empty : layout.empty = true := covered
    rw [contains_nonempty inside] at empty
    contradiction
  | written footprint previous ih =>
    simp only [Initialization.coversRectangle, Bool.or_eq_true] at covered
    rcases covered with now | before
    · exact Or.inl (covers_bytes now inside)
    · exact Or.inr (ih before)
  | intersection left right leftIH rightIH =>
    simp only [Initialization.coversRectangle, Bool.and_eq_true] at covered
    exact ⟨leftIH covered.1, rightIH covered.2⟩

theorem footprint_sound {scalar : Scalar} {cursor byte : Nat} {layout : Layout}
    (lo : cursor ≤ byte) (hi : byte < layout.initializedEnd scalar cursor) :
    ContainsByte layout scalar byte := by
  unfold Layout.initializedEnd at hi
  split at hi
  next h =>
    have finish : byte < layout.endByte scalar := by omega
    exact contiguous_bytes h.1 h.2.1 (by omega) finish
  next h => omega

theorem reach_sound {scalar : Scalar} {cursor byte : Nat} (initialization : Initialization)
    (lo : cursor ≤ byte) (hi : byte < initialization.reach scalar cursor) :
    Initialized scalar byte initialization := by
  induction initialization with
  | none => simp [Initialization.reach] at hi; omega
  | written footprint previous ih =>
    simp only [Initialization.reach] at hi
    have alternatives : byte < footprint.initializedEnd scalar cursor ∨ byte < previous.reach scalar cursor := by omega
    rcases alternatives with current | prior
    · exact Or.inl (footprint_sound lo current)
    · exact Or.inr (ih prior)
  | intersection left right ihLeft ihRight =>
    simp only [Initialization.reach, Nat.lt_min] at hi
    exact ⟨ihLeft hi.1, ihRight hi.2⟩

theorem interval_sound {scalar : Scalar} {initialization : Initialization}
    (fuel : Nat) {cursor finish byte : Nat}
    (accepted : initialization.coversInterval scalar fuel cursor finish = true)
    (lo : cursor ≤ byte) (hi : byte < finish) : Initialized scalar byte initialization := by
  induction fuel generalizing cursor with
  | zero => simp only [Initialization.coversInterval, decide_eq_true_eq] at accepted; omega
  | succ fuel ih =>
    simp only [Initialization.coversInterval] at accepted
    split at accepted
    next done => omega
    next pending =>
      split at accepted
      next advances =>
        by_cases inside : byte < initialization.reach scalar cursor
        · exact reach_sound initialization lo inside
        · exact ih accepted (by omega)
      next stopped => contradiction

theorem columns_sound {initialization : Initialization} {layout : Layout} {scalar : Scalar}
    (steps : Nat) (covered : initialization.coversColumns scalar layout steps = true)
    {byte : Nat} (inside : ContainsByte layout scalar byte) : Initialized scalar byte initialization := by
  unfold Initialization.coversColumns at covered
  split at covered
  next bounded =>
    obtain ⟨column, member, lo, hi⟩ := inside
    have accepted := (List.all_eq_true.mp covered) column (List.mem_range.mpr member)
    exact interval_sound _ accepted lo hi
  next tooLarge => contradiction

theorem initialization_bytes {initialization : Initialization} {layout : Layout} {scalar : Scalar}
    (covered : initialization.covers scalar layout = true) {byte : Nat}
    (inside : ContainsByte layout scalar byte) : Initialized scalar byte initialization := by
  unfold Initialization.covers at covered
  split at covered
  next absent => contradiction
  next remaining bounded =>
    simp only [Bool.or_eq_true] at covered
    rcases covered with rectangle | intervals
    · exact rectangular_initialization_bytes rectangle inside
    · split at intervals
      · exact interval_sound _ intervals (byte_bounds inside).1 (byte_bounds inside).2
      · exact columns_sound _ intervals inside

/-- The fallback's repeated history traversals have a fixed metadata-work bound,
independent of allocation capacity and matrix dimensions. -/
theorem initialization_work_bound (nodes : Nat) :
    initializationSteps nodes * nodes ≤ initializationWorkLimit := by
  apply Nat.le_trans (Nat.mul_le_mul_right nodes (Nat.min_le_right _ _))
  exact Nat.div_mul_le_self initializationWorkLimit nodes

theorem initialization_column_work_bound (nodes columns : Nat) :
    (initializationSteps nodes / columns * columns) * nodes ≤ initializationWorkLimit := by
  apply Nat.le_trans (Nat.mul_le_mul_right nodes (Nat.div_mul_le_self _ _))
  exact initialization_work_bound nodes

/-- A proof-only node count for the actual bounded-history traversal. -/
def initializationNodes : Initialization → Nat
  | .none => 1
  | .written _ previous => 1 + initializationNodes previous
  | .intersection left right => 1 + initializationNodes left + initializationNodes right

theorem remaining_nodes {history : Initialization} {fuel remaining : Nat}
    (bounded : history.remaining fuel = some remaining) :
    initializationNodes history + remaining = fuel := by
  induction history generalizing fuel remaining with
  | none =>
    cases fuel <;> simp_all [Initialization.remaining, initializationNodes, Nat.add_comm]
  | written footprint previous ih =>
    cases fuel with
    | zero => simp [Initialization.remaining] at bounded
    | succ fuel =>
      have smaller := ih bounded
      simp only [initializationNodes]
      omega
  | intersection left right leftIH rightIH =>
    cases fuel with
    | zero => simp [Initialization.remaining] at bounded
    | succ fuel =>
      cases first : left.remaining fuel with
      | none => simp [Initialization.remaining, first] at bounded
      | some afterLeft =>
        have leftSize := leftIH first
        simp [Initialization.remaining, first] at bounded
        have rightSize := rightIH bounded
        simp only [initializationNodes]
        omega

theorem checked_initialization_work_bound {history : Initialization} {remaining : Nat}
    (bounded : history.remaining 4096 = some remaining) :
    initializationSteps (4096 - remaining) * initializationNodes history ≤ initializationWorkLimit := by
  have count := remaining_nodes bounded
  have same : 4096 - remaining = initializationNodes history := by omega
  rw [same]
  exact initialization_work_bound _

theorem meet_bytes (left right : Initialization) (scalar : Scalar) (byte : Nat) :
    Initialized scalar byte (left.meet right scalar) ↔
      Initialized scalar byte left ∧ Initialized scalar byte right := by
  unfold Initialization.meet
  split
  next equal => subst right; simp
  next different =>
    cases left <;> cases right <;> simp only [Initialized, false_and, and_false]
    all_goals try rfl
    all_goals split
    all_goals try {
      rename_i equal; cases equal
      exact ⟨fun h => ⟨Or.inr h, h⟩, And.right⟩ }
    all_goals try {
      rename_i equal; cases equal
      exact ⟨fun h => ⟨h, Or.inr h⟩, And.left⟩ }
    all_goals try rfl
    all_goals split
    all_goals try {
      rename_i equal; cases equal
      exact ⟨fun h => ⟨h, Or.inr h⟩, And.left⟩ }
    all_goals try rfl
    all_goals split
    next same =>
      obtain ⟨rfl, separated⟩ := same
      constructor
      · intro initialized
        exact ⟨Or.inr initialized, Or.inr initialized⟩
      · rintro ⟨inLeft | initialized, inRight | initialized⟩
        · exact False.elim (disjoint_bytes separated inLeft inRight)
        all_goals exact initialized
    next => rfl

theorem record_bytes (previous : Initialization) (layout : Layout) (scalar : Scalar) (byte : Nat) :
    Initialized scalar byte (previous.record scalar layout) ↔
      ContainsByte layout scalar byte ∨ Initialized scalar byte previous := by
  unfold Initialization.record
  split
  next covered =>
    constructor
    · exact Or.inr
    · intro either
      exact either.elim (initialization_bytes covered) id
  next notCovered => rfl

/-! ### The explanation of a rejected read borrow

`Initialization.uncoveredCell` is presentation only: `borrowTransition` rejects a
read by `Initialization.covers` before it asks for a cell. These theorems give the
byte meaning of the cell that the diagnostic names. They state nothing about
the search that finds it, and nothing depends on them for acceptance. -/

/-- Containment is complete for one element: a checked footprint that contains
the first byte of an element-aligned address covers the one-cell request at
that address. `covers_bytes` is the converse for every byte of the cell. -/
theorem cell_contained {footprint : Layout} {scalar : Scalar} {capacity address : Nat}
    (valid : checkLayout scalar capacity footprint = true)
    (aligned : address % scalar.width = 0)
    (inside : ContainsByte footprint scalar address) :
    footprint.covers ⟨address, 1, 1, 1, false⟩ scalar = true := by
  have nonempty := contains_nonempty inside
  obtain ⟨column, hc, lo, hi⟩ := inside
  have width : 0 < scalar.width := by cases scalar <;> decide
  have checked := checked_layout valid
  have leading : footprint.rows ≤ footprint.leading := by
    have bound := checked.2.2.2.2.2.1
    omega
  have origin : footprint.offset % scalar.width = 0 := by
    rcases checked.2.2.2.2.2.2.1 with empty | ok
    · rw [nonempty] at empty; contradiction
    · exact ok
  -- The address is a whole number of elements into its stored column.
  have whole : (address - (footprint.offset + column * (footprint.leading * scalar.width))) % scalar.width = 0 := by
    apply Nat.sub_mod_eq_zero_of_mod_eq
    rw [aligned]
    simp [Nat.add_mod, Nat.mul_mod, origin]
  obtain ⟨row, at_row⟩ : ∃ row, address =
      footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) := by
    refine ⟨(address - (footprint.offset + column * (footprint.leading * scalar.width))) / scalar.width, ?_⟩
    have split := Nat.div_add_mod (address - (footprint.offset + column * (footprint.leading * scalar.width)))
      scalar.width
    rw [whole, Nat.add_zero, Nat.mul_comm scalar.width] at split
    omega
  subst at_row
  have hr : row < footprint.rows := by
    have bound : row * scalar.width < footprint.rows * scalar.width := by omega
    exact Nat.lt_of_mul_lt_mul_right bound
  have rowStride : row * scalar.width < footprint.leading * scalar.width :=
    Nat.mul_lt_mul_of_pos_right (by omega) width
  have stridePositive : 0 < footprint.leading * scalar.width := by omega
  have difference : footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) -
      footprint.offset = row * scalar.width + column * (footprint.leading * scalar.width) := by omega
  have alignedDifference : (footprint.offset + row * scalar.width +
      column * (footprint.leading * scalar.width) - footprint.offset) % scalar.width = 0 := by
    rw [difference]
    simp [Nat.add_mod, Nat.mul_mod]
  have remainder : (footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) -
      footprint.offset) % (footprint.leading * scalar.width) = row * scalar.width := by
    rw [difference, Nat.add_comm, Nat.mul_add_mod']
    exact Nat.mod_eq_of_lt rowStride
  have quotient : (footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) -
      footprint.offset) / (footprint.leading * scalar.width) = column := by
    rw [difference, Nat.add_comm, Nat.mul_comm column, Nat.mul_add_div stridePositive]
    simp [Nat.div_eq_of_lt rowStride]
  have notBelow : ¬(footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) <
      footprint.offset) := by omega
  have cellEmpty : (Layout.mk (footprint.offset + row * scalar.width +
      column * (footprint.leading * scalar.width)) 1 1 1 false).empty = false := rfl
  have sameOrigin : ((footprint.offset + row * scalar.width + column * (footprint.leading * scalar.width) -
      footprint.offset) % scalar.width != 0) = false := by simp [alignedDifference]
  simp only [Layout.covers, cellEmpty, Bool.false_eq_true, ↓reduceIte,
    nonempty, notBelow, decide_false, Bool.or_self, sameOrigin]
  cases contiguous : footprint.contiguous
  · simp only [Bool.false_eq_true, ↓reduceIte, alignedDifference, remainder, quotient,
      Nat.mul_div_cancel _ width, Nat.le_refl, decide_true, Bool.true_or,
      beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · have mr := Nat.mul_le_mul_right scalar.width (show row ≤ footprint.rows - 1 by omega)
    have mc := Nat.mul_le_mul_right (footprint.leading * scalar.width)
      (show column ≤ footprint.columns - 1 by omega)
    simp only [↓reduceIte, Layout.endByte, cellEmpty, nonempty, Bool.false_eq_true, ↓reduceIte]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, decide_eq_true_eq]
    omega

/-- The rectangular path is complete for one element: under a checked history,
an element-aligned cell that it rejects has an uninitialized first byte. -/
theorem rejected_cell_uninitialized {history : Initialization} {scalar : Scalar} {capacity address : Nat}
    (valid : history.valid scalar capacity = true) (aligned : address % scalar.width = 0)
    (rejected : history.coversRectangle scalar ⟨address, 1, 1, 1, false⟩ = false) :
    ¬ Initialized scalar address history := by
  induction history with
  | none => simp [Initialized]
  | written footprint previous ih =>
    simp only [Initialization.valid, Bool.and_eq_true] at valid
    simp only [Initialization.coversRectangle, Bool.or_eq_false_iff] at rejected
    intro initialized
    simp only [Initialized] at initialized
    rcases initialized with current | prior
    · have covered := cell_contained valid.1 aligned current
      rw [rejected.1] at covered
      contradiction
    · exact ih valid.2 rejected.2 prior
  | intersection left right ihLeft ihRight =>
    simp only [Initialization.valid, Bool.and_eq_true] at valid
    simp only [Initialization.coversRectangle, Bool.and_eq_false_iff] at rejected
    intro initialized
    simp only [Initialized] at initialized
    rcases rejected with first | second
    · exact ihLeft valid.1 first initialized.1
    · exact ihRight valid.2 second initialized.2

/-- The cell that the diagnostic of a rejected read borrow names is a cell of
the view whose first byte no recorded write initializes on every path. -/
theorem uncoveredCell_uninitialized {history : Initialization} {scalar : Scalar} {capacity : Nat}
    {layout : Layout} {row column : Nat}
    (found : history.uncoveredCell scalar capacity layout = some (row, column)) :
    layout.InDomain (layout.logicalCell row column).1 (layout.logicalCell row column).2 ∧
      ¬ Initialized scalar
        (layout.address scalar (layout.logicalCell row column).1 (layout.logicalCell row column).2) history := by
  obtain ⟨inside, rejected⟩ := Initialization.uncoveredCell_rejected found
  refine ⟨inside, ?_⟩
  have candidate := (Option.filter_eq_some_iff.mp found).1
  unfold Initialization.uncoveredCandidate at candidate
  split at candidate
  next => contradiction
  next remaining budget =>
    split at candidate
    next guards =>
      simp only [Bool.and_eq_true] at guards
      have checked := checked_layout guards.1
      have origin : layout.offset % scalar.width = 0 := by
        rcases checked.2.2.2.2.2.2.1 with empty | ok
        · rw [nonempty_of_index inside] at empty; contradiction
        · exact ok
      have aligned : layout.address scalar (layout.logicalCell row column).1
          (layout.logicalCell row column).2 % scalar.width = 0 := by
        simp only [Layout.address]
        simp [Nat.add_mod, Nat.mul_mod, origin]
      have rectangle : history.coversRectangle scalar
          ⟨layout.address scalar (layout.logicalCell row column).1 (layout.logicalCell row column).2,
            1, 1, 1, false⟩ = false := by
        unfold Initialization.covers at rejected
        simp only [budget, Bool.or_eq_false_iff] at rejected
        exact rejected.1
      exact rejected_cell_uninitialized guards.2 aligned rectangle
    next => contradiction

end VastitasOracle.StorageRegions
