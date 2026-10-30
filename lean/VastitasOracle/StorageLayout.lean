import VastitasKernel.Storage

/-! All-access bounds and byte-interval separation for the actual canonical
storage layout checker. Allocator liveness, pointer ABI, initialization coverage
and public/native integration are separate obligations. -/
namespace VastitasOracle.StorageLayout
open VastitasKernel.Storage

theorem checked_layout {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) : layout.Valid scalar capacity :=
  of_decide_eq_true accepted

theorem physical_indices {layout : Layout} {row column : Nat} (inside : layout.InDomain row column) :
    layout.physicalRow row column < layout.rows ∧ layout.physicalColumn row column < layout.columns := by
  cases transposed : layout.transposed <;>
    simpa [Layout.InDomain, Layout.logicalRows, Layout.logicalColumns,
      Layout.physicalRow, Layout.physicalColumn, transposed, and_comm] using inside

theorem nonempty_of_index {layout : Layout} {row column : Nat} (inside : layout.InDomain row column) :
    layout.empty = false := by
  obtain ⟨hr, hc⟩ := physical_indices inside
  simp only [Layout.empty, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  omega

theorem all_accesses_bounded {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) {row column : Nat}
    (inside : layout.InDomain row column) :
    layout.offset ≤ layout.address scalar row column ∧
      layout.address scalar row column + scalar.width ≤ capacity := by
  have valid := checked_layout accepted
  obtain ⟨hr, hc⟩ := physical_indices inside
  have mr := Nat.mul_le_mul_right scalar.width (show layout.physicalRow row column ≤ layout.rows - 1 by omega)
  have mc := Nat.mul_le_mul_right (layout.leading * scalar.width)
    (show layout.physicalColumn row column ≤ layout.columns - 1 by omega)
  have bound := valid.2.2.2.2.2.2.2
  simp only [Layout.endByte, nonempty_of_index inside, Bool.false_eq_true, ↓reduceIte] at bound
  unfold Layout.address
  omega

theorem all_accesses_aligned {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) {row column : Nat}
    (inside : layout.InDomain row column) : layout.address scalar row column % scalar.alignment = 0 := by
  have valid := checked_layout accepted
  have alignment := valid.2.2.2.2.2.2.1
  have offset : layout.offset % scalar.alignment = 0 := by
    rcases alignment with empty | aligned
    · rw [nonempty_of_index inside] at empty
      contradiction
    · exact aligned
  cases scalar <;> simp [Layout.address, Scalar.width, Scalar.alignment,
    Nat.add_mod, Nat.mul_mod, Scalar.alignment] at offset ⊢ <;> exact offset

private theorem earlier_column (width leading r1 r2 c1 c2 : Nat)
    (rowBound : r1 < leading) (columnOrder : c1 < c2) :
    r1 * width + c1 * (leading * width) + width ≤ r2 * width + c2 * (leading * width) := by
  have rows := Nat.mul_le_mul_right width (show r1 + 1 ≤ leading by omega)
  have columns := Nat.mul_le_mul_right (leading * width) (show c1 + 1 ≤ c2 by omega)
  simp only [Nat.add_mul, Nat.one_mul] at rows columns
  omega

/-- Distinct cells occupy disjoint whole byte intervals, not merely distinct
starting addresses. No enumeration or injectivity assumption is used. -/
theorem all_cells_disjoint {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) {r1 c1 r2 c2 : Nat}
    (first : layout.InDomain r1 c1) (second : layout.InDomain r2 c2)
    (different : (r1, c1) ≠ (r2, c2)) :
    layout.address scalar r1 c1 + scalar.width ≤ layout.address scalar r2 c2 ∨
      layout.address scalar r2 c2 + scalar.width ≤ layout.address scalar r1 c1 := by
  have valid := checked_layout accepted
  have leading : layout.rows ≤ layout.leading := by
    have bound := valid.2.2.2.2.2.1
    omega
  obtain ⟨hr1, hc1⟩ := physical_indices first
  obtain ⟨hr2, hc2⟩ := physical_indices second
  have distinct : (layout.physicalRow r1 c1, layout.physicalColumn r1 c1) ≠
      (layout.physicalRow r2 c2, layout.physicalColumn r2 c2) := by
    intro equal
    apply different
    cases transposed : layout.transposed <;>
      simp [Layout.physicalRow, Layout.physicalColumn, transposed, Prod.mk.injEq] at equal ⊢ <;> omega
  rcases Nat.lt_trichotomy (layout.physicalColumn r1 c1) (layout.physicalColumn r2 c2) with before | same | after
  · have bound := earlier_column scalar.width layout.leading
      (layout.physicalRow r1 c1) (layout.physicalRow r2 c2)
      (layout.physicalColumn r1 c1) (layout.physicalColumn r2 c2)
      (by omega) before
    left
    simp only [Layout.address]
    omega
  · have notSame : layout.physicalRow r1 c1 ≠ layout.physicalRow r2 c2 := by
      intro equal
      exact distinct (Prod.ext equal same)
    rcases Nat.lt_or_gt_of_ne notSame with before | after
    · have bound := Nat.mul_le_mul_right scalar.width
        (show layout.physicalRow r1 c1 + 1 ≤ layout.physicalRow r2 c2 by omega)
      left
      simp only [Layout.address, same]
      simp only [Nat.add_mul, Nat.one_mul] at bound
      omega
    · have bound := Nat.mul_le_mul_right scalar.width
        (show layout.physicalRow r2 c2 + 1 ≤ layout.physicalRow r1 c1 by omega)
      right
      simp only [Layout.address, same]
      simp only [Nat.add_mul, Nat.one_mul] at bound
      omega
  · have bound := earlier_column scalar.width layout.leading
      (layout.physicalRow r2 c2) (layout.physicalRow r1 c1)
      (layout.physicalColumn r2 c2) (layout.physicalColumn r1 c1)
      (by omega) after
    right
    simp only [Layout.address]
    omega

theorem transpose_preserves_footprint (layout : Layout) (scalar : Scalar) :
    layout.transpose.endByte scalar = layout.endByte scalar ∧
    ∀ row column, layout.transpose.address scalar row column = layout.address scalar column row := by
  constructor
  · rfl
  · intro row column
    cases transposed : layout.transposed <;>
      simp [Layout.transpose, Layout.address, Layout.physicalRow, Layout.physicalColumn, transposed]

/-- Every intermediate in the specified offset expression fits the checked
signed byte range. This does not cover arbitrary rewrites or pointer addition. -/
theorem native_stride_fits {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) :
    layout.leading * scalar.width ≤ byteLimit := by
  have leading := (checked_layout accepted).2.2.2.2.1
  cases scalar <;> simp [Scalar.width, dimensionLimit, byteLimit] at leading ⊢ <;> omega

theorem native_offset_intermediates {scalar : Scalar} {capacity : Nat} {layout : Layout}
    (accepted : checkLayout scalar capacity layout = true) {row column : Nat}
    (inside : layout.InDomain row column) :
    layout.physicalRow row column * scalar.width ≤ byteLimit ∧
    layout.physicalColumn row column * (layout.leading * scalar.width) ≤ byteLimit ∧
    layout.offset + layout.physicalRow row column * scalar.width ≤ byteLimit ∧
    layout.address scalar row column + scalar.width ≤ byteLimit := by
  have capacityBound := (checked_layout accepted).1
  have bound := (all_accesses_bounded accepted inside).2
  simp only [Layout.address] at bound ⊢
  omega

end VastitasOracle.StorageLayout
