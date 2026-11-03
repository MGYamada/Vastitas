import VastitasKernel.StorageShapes
import VastitasStorageNative
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Universal arithmetic checks for the actual optional runtime helpers and the
Lean UInt64 comparisons emitted by StorageShapeCodegen.renderGuard. This test-only
script imports both packages; neither package gains a dependency on the other.
It proves Lean-level helper/guard agreement, not interpretation of generated
source text, C/FFI refinement, physical heap validity or floating-point laws.
Run with the same LEAN_PATH as check_runtime_shape_guards.lean.
-/

open VastitasKernel.Storage
namespace RuntimeShapeGuardProof

def layoutPredicate (scalar : Scalar) (elements rows columns leading : Nat) : Prop :=
  elements ≤ byteLimit / scalar.width ∧
  rows ≤ dimensionLimit ∧ columns ≤ dimensionLimit ∧ leading ≤ dimensionLimit ∧
  1 ≤ leading ∧ rows ≤ leading ∧
  (rows = 0 ∨ columns = 0 ∨ (columns - 1) * leading + rows ≤ elements)

instance : Decidable (layoutPredicate scalar elements rows columns leading) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem whole_layout (scalar : Scalar) (elements rows columns leading : Nat) :
    checkLayout scalar (elements * scalar.width) ⟨0, rows, columns, leading, false⟩ =
      decide (layoutPredicate scalar elements rows columns leading) := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkLayout, decide_eq_true_eq]
  cases scalar <;> by_cases zeroRows : rows = 0 <;> by_cases zeroColumns : columns = 0 <;>
    simp_all [Layout.Valid, Layout.empty, Layout.endByte, layoutPredicate,
      Scalar.width, byteLimit, dimensionLimit, Nat.max_le, ← Nat.mul_assoc] <;> omega

theorem span_toNat (rows columns leading : UInt64)
    (rowBound : rows.toNat ≤ dimensionLimit)
    (columnBound : columns.toNat ≤ dimensionLimit)
    (leadingBound : leading.toNat ≤ dimensionLimit)
    (nonempty : 0 < columns.toNat) :
    ((columns - 1) * leading + rows).toNat =
      (columns.toNat - 1) * leading.toNat + rows.toNat := by
  have columnPositive : (1 : UInt64) ≤ columns := by
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat]
    omega
  have productBound := Nat.mul_le_mul (show columns.toNat - 1 ≤ dimensionLimit by omega) leadingBound
  have productFits : (columns.toNat - 1) * leading.toNat < 2^64 := by
    simp only [dimensionLimit] at *
    omega
  have sumFits : (columns.toNat - 1) * leading.toNat + rows.toNat < 2^64 := by
    simp only [dimensionLimit] at *
    omega
  rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le _ _ columnPositive]
  simp only [UInt64.toNat_ofNat]
  rw [Nat.mod_eq_of_lt productFits, Nat.mod_eq_of_lt sumFits]

def scalarTag : Scalar → UInt8 | .f64 => 0 | .complexF64 => 1

theorem runtime_layout (scalar : Scalar) (elements rows columns leading : UInt64) :
    VastitasStorageNative.runtimeLayoutValid (scalarTag scalar) elements rows columns leading =
      decide (layoutPredicate scalar elements.toNat rows.toNat columns.toNat leading.toNat) := by
  apply Bool.eq_iff_iff.mpr
  cases scalar <;>
    simp [scalarTag, VastitasStorageNative.runtimeLayoutValid,
      UInt8.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt,
      UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  all_goals
    simp only [layoutPredicate, Scalar.width, byteLimit, dimensionLimit]
    constructor
    · rintro ⟨⟨⟨⟨⟨hr, hc⟩, hl⟩, hn⟩, hrl⟩, he, hs⟩
      refine ⟨he, hr, hc, hl, by omega, hrl, ?_⟩
      rcases hs with empty | fits
      · rcases empty with zero | zero
        · exact Or.inl zero
        · exact Or.inr (Or.inl zero)
      · by_cases zero : columns.toNat = 0
        · exact Or.inr (Or.inl zero)
        · have exactSpan := span_toNat rows columns leading hr hc hl (by omega)
          simp at exactSpan
          exact Or.inr (Or.inr (by simpa only [exactSpan] using fits))
    · rintro ⟨he, hr, hc, hl, hn, hrl, hs⟩
      refine ⟨⟨⟨⟨⟨hr, hc⟩, hl⟩, by omega⟩, hrl⟩, he, ?_⟩
      rcases hs with zero | zero | fits
      · exact Or.inl (Or.inl zero)
      · exact Or.inl (Or.inr zero)
      · by_cases zero : columns.toNat = 0
        · exact Or.inl (Or.inr zero)
        · have exactSpan := span_toNat rows columns leading hr hc hl (by omega)
          simp at exactSpan
          exact Or.inr (by simpa only [exactSpan] using fits)

theorem runtime_layout_checked (scalar : Scalar) (elements rows columns leading : UInt64)
    (transposed : Bool) :
    VastitasStorageNative.runtimeLayoutValid (scalarTag scalar) elements rows columns leading =
      checkLayout scalar (elements.toNat * scalar.width)
        ⟨0, rows.toNat, columns.toNat, leading.toNat, transposed⟩ := by
  exact (runtime_layout scalar elements rows columns leading).trans
    (whole_layout scalar elements.toNat rows.toNat columns.toNat leading.toNat).symm

theorem layout_guard (values : Shapes.Valuation) (scalar : Scalar)
    (elements : Shapes.Extent) (shape : Shapes.Layout)
    (e r c l : UInt64)
    (elementValue : elements.eval values = e.toNat)
    (rowValue : shape.rows.eval values = r.toNat)
    (columnValue : shape.columns.eval values = c.toNat)
    (leadingValue : shape.leading.eval values = l.toNat) :
    VastitasStorageNative.runtimeLayoutValid (scalarTag scalar) e r c l =
      (Shapes.Guard.layout scalar elements shape).eval values := by
  simp only [Shapes.Guard.eval, Shapes.Layout.eval, elementValue, rowValue, columnValue, leadingValue]
  exact runtime_layout_checked scalar e r c l shape.transposed

theorem extent_nat_success (value result : Nat) (accepted : Shapes.narrowNat value = some result) :
    VastitasStorageNative.runtimeExtentNat value = pure (UInt64.ofNat result) ∧
      (UInt64.ofNat result).toNat = value := by
  by_cases bounded : value ≤ byteLimit
  · simp only [Shapes.narrowNat, bounded, ite_true, Option.some.injEq] at accepted
    subst result
    have bound : ¬9223372036854775807 < value := by simp only [byteLimit] at bounded; omega
    constructor
    · simp [VastitasStorageNative.runtimeExtentNat, bound]
    · apply UInt64.toNat_ofNat_of_lt'
      simp only [UInt64.size, byteLimit] at *
      omega
  · simp [Shapes.narrowNat, bounded] at accepted

theorem extent_nat_failure (value : Nat) (rejected : Shapes.narrowNat value = none) :
    VastitasStorageNative.runtimeExtentNat value =
      throw (IO.userError "E_RUNTIME_EXTENT: extent exceeds signed native size range") := by
  have bounded : ¬value ≤ byteLimit := by
    by_cases h : value ≤ byteLimit
    · simp [Shapes.narrowNat, h] at rejected
    · exact h
  have bound : 9223372036854775807 < value := by simp only [byteLimit] at bounded; omega
  simp [VastitasStorageNative.runtimeExtentNat, bound]
  rfl

theorem extent_int_success (value : Int) (result : Nat)
    (accepted : Shapes.narrowInt value = some result) :
    VastitasStorageNative.runtimeExtentInt value = pure (UInt64.ofNat result) ∧
      Int.ofNat (UInt64.ofNat result).toNat = value := by
  by_cases negative : value < 0
  · simp [Shapes.narrowInt, negative] at accepted
  · simp only [Shapes.narrowInt, negative, ite_false] at accepted
    obtain ⟨run, exactValue⟩ := extent_nat_success value.toNat result accepted
    constructor
    · simpa [VastitasStorageNative.runtimeExtentInt, negative] using run
    · rw [exactValue]
      exact Int.toNat_of_nonneg (by omega)

theorem extent_int_failure (value : Int) (rejected : Shapes.narrowInt value = none) :
    VastitasStorageNative.runtimeExtentInt value =
      throw (IO.userError (if value < 0 then "E_RUNTIME_EXTENT: extent is negative"
        else "E_RUNTIME_EXTENT: extent exceeds signed native size range")) := by
  by_cases negative : value < 0
  · simp [VastitasStorageNative.runtimeExtentInt, negative]
    rfl
  · simp only [Shapes.narrowInt, negative, ite_false] at rejected
    simpa [VastitasStorageNative.runtimeExtentInt, negative] using extent_nat_failure value.toNat rejected

theorem invalid_scalar (scalar : UInt8) (elements rows columns leading : UInt64)
    (invalid : 1 < scalar) :
    VastitasStorageNative.runtimeLayoutValid scalar elements rows columns leading = false := by
  simp [VastitasStorageNative.runtimeLayoutValid, invalid]

theorem bound_expression (value : UInt64) (maximum : Nat) (fits : maximum < 2^64) :
    decide (value ≤ UInt64.ofNat maximum) = decide (value.toNat ≤ maximum) := by
  simp [UInt64.le_iff_toNat_le, Nat.mod_eq_of_lt fits]

theorem equal_expression (left right : UInt64) :
    (left == right) = (left.toNat == right.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [← UInt64.toNat_inj]

theorem cell_expression (rows columns leading : UInt64) (transposed : Bool)
    (row column : Nat) (rowFits : row < 2^64) (columnFits : column < 2^64) :
    (decide (UInt64.ofNat row < (if transposed then columns else rows)) &&
      decide (UInt64.ofNat column < (if transposed then rows else columns))) =
    decide ((⟨0, rows.toNat, columns.toNat, leading.toNat, transposed⟩ : Layout).InDomain row column) := by
  cases transposed <;>
    simp [Layout.InDomain, Layout.logicalRows, Layout.logicalColumns,
      UInt64.lt_iff_toNat_lt, Nat.mod_eq_of_lt rowFits, Nat.mod_eq_of_lt columnFits]

end RuntimeShapeGuardProof

open Lean Elab Command
run_cmd do
  let declarations := #[`RuntimeShapeGuardProof.whole_layout, `RuntimeShapeGuardProof.span_toNat,
    `RuntimeShapeGuardProof.runtime_layout, `RuntimeShapeGuardProof.runtime_layout_checked,
    `RuntimeShapeGuardProof.layout_guard, `RuntimeShapeGuardProof.extent_nat_success,
    `RuntimeShapeGuardProof.extent_nat_failure, `RuntimeShapeGuardProof.extent_int_success,
    `RuntimeShapeGuardProof.extent_int_failure, `RuntimeShapeGuardProof.invalid_scalar,
    `RuntimeShapeGuardProof.bound_expression, `RuntimeShapeGuardProof.equal_expression,
    `RuntimeShapeGuardProof.cell_expression]
  for name in declarations do
    unless (← getEnv).contains name do throwError "missing runtime-guard theorem {name}"
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unapproved runtime-guard axiom {axiomName} in {name}"
  logInfo m!"runtime shape guards: {declarations.size} universal helper/expression theorems audited"
