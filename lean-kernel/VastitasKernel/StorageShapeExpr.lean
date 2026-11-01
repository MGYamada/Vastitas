import VastitasKernel.Storage
import VastitasKernel.IndexedCore

/-! Symbolic dimensions refer to immutable, independently typed scalar slots.
This is a compiler representation, not a runtime expression interpreter.
Arithmetic remains in actual checked scalar Core; the shape layer only names
its results and emits checked narrowing and physical-layout preflight. -/
namespace VastitasKernel.Storage.Shapes

inductive Extent where
  | literal (value : Nat)
  | slot (name : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Valuation := Symbol → Nat

def Extent.eval (values : Valuation) : Extent → Nat
  | .literal value => value
  | .slot name => values name

def Extent.references : Extent → List Symbol
  | .literal _ => []
  | .slot name => [name]

def Extent.rename (names : Symbol → Symbol) : Extent → Extent
  | .literal value => .literal value
  | .slot name => .slot (names name)

/-- Whole-map physical layout. Offset is deliberately absent: the first profile
does not establish dynamic subregion separation or containment. Transposition
is a fixed representation choice and never a runtime dispatch key. -/
structure Layout where
  rows : Extent
  columns : Extent
  leading : Extent
  transposed : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

def Layout.eval (values : Valuation) (layout : Layout) : Storage.Layout :=
  ⟨0, layout.rows.eval values, layout.columns.eval values,
    layout.leading.eval values, layout.transposed⟩

def Layout.logicalRows (layout : Layout) : Extent :=
  if layout.transposed then layout.columns else layout.rows

def Layout.logicalColumns (layout : Layout) : Extent :=
  if layout.transposed then layout.rows else layout.columns

def Layout.references (layout : Layout) : List Symbol :=
  layout.rows.references ++ layout.columns.references ++ layout.leading.references

def Layout.rename (names : Symbol → Symbol) (layout : Layout) : Layout :=
  ⟨layout.rows.rename names, layout.columns.rename names,
    layout.leading.rename names, layout.transposed⟩

/-- Each guard has a direct finite arithmetic lowering. There are no dynamic
owner/loan/name-table operations in this representation. -/
inductive Guard where
  | bound (extent : Extent) (maximum : Nat)
  | layout (scalar : Scalar) (elements : Extent) (layout : Layout)
  | equal (left right : Extent)
  | cell (layout : Layout) (row column : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Guard.eval (values : Valuation) : Guard → Bool
  | .bound extent maximum => extent.eval values ≤ maximum
  | .layout scalar elements shape =>
    checkLayout scalar (elements.eval values * scalar.width) (shape.eval values)
  | .equal left right => left.eval values == right.eval values
  | .cell shape row column => decide ((shape.eval values).InDomain row column)

def Guard.references : Guard → List Symbol
  | .bound extent _ => extent.references
  | .layout _ elements shape => elements.references ++ shape.references
  | .equal left right => left.references ++ right.references
  | .cell shape .. => shape.references

def guardsHold (values : Valuation) (guards : List Guard) : Prop :=
  ∀ guard ∈ guards, guard.eval values = true

/-- Exact logical write history. Interpretation uses the actual optimizing
record operation, including empty extents and already initialized rectangles. -/
inductive Initialization where
  | none
  | record (layout : Layout) (prior : Initialization)
  deriving Repr, BEq, DecidableEq, Inhabited

def Initialization.eval (values : Valuation) (scalar : Scalar) : Initialization → Storage.Initialization
  | .none => .none
  | .record layout prior => (prior.eval values scalar).record scalar (layout.eval values)

def Initialization.nodes : Initialization → Nat
  | .none => 1
  | .record _ prior => prior.nodes + 1

def Initialization.layouts : Initialization → List Layout
  | .none => []
  | .record layout prior => layout :: prior.layouts

/-- A source scalar value is narrowed only after this predicate holds. Int
values are never converted by saturating/clamping a negative value to Nat. -/
def narrowNat (value : Nat) : Option Nat :=
  if value ≤ byteLimit then some value else none

def narrowInt (value : Int) : Option Nat :=
  if value < 0 then none else narrowNat value.toNat

end VastitasKernel.Storage.Shapes
