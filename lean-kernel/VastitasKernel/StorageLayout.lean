import Std

/-! Canonical layout and region records for the resource IR. Arithmetic is
mathematical Nat arithmetic; narrowing is checked after computing bounds.
This is not a runtime pointer or an assertion that foreign storage is live. -/
namespace VastitasKernel.Storage

inductive Scalar where
  | f64 | complexF64
  deriving Repr, BEq, DecidableEq, Inhabited

def Scalar.width : Scalar → Nat | .f64 => 8 | .complexF64 => 16
def Scalar.alignment (_ : Scalar) : Nat := 8

/-- A dense physical rectangle and an explicit logical transpose. `leading`
is measured in elements; `offset` and capacity are measured in bytes. Padding
is not part of the rectangle. Arbitrary strides require a future contract. -/
structure Layout where
  offset : Nat
  rows : Nat
  columns : Nat
  leading : Nat
  transposed : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

def Layout.empty (layout : Layout) : Bool := layout.rows == 0 || layout.columns == 0
def Layout.logicalRows (layout : Layout) : Nat := if layout.transposed then layout.columns else layout.rows
def Layout.logicalColumns (layout : Layout) : Nat := if layout.transposed then layout.rows else layout.columns
def Layout.transpose (layout : Layout) : Layout := { layout with transposed := !layout.transposed }
def Layout.physicalRow (layout : Layout) (row column : Nat) : Nat := if layout.transposed then column else row
def Layout.physicalColumn (layout : Layout) (row column : Nat) : Nat := if layout.transposed then row else column

def Layout.InDomain (layout : Layout) (row column : Nat) : Prop :=
  row < layout.logicalRows ∧ column < layout.logicalColumns

instance (layout : Layout) (row column : Nat) : Decidable (layout.InDomain row column) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Layout.address (layout : Layout) (scalar : Scalar) (row column : Nat) : Nat :=
  layout.offset + layout.physicalRow row column * scalar.width +
    layout.physicalColumn row column * (layout.leading * scalar.width)

/-- The empty branch precedes subtraction and forms no element pointer. -/
def Layout.endByte (layout : Layout) (scalar : Scalar) : Nat :=
  if layout.empty then layout.offset
  else layout.offset + (layout.rows - 1) * scalar.width +
    (layout.columns - 1) * (layout.leading * scalar.width) + scalar.width

def byteLimit : Nat := 2^63 - 1
def dimensionLimit : Nat := 2^31 - 1

def Layout.Valid (scalar : Scalar) (capacity : Nat) (layout : Layout) : Prop :=
  capacity ≤ byteLimit ∧ layout.offset ≤ capacity ∧
  layout.rows ≤ dimensionLimit ∧ layout.columns ≤ dimensionLimit ∧
  layout.leading ≤ dimensionLimit ∧ max 1 layout.rows ≤ layout.leading ∧
  (layout.empty = true ∨ layout.offset % scalar.alignment = 0) ∧
  layout.endByte scalar ≤ capacity

instance (scalar : Scalar) (capacity : Nat) (layout : Layout) : Decidable (layout.Valid scalar capacity) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkLayout (scalar : Scalar) (capacity : Nat) (layout : Layout) : Bool :=
  decide (layout.Valid scalar capacity)

/-- A whole byte interval is available only if there is no inter-column gap. -/
def Layout.contiguous (layout : Layout) : Bool := layout.columns ≤ 1 || layout.leading == layout.rows

/-- Conservative containment of actual element bytes, not just envelopes.
For padded rectangles require the same grid and reconstruct the row/column
shift. Transpose changes no physical footprint. This runs in constant metadata
operations, independent of the number of cells. -/
def Layout.covers (outer inner : Layout) (scalar : Scalar) : Bool :=
  if inner.empty then true
  else if outer.empty || inner.offset < outer.offset then false
  else if outer.contiguous then inner.endByte scalar ≤ outer.endByte scalar
  else
    let difference := inner.offset - outer.offset
    let stride := outer.leading * scalar.width
    (inner.columns ≤ 1 || inner.leading == outer.leading) && difference % scalar.width == 0 &&
      difference % stride / scalar.width + inner.rows ≤ outer.rows &&
      difference / stride + inner.columns ≤ outer.columns

def Layout.disjoint (left right : Layout) (scalar : Scalar) : Bool :=
  left.empty || right.empty || left.endByte scalar ≤ right.offset || right.endByte scalar ≤ left.offset

/-- Exact record of writes and branch intersections. Entailment preserves
padding holes and never treats an enclosing envelope as a write. -/
inductive Initialization where
  | none
  | written (layout : Layout) (previous : Initialization)
  | intersection (left right : Initialization)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Consume a finite metadata budget before any unbounded history traversal.
Shared branch histories must not turn a short source into exponential auditing. -/
def Initialization.remaining : Nat → Initialization → Option Nat
  | 0, _ => Option.none
  | fuel + 1, .none => some fuel
  | fuel + 1, .written _ previous => previous.remaining fuel
  | fuel + 1, .intersection left right => do
    let afterLeft ← left.remaining fuel
    right.remaining afterLeft

/-- Identical guarantees share one history; an empty guarantee on either side
annuls a branch intersection. Inputs are budget-audited before equality. -/
def Initialization.meet (left right : Initialization) : Initialization :=
  match left, right with
  | .none, _ | _, .none => .none
  | _, _ => if left = right then left else .intersection left right

def Initialization.coversRectangle (scalar : Scalar) (layout : Layout) : Initialization → Bool
  | .none => layout.empty
  | .written footprint previous => footprint.covers layout scalar || previous.coversRectangle scalar layout
  | .intersection left right => left.coversRectangle scalar layout && right.coversRectangle scalar layout

/-- Extend only through a contiguous write containing the cursor. A padded
rectangle is not flattened into its enclosing byte interval. -/
def Layout.initializedEnd (scalar : Scalar) (cursor : Nat) (layout : Layout) : Nat :=
  if layout.contiguous = true ∧ layout.empty = false ∧ layout.offset ≤ cursor
  then max cursor (layout.endByte scalar)
  else cursor

/-- At a branch join both histories must justify every byte of the extension.
This traverses write metadata, never the allocation or its elements. -/
def Initialization.reach (scalar : Scalar) (cursor : Nat) : Initialization → Nat
  | .none => cursor
  | .written footprint previous => max (footprint.initializedEnd scalar cursor) (previous.reach scalar cursor)
  | .intersection left right => min (left.reach scalar cursor) (right.reach scalar cursor)

def Initialization.coversInterval (scalar : Scalar) (history : Initialization) : Nat → Nat → Nat → Bool
  | 0, cursor, finish => decide (finish ≤ cursor)
  | fuel + 1, cursor, finish =>
    if finish ≤ cursor then true
    else
      let next := history.reach scalar cursor
      if cursor < next then history.coversInterval scalar fuel next finish
      else false

/-- A fixed metadata-work budget prevents a large union or branch history from
turning an individual initialization query into unbounded repeated traversal. -/
def initializationWorkLimit : Nat := 65536

def initializationSteps (nodes : Nat) : Nat := min nodes (initializationWorkLimit / nodes)

/-- A padded request checks only its physical columns, not the padding. The
column count must fit the metadata-derived budget before constructing its range;
each column receives an equal share of the bounded interval traversals. -/
def Initialization.coversColumns (scalar : Scalar) (layout : Layout) (steps : Nat)
    (history : Initialization) : Bool :=
  if layout.columns ≤ steps then
    (List.range layout.columns).all fun column =>
      let start := layout.offset + column * (layout.leading * scalar.width)
      history.coversInterval scalar (steps / layout.columns) start (start + layout.rows * scalar.width)
  else false

/-- Keep exact rectangular containment as the fast path. Otherwise reconstruct
coverage from contiguous write intervals, including intersections at joins.
Padded requests check separate columns; their gaps need not be initialized.
At most 4096 metadata nodes and 65536 fallback node visits are admitted per query;
budget exhaustion rejects rather than assuming initialization. -/
def Initialization.covers (scalar : Scalar) (layout : Layout) (history : Initialization) : Bool :=
  match history.remaining 4096 with
  | Option.none => false
  | some remaining =>
    history.coversRectangle scalar layout || (if layout.contiguous then
      history.coversInterval scalar (initializationSteps (4096 - remaining)) layout.offset (layout.endByte scalar)
    else history.coversColumns scalar layout (initializationSteps (4096 - remaining)))

/-- Writing an already initialized region does not enlarge its metadata. -/
def Initialization.record (scalar : Scalar) (layout : Layout) (previous : Initialization) : Initialization :=
  if previous.covers scalar layout then previous else .written layout previous

def Initialization.valid (scalar : Scalar) (capacity : Nat) : Initialization → Bool
  | .none => true
  | .written layout previous => checkLayout scalar capacity layout && previous.valid scalar capacity
  | .intersection left right => left.valid scalar capacity && right.valid scalar capacity

end VastitasKernel.Storage
