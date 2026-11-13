import Std

/-! Canonical layout and region records for the resource IR. Arithmetic is
mathematical Nat arithmetic; narrowing is checked after computing bounds.
This is not a runtime pointer or an assertion that foreign storage is live. -/
namespace VastitasKernel.Storage

inductive Scalar where
  | f64 | complexF64
  deriving Repr, BEq, DecidableEq, Inhabited

def Scalar.width : Scalar → Nat | .f64 => 8 | .complexF64 => 16
/-- Native binary64 component alignment. Typed views additionally preserve
whole-element boundaries relative to their allocation origin. -/
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
  (layout.empty = true ∨ layout.offset % scalar.width = 0) ∧
  layout.endByte scalar ≤ capacity

instance (scalar : Scalar) (capacity : Nat) (layout : Layout) : Decidable (layout.Valid scalar capacity) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkLayout (scalar : Scalar) (capacity : Nat) (layout : Layout) : Bool :=
  decide (layout.Valid scalar capacity)

/-- The first conjunct of `Layout.Valid` that fails, with its computed
numbers. This explains a rejection only; `checkLayout` alone decides. -/
inductive Layout.Violation where
  | capacity (capacity : Nat)
  | offset (offset capacity : Nat)
  | rows (rows : Nat)
  | columns (columns : Nat)
  | leading (leading : Nat)
  | leadingBelowRows (leading rows : Nat)
  | alignment (offset width : Nat)
  | endByte (endByte capacity width : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Layout.firstViolation (scalar : Scalar) (capacity : Nat) (layout : Layout) : Option Layout.Violation :=
  if ¬capacity ≤ byteLimit then some (.capacity capacity)
  else if ¬layout.offset ≤ capacity then some (.offset layout.offset capacity)
  else if ¬layout.rows ≤ dimensionLimit then some (.rows layout.rows)
  else if ¬layout.columns ≤ dimensionLimit then some (.columns layout.columns)
  else if ¬layout.leading ≤ dimensionLimit then some (.leading layout.leading)
  else if ¬max 1 layout.rows ≤ layout.leading then some (.leadingBelowRows layout.leading layout.rows)
  else if ¬(layout.empty = true ∨ layout.offset % scalar.width = 0) then
    some (.alignment layout.offset scalar.width)
  else if ¬layout.endByte scalar ≤ capacity then
    some (.endByte (layout.endByte scalar) capacity scalar.width)
  else none

/-- The explanation can never disagree with acceptance. -/
theorem Layout.firstViolation_eq_none (scalar : Scalar) (capacity : Nat) (layout : Layout) :
    layout.firstViolation scalar capacity = none ↔ layout.Valid scalar capacity := by
  unfold Layout.firstViolation Layout.Valid
  repeat' split
  all_goals simp only [reduceCtorEq, false_iff, not_and]
  all_goals first
    | (intros; omega)
    | (intros; simp_all; done)
    | (cases empty : layout.empty <;> simp_all)

theorem checkLayout_eq_false_iff_violation (scalar : Scalar) (capacity : Nat) (layout : Layout) :
    checkLayout scalar capacity layout = false ↔ (layout.firstViolation scalar capacity).isSome := by
  have := Layout.firstViolation_eq_none scalar capacity layout
  cases h : layout.firstViolation scalar capacity <;> simp_all [checkLayout]

def Layout.Violation.message : Layout.Violation → String
  | .capacity bytes => s!"allocation capacity {bytes} bytes exceeds the native limit 2^63 - 1"
  | .offset start bytes => s!"view offset {start} is beyond the allocation's {bytes} bytes"
  | .rows count => s!"rows {count} exceed the native limit 2^31 - 1"
  | .columns count => s!"columns {count} exceed the native limit 2^31 - 1"
  | .leading count => s!"leading {count} exceeds the native limit 2^31 - 1"
  | .leadingBelowRows stride count => s!"leading {stride} is smaller than max(1, rows {count})"
  | .alignment start width => s!"view offset {start} is not aligned to {width}-byte elements"
  | .endByte stop bytes width =>
    s!"view ends at byte {stop}, but the allocation has {bytes} bytes ({bytes / width} elements of {width} bytes)"

/-- A whole byte interval is available only if there is no inter-column gap. -/
def Layout.contiguous (layout : Layout) : Bool := layout.columns ≤ 1 || layout.leading == layout.rows

/-- Conservative containment of actual element bytes, not just envelopes.
For padded rectangles require the same grid and reconstruct the row/column
shift. Transpose changes no physical footprint. This runs in constant metadata
operations, independent of the number of cells. -/
def Layout.covers (outer inner : Layout) (scalar : Scalar) : Bool :=
  if inner.empty then true
  else if outer.empty || inner.offset < outer.offset then false
  else if (inner.offset - outer.offset) % scalar.width != 0 then false
  else if outer.contiguous then inner.endByte scalar ≤ outer.endByte scalar
  else
    let difference := inner.offset - outer.offset
    let stride := outer.leading * scalar.width
    (inner.columns ≤ 1 || inner.leading == outer.leading) && difference % scalar.width == 0 &&
      difference % stride / scalar.width + inner.rows ≤ outer.rows &&
      difference / stride + inner.columns ≤ outer.columns

def Layout.disjoint (left right : Layout) (scalar : Scalar) : Bool :=
  left.empty || right.empty || left.endByte scalar ≤ right.offset || right.endByte scalar ≤ left.offset

/-- The bytes `[offset, endByte)` of a nonempty contiguous footprint, all of
which it holds. A padded or empty footprint has no such run. -/
def Layout.run? (scalar : Scalar) (layout : Layout) : Option (Nat × Nat) :=
  if layout.contiguous && !layout.empty then some (layout.offset, layout.endByte scalar) else none

/-- One stored column of `count` cells from byte `start`: the canonical record
of a run of whole cells. -/
def Layout.cells (start count : Nat) : Layout := ⟨start, count, 1, count, false⟩

/-- The canonical record of the bytes `[start, finish)` when they are a
nonempty run of whole cells whose number fits the native dimension limit. -/
def Layout.ofRun (scalar : Scalar) (start finish : Nat) : Option Layout :=
  let count := (finish - start) / scalar.width
  if 0 < count ∧ count ≤ dimensionLimit ∧ start + count * scalar.width = finish then
    some (Layout.cells start count)
  else none

/-- A write that continues a canonical run at either end. The merged run is
again canonical, so that records which only runs extend stay comparable. -/
def Layout.extend (scalar : Scalar) (last write : Layout) : Option Layout :=
  if last = Layout.cells last.offset last.rows then
    match last.run? scalar, write.run? scalar with
    | some (start, finish), some (start', finish') =>
      if finish = start' then Layout.ofRun scalar start finish'
      else if finish' = start then Layout.ofRun scalar start' finish
      else none
    | _, _ => none
  else none

/-- The canonical record of the bytes that two runs share. -/
def Layout.common (scalar : Scalar) (left right : Layout) : Option Layout :=
  match left.run? scalar, right.run? scalar with
  | some (start, finish), some (start', finish') =>
    Layout.ofRun scalar (max start start') (min finish finish')
  | _, _ => none

/-- `outer` contains `inner`, and every byte that `outer` shares with the
envelope of `write` lies in `inner`. Then the bytes that `write` adds beside
`inner` are none that `outer` holds. -/
def Layout.absorbs (scalar : Scalar) (outer inner write : Layout) : Bool :=
  outer.covers inner scalar &&
    match outer.run? scalar, inner.run? scalar with
    | some (start, finish), some (start', finish') =>
      let low := max start write.offset
      let high := min finish (write.endByte scalar)
      decide (high ≤ low) || (decide (start' ≤ low) && decide (high ≤ finish'))
    | _, _ => false

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

/-- The join of two writes over one history: `(H ∪ A) ∩ (H ∪ B) = H ∪ (A ∩ B)`.
Disjoint writes leave `H`, a contained write leaves its own arm, and two runs
leave the run that they share. -/
def Initialization.meetWrites (scalar : Scalar) (a b : Layout) (previous : Initialization) : Initialization :=
  if a.disjoint b scalar then previous
  else if a.covers b scalar then .written b previous
  else if b.covers a scalar then .written a previous
  else match a.common scalar b with
    | some shared => .written shared previous
    | Option.none => .intersection (.written a previous) (.written b previous)

/-- One arm `.written outer base` and the other `.written write (.written inner base)`,
where `outer` absorbs `inner` beside `write`: their join is the second arm's
history `.written inner base`. This is the join of a write in one arm with a
write in the other that extended the run `inner` (`Initialization.record`). -/
def Initialization.absorbs (scalar : Scalar) (outer : Layout) (base : Initialization)
    (write : Layout) : Initialization → Bool
  | .written inner older => decide (older = base) && outer.absorbs scalar inner write
  | _ => false

/-- Exact absorption avoids copying a common history when only one branch adds
a write, or when both branches add a write to the same history. Writes that
extended a common run are joined through that run. Other intersections retain
both histories. Inputs are budget-audited before equality; no layout elements
are enumerated. -/
def Initialization.meet (left right : Initialization) (scalar : Scalar) : Initialization :=
  if left = right then left else
  match left, right with
  | .none, _ | _, .none => .none
  | .written a previous, .written b other =>
    if previous = right then right
    else if left = other then left
    else if previous = other then Initialization.meetWrites scalar a b previous
    else if Initialization.absorbs scalar b other a previous then previous
    else if Initialization.absorbs scalar a previous b other then other
    else .intersection left right
  | .written _ previous, _ =>
    if previous = right then right else .intersection left right
  | _, .written _ previous =>
    if left = previous then left else .intersection left right
  | _, _ => .intersection left right

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

/-- Interval traversals of one query. Each visits every node of the history,
and a padded request shares them between its columns. A smaller history never
admits fewer of them, and at most 256, so that one query visits at most
`256 * nodes` nodes: the audit repeats the query for every live read loan, and
the work price of a frame charges each loan about one visit of the history. -/
def initializationQuerySteps : Nat := 256

def initializationSteps (nodes : Nat) : Nat :=
  min initializationQuerySteps (initializationWorkLimit / nodes)

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

/-- Writing an already initialized region does not enlarge its metadata. A
write that continues the run of the last recorded write, at either end, extends
that record instead of adding a node, so that consecutive single-cell writes
leave one run. -/
def Initialization.record (scalar : Scalar) (layout : Layout) (previous : Initialization) : Initialization :=
  if previous.covers scalar layout then previous
  else match previous with
    | .written last older =>
      match last.extend scalar layout with
      | some merged => .written merged older
      | Option.none => .written layout previous
    | _ => .written layout previous

def Initialization.valid (scalar : Scalar) (capacity : Nat) : Initialization → Bool
  | .none => true
  | .written layout previous => checkLayout scalar capacity layout && previous.valid scalar capacity
  | .intersection left right => left.valid scalar capacity && right.valid scalar capacity

end VastitasKernel.Storage
