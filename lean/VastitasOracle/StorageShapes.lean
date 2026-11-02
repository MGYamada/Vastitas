import VastitasKernel.StorageShapeFunctions
import VastitasOracle.StorageRegions

/-! Universal valuation facts for the actual symbolic resource frame. These
theorems concern the existing concrete checker, not native execution or an
alternative sampled-dimension model. -/
namespace VastitasOracle.StorageShapes
open VastitasKernel VastitasKernel.Storage

deriving instance ReflBEq, LawfulBEq for Shapes.Extent
deriving instance ReflBEq, LawfulBEq for Shapes.Layout
deriving instance ReflBEq for Literal

theorem closed_extent_eval (extent : Shapes.Extent) (values : Shapes.Valuation)
    (closed : extent.references = []) : extent.eval values = extent.eval (fun _ => 0) := by
  cases extent <;> simp_all [Shapes.Extent.references, Shapes.Extent.eval]

theorem closed_layout_eval (layout : Shapes.Layout) (values : Shapes.Valuation)
    (closed : layout.references = []) : layout.eval values = layout.eval (fun _ => 0) := by
  rcases layout with ⟨rows, columns, leading, transposed⟩
  cases rows <;> cases columns <;> cases leading <;>
    simp_all [Shapes.Layout.references, Shapes.Extent.references, Shapes.Layout.eval, Shapes.Extent.eval]

/-- A closed arithmetic guard is independent of every runtime valuation. -/
theorem closed_guard_eval (guard : Shapes.Guard) (values : Shapes.Valuation)
    (closed : guard.references = []) : guard.eval values = guard.eval (fun _ => 0) := by
  cases guard with
  | bound extent maximum =>
    simp [Shapes.Guard.eval, closed_extent_eval extent values closed]
  | equal left right =>
    cases left <;> cases right <;>
      simp_all [Shapes.Guard.references, Shapes.Extent.references, Shapes.Guard.eval, Shapes.Extent.eval]
  | layout scalar elements layout =>
    have parts : elements.references = [] ∧ layout.references = [] := by
      simpa [Shapes.Guard.references] using closed
    simp [Shapes.Guard.eval, closed_extent_eval elements values parts.1, closed_layout_eval layout values parts.2]
  | cell layout row column =>
    simp [Shapes.Guard.eval, closed_layout_eval layout values closed]

theorem closed_guard_holds (guard : Shapes.Guard) (values : Shapes.Valuation)
    (closed : guard.references = []) (accepted : guard.closedValid = true) : guard.eval values = true := by
  rw [closed_guard_eval guard values closed]
  simpa [Shapes.Guard.closedValid, closed] using accepted

/-- The actual symbolic checker retains the closed-guard decision together
with the exact executed schedule. Guards containing slots remain conditional. -/
theorem checked_closed_guard {slots : Shapes.Slots} {before : Shapes.Frame} {code : List Shapes.Action}
    (checked : Shapes.Checked slots before code) (guard : Shapes.Guard) (values : Shapes.Valuation)
    (member : guard ∈ before.guards ++ checked.guards) (closed : guard.references = []) :
    guard.eval values = true :=
  closed_guard_holds guard values closed (List.all_eq_true.mp checked.closedGuards guard member)

@[simp] theorem eval_owner (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol) :
    (frame.eval values).owner? name = (frame.owner? name).map (Shapes.Allocation.eval values) := by
  simp [State.owner?, Shapes.Frame.eval, Shapes.Frame.owner?, List.find?_map, Function.comp_def, Shapes.Allocation.eval]

@[simp] theorem eval_allocation (values : Shapes.Valuation) (frame : Shapes.Frame) (id : Nat) :
    (frame.eval values).allocation? id =
      (frame.allocation? id).map (Shapes.Allocation.eval values) := by
  simp [State.allocation?, Shapes.Frame.eval, Shapes.Frame.allocation?, List.find?_map, Function.comp_def, Shapes.Allocation.eval]

@[simp] theorem eval_loan (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol) :
    (frame.eval values).loan? name =
      (frame.loan? name).map (Shapes.Loan.eval values) := by
  simp [State.loan?, Shapes.Frame.eval, Shapes.Frame.loan?, List.find?_map, Function.comp_def, Shapes.Loan.eval]

@[simp] theorem eval_children (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol) :
    (frame.eval values).children name =
      (frame.children name).map (Shapes.Loan.eval values) := by
  simp [State.children, Shapes.Frame.eval, Shapes.Frame.children, List.filter_map, Function.comp_def, Shapes.Loan.eval]

@[simp] theorem eval_suspended (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol) :
    (frame.eval values).suspended name = frame.suspended name := by
  simp [State.suspended, Shapes.Frame.suspended, eval_children]

theorem eval_ancestor (values : Shapes.Valuation) (loans : List Shapes.Loan)
    (fuel name : Nat) (loan : Shapes.Loan) :
    ancestor (loans.map (Shapes.Loan.eval values)) fuel name (loan.eval values) =
      Shapes.ancestor loans fuel name loan := by
  induction fuel generalizing loan with
  | zero => rfl
  | succ fuel ih =>
    simp only [ancestor, Shapes.ancestor, Shapes.Loan.eval]
    cases hp : loan.parent with
    | none => simp
    | some parent =>
      simp only
      split
      · rfl
      · rw [List.find?_map]
        simp only [Function.comp_def, Shapes.Loan.eval]
        cases found : loans.find? (fun l => l.name == parent) with
        | none => rfl
        | some next => simpa only [Option.map_some] using ih next

theorem whole_layout_covers (layout : Storage.Layout) (scalar : Scalar) :
    layout.covers layout scalar = true := by
  have sameOrigin : ((layout.offset - layout.offset) % scalar.width != 0) = false := by simp
  simp only [Storage.Layout.covers, sameOrigin, Bool.false_eq_true, ↓reduceIte]
  split
  · rfl
  · simp only [Nat.lt_irrefl, Nat.sub_self]
    split
    · simp_all
    · split
      · simp
      · cases scalar <;> simp [Scalar.width]

theorem written_covers (layout : Storage.Layout) (scalar : Scalar) :
    (Initialization.written layout .none).covers scalar layout = true := by
  simp [Initialization.covers, Initialization.remaining, Initialization.coversRectangle,
    whole_layout_covers]

/-- Whole-map histories normalize through the implementation's real record
operation. An empty write may leave `.none`; repeated writes need no extra
metadata. Neither case is replaced by a fictitious `.written` constructor. -/
theorem history_forms (values : Shapes.Valuation) (scalar : Scalar)
    (history : Shapes.Initialization) (layout : Shapes.Layout)
    (canonical : history.layouts.all (· == layout) = true) :
    history.eval values scalar = .none ∨
      history.eval values scalar = .written (layout.eval values) .none := by
  induction history with
  | none => exact Or.inl rfl
  | record shape prior ih =>
    simp only [Shapes.Initialization.layouts, List.all_cons, Bool.and_eq_true,
      beq_iff_eq] at canonical
    rcases canonical with ⟨rfl, canonical⟩
    rcases ih canonical with empty | written
    · simp only [Shapes.Initialization.eval, empty, Initialization.record]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · simp [Shapes.Initialization.eval, written, Initialization.record, written_covers]

theorem history_covers (values : Shapes.Valuation) (scalar : Scalar)
    (history : Shapes.Initialization) (layout : Shapes.Layout)
    (canonical : history.layouts.all (· == layout) = true)
    (initialized : history.layouts.isEmpty = false) :
    (history.eval values scalar).covers scalar (layout.eval values) = true := by
  cases history with
  | none => simp [Shapes.Initialization.layouts] at initialized
  | record shape prior =>
    simp only [Shapes.Initialization.layouts, List.all_cons, Bool.and_eq_true,
      beq_iff_eq] at canonical
    rcases canonical with ⟨rfl, canonical⟩
    rcases history_forms values scalar prior shape canonical with empty | written
    · simp only [Shapes.Initialization.eval, empty, Initialization.record]
      split
      · assumption
      · exact written_covers _ _
    · simp [Shapes.Initialization.eval, written, Initialization.record, written_covers]

theorem history_audited (values : Shapes.Valuation) (scalar : Scalar)
    (history : Shapes.Initialization) (layout : Shapes.Layout) (capacity : Nat)
    (canonical : history.layouts.all (· == layout) = true)
    (valid : checkLayout scalar capacity (layout.eval values) = true) :
    ((history.eval values scalar).remaining 4096).isSome = true ∧
      (history.eval values scalar).valid scalar capacity = true := by
  rcases history_forms values scalar history layout canonical with empty | written
  · simp [empty, Initialization.remaining, Initialization.valid]
  · simp [written, Initialization.remaining, Initialization.valid, valid]

theorem frame_layout (values : Shapes.Valuation) (frame : Shapes.Frame)
    (guards : Shapes.guardsHold values frame.guards) (allocation : Shapes.Allocation)
    (live : allocation ∈ frame.allocations) :
    checkLayout allocation.scalar (allocation.elements.eval values * allocation.scalar.width)
      (allocation.layout.eval values) = true := by
  exact guards _ (List.mem_map.mpr ⟨allocation, live, rfl⟩)

theorem allocation_history (frame : Shapes.Frame) (valid : Shapes.auditFrame frame = true)
    (allocation : Shapes.Allocation) (live : allocation ∈ frame.allocations) :
    allocation.initialization.layouts.all (· == allocation.layout) = true := by
  simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at valid
  exact List.all_eq_true.mpr (valid.1.1.2 allocation live).1.1.1.2

theorem loan_valid (values : Shapes.Valuation) (frame : Shapes.Frame)
    (audited : Shapes.auditFrame frame = true)
    (guards : Shapes.guardsHold values frame.guards) (loan : Shapes.Loan)
    (valid : loan.valid frame = true) :
    (loan.eval values).valid (frame.eval values) = true := by
  cases found : frame.allocation? loan.allocation with
  | none => simp [Shapes.Loan.valid, found] at valid
  | some allocation =>
    have live := List.mem_of_find?_eq_some found
    have physical := frame_layout values frame guards allocation live
    have canonical := allocation_history frame audited allocation live
    simp only [Shapes.Loan.valid, found, Bool.and_eq_true] at valid
    have shape : loan.layout = allocation.layout := by simpa using valid.1.1.2
    have initialized : (!loan.access.reads ||
        (allocation.initialization.eval values allocation.scalar).covers allocation.scalar
          (allocation.layout.eval values)) = true := by
      cases reads : loan.access.reads with
      | false => simp
      | true =>
        have written : allocation.initialization.layouts.isEmpty = false := by
          simpa [reads] using valid.1.2
        simpa [reads] using history_covers values allocation.scalar allocation.initialization
          allocation.layout canonical written
    simp only [Loan.valid, Shapes.Loan.eval, eval_allocation, found, Option.map_some,
      Shapes.Allocation.eval, shape]
    simp only [Shapes.Frame.eval, physical, Bool.true_and, initialized, Bool.and_true, Bool.and_eq_true]
    apply And.intro valid.1.1.1
    cases parent : loan.parent with
    | none => simp
    | some name =>
      cases lookup : frame.loan? name with
      | none => simpa [parent, lookup] using valid.2
      | some prior =>
        have before := valid.2
        simp only [parent, lookup, Bool.and_eq_true] at before
        have same : prior.allocation = loan.allocation := by
          simpa only [beq_iff_eq] using before.1.1.1.2
        have parentValid := audited
        simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at parentValid
        have pv := (parentValid.1.2 prior (List.mem_of_find?_eq_some lookup)).2
        simp only [Shapes.Loan.valid, same, found, Bool.and_eq_true] at pv
        have parentShape : prior.layout = allocation.layout := by simpa using pv.1.1.2
        have lookup' := eval_loan values frame name
        simp only [Shapes.Frame.eval] at lookup'
        have ancestry := eval_ancestor values frame.loans frame.loans.length loan.name prior
        simp only [Shapes.Loan.eval, same, parentShape] at ancestry
        simp [lookup', lookup, Shapes.Loan.eval, same, parentShape,
          whole_layout_covers, ancestry, before]

theorem loans_compatible (values : Shapes.Valuation) (frame : Shapes.Frame)
    (left right : Shapes.Loan) (compatible : Shapes.loansCompatible frame left right = true) :
    loansCompatible (frame.eval values) (left.eval values) (right.eval values) = true := by
  simp only [loansCompatible, Shapes.Frame.eval, List.length_map]
  rw [eval_ancestor, eval_ancestor]
  simp only [Shapes.Loan.eval]
  simp only [Shapes.loansCompatible] at compatible
  simp only [compatible, Bool.true_or]

/-- Every accepted symbolic frame realizes an actual audited Storage.State for
every valuation satisfying its emitted physical-layout guards. No sampled
dimension state appears in this implication. -/
theorem frame_audited (values : Shapes.Valuation) (frame : Shapes.Frame)
    (audited : Shapes.auditFrame frame = true)
    (guards : Shapes.guardsHold values frame.guards) :
    auditState (frame.eval values) = true := by
  have original := audited
  simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at audited
  simp only [auditState, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [auditDependencies, Shapes.Frame.eval]
  · exact List.all_eq_true.mpr audited.1.1.1.2
  · apply List.all_eq_true.mpr
    intro actual member
    obtain ⟨allocation, live, rfl⟩ := List.mem_map.mp member
    have attrs := audited.1.1.2 allocation live
    have layout := frame_layout values frame guards allocation live
    have history := history_audited values allocation.scalar allocation.initialization allocation.layout
      (allocation.elements.eval values * allocation.scalar.width)
      (allocation_history frame original allocation live) layout
    have capacity : allocation.elements.eval values * allocation.scalar.width ≤ byteLimit :=
      (of_decide_eq_true layout : Storage.Layout.Valid _ _ _).1
    dsimp only [Shapes.Frame.eval, Shapes.Allocation.eval]
    simp only [Bool.and_eq_true, List.countP_map, Function.comp_def, Shapes.Allocation.eval]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨attrs.1.1.1.1.1.1, decide_eq_true capacity⟩, ?_⟩,
      attrs.1.1.1.1.1.2⟩, history.1⟩, history.2⟩, attrs.1.1.2⟩, attrs.1.2⟩, ?_⟩
    · simp
    · change ((frame.eval values).loan? allocation.owner).isNone = true
      simpa only [eval_loan, Option.isNone_map] using attrs.2
  · apply List.all_eq_true.mpr
    intro actual member
    obtain ⟨loan, live, rfl⟩ := List.mem_map.mp member
    have attrs := audited.1.2 loan live
    simp only [Bool.and_eq_true]
    constructor
    · simpa only [Shapes.Frame.eval, List.countP_map, Function.comp_def, Shapes.Loan.eval] using attrs.1
    · exact loan_valid values frame original guards loan attrs.2
  · apply List.all_eq_true.mpr
    intro left leftLive
    change left ∈ frame.loans.map (Shapes.Loan.eval values) at leftLive
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp leftLive
    apply List.all_eq_true.mpr
    intro right rightLive
    change right ∈ frame.loans.map (Shapes.Loan.eval values) at rightLive
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp rightLive
    exact loans_compatible values frame l r (audited.2 l hl r hr)

theorem fresh_realizes (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol)
    (accepted : Shapes.fresh frame name = .ok ()) :
    freshName (frame.eval values) name = .ok () := by
  by_cases used : name ∈ frame.used
  · simp [Shapes.fresh, used] at accepted
    cases accepted
  · simp [freshName, State.fresh, Shapes.Frame.eval, used]
    rfl

theorem owner_realizes (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol)
    (allocation : Shapes.Allocation) (accepted : Shapes.owner frame name = .ok allocation) :
    owned (frame.eval values) name = .ok (allocation.eval values) := by
  cases found : frame.owner? name with
  | none => simp [Shapes.owner, found] at accepted; cases accepted
  | some data =>
    simp [Shapes.owner, found] at accepted
    have same := Except.ok.inj accepted
    subst allocation
    simp [owned, eval_owner, found]
    rfl

theorem usable_realizes (values : Shapes.Valuation) (frame : Shapes.Frame) (name : Symbol)
    (write : Bool) (loan : Shapes.Loan) (allocation : Shapes.Allocation)
    (accepted : Shapes.usable frame name write = .ok (loan, allocation)) :
    usable (frame.eval values) name write = .ok (loan.eval values, allocation.eval values) := by
  cases found : frame.loan? name with
  | none => simp [Shapes.usable, found] at accepted; cases accepted
  | some actual =>
    cases suspended : frame.suspended name
    · cases writes : write && !actual.access.writes
      · cases reads : !write && !actual.access.reads
        · cases allocated : frame.allocation? actual.allocation with
          | none => simp [Shapes.usable, found, suspended, writes, reads, allocated] at accepted; cases accepted
          | some data =>
            simp [Shapes.usable, found, suspended, writes, reads, allocated] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            simp [usable, eval_loan, eval_allocation, found, allocated, Shapes.Loan.eval,
              eval_suspended, suspended, writes, reads]
            rfl
        · simp [Shapes.usable, found, suspended, writes, reads] at accepted; cases accepted
      · simp [Shapes.usable, found, suspended, writes] at accepted; cases accepted
    · simp [Shapes.usable, found, suspended] at accepted; cases accepted

private theorem unique_selected {α : Type} (items : List α) (predicate : α → Bool)
    (count : items.countP predicate = 1) (a b : α)
    (ha : a ∈ items) (hb : b ∈ items) (pa : predicate a = true) (pb : predicate b = true) : a = b := by
  have length : (items.filter predicate).length = 1 := by
    simpa only [List.countP_eq_length_filter] using count
  obtain ⟨only, singleton⟩ := List.length_eq_one_iff.mp length
  have first := List.mem_filter.mpr ⟨ha, pa⟩
  have second := List.mem_filter.mpr ⟨hb, pb⟩
  simp only [singleton, List.mem_singleton] at first second
  exact first.trans second.symm

theorem allocation_unique (frame : Shapes.Frame) (audited : Shapes.auditFrame frame = true)
    (a b : Shapes.Allocation) (ha : a ∈ frame.allocations) (hb : b ∈ frame.allocations)
    (same : a.identity = b.identity) : a = b := by
  simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at audited
  have count : frame.allocations.countP (·.identity == a.identity) = 1 := by
    simpa only [beq_iff_eq] using (audited.1.1.2 a ha).1.1.2
  exact unique_selected frame.allocations (·.identity == a.identity) count a b ha hb
    (by simp) (by simp [same])

theorem written_realizes (values : Shapes.Valuation) (frame : Shapes.Frame)
    (audited : Shapes.auditFrame frame = true) (allocation : Shapes.Allocation)
    (live : allocation ∈ frame.allocations) :
    (frame.markWritten allocation.identity).eval values =
      (frame.eval values).markWritten allocation.identity (allocation.layout.eval values) := by
  simp only [Shapes.Frame.markWritten, Shapes.Frame.eval, State.markWritten,
    invalidateDependencies, List.map_nil, List.map_map]
  congr 1
  apply List.map_congr_left
  intro current member
  by_cases same : current.identity = allocation.identity
  · have equal := allocation_unique frame audited current allocation member live same
    subst current
    simp [Shapes.Allocation.eval, Shapes.Initialization.eval]
  · simp [Shapes.Allocation.eval, same]

theorem guards_iff (values : Shapes.Valuation) (frame : Shapes.Frame) :
    Shapes.guardsHold values frame.guards ↔
      ∀ allocation ∈ frame.allocations,
        checkLayout allocation.scalar (allocation.elements.eval values * allocation.scalar.width)
          (allocation.layout.eval values) = true := by
  simp [Shapes.guardsHold, Shapes.Frame.guards, Shapes.Guard.eval]

theorem written_guards (values : Shapes.Valuation) (frame : Shapes.Frame) (identity : Nat)
    (guards : Shapes.guardsHold values frame.guards) :
    Shapes.guardsHold values (frame.markWritten identity).guards := by
  rw [guards_iff] at guards ⊢
  intro allocation member
  obtain ⟨prior, live, rfl⟩ := List.mem_map.mp member
  split <;> exact guards prior live

theorem allocation_step (values : Shapes.Valuation) (before : Shapes.Frame)
    (name : Symbol) (scalar : Scalar) (elements : Shapes.Extent) (layout : Shapes.Layout)
    (checked : Shapes.CheckedStep before (.allocate name scalar elements layout))
    (prior : Shapes.guardsHold values before.guards)
    (guards : Shapes.guardsHold values checked.guards) :
    executeAction (before.eval values) (.allocate name scalar (elements.eval values)) =
        .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at guards ⊢
  cases fresh : Shapes.fresh before name with
  | error problem => simp [Shapes.execute, fresh] at accepted; cases accepted
  | ok value =>
    cases value
    simp only [Shapes.execute, fresh, bind, Except.bind, pure, Except.pure] at accepted
    cases accepted
    have physical := guards (.layout scalar elements layout) (by simp)
    have capacity : elements.eval values * scalar.width ≤ byteLimit :=
      (of_decide_eq_true physical : Storage.Layout.Valid _ _ _).1
    constructor
    · have fresh' := fresh_realizes values before name fresh
      simp only [executeAction, fresh', bind, Except.bind, pure, Except.pure]
      simp only [show ¬elements.eval values * scalar.width > byteLimit by omega, ↓reduceIte]
      rfl
    · rw [guards_iff]
      intro allocation member
      rcases List.mem_cons.mp member with equal | live
      · subst allocation
        exact physical
      · exact frame_layout values before prior allocation live

theorem move_step (values : Shapes.Valuation) (before : Shapes.Frame) (source target : Symbol)
    (checked : Shapes.CheckedStep before (.move source target))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (.move source target) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases fresh : Shapes.fresh before target with
  | error problem => simp [Shapes.execute, fresh] at accepted; cases accepted
  | ok value =>
    cases value
    cases owner : Shapes.owner before source with
    | error problem => simp [Shapes.execute, fresh, owner] at accepted; cases accepted
    | ok allocation =>
      cases loans : before.loans.any (·.allocation == allocation.identity)
      · simp only [Shapes.execute, fresh, owner, loans, Bool.false_eq_true, ↓reduceIte,
          bind, Except.bind, pure, Except.pure] at accepted
        cases accepted
        have actualFresh := fresh_realizes values before target fresh
        have actualOwner := owner_realizes values before source allocation owner
        constructor
        · simp only [executeAction, actualFresh, actualOwner, bind, Except.bind, pure, Except.pure]
          simp only [Shapes.Frame.eval, Shapes.Allocation.eval, List.any_map, Function.comp_def, Shapes.Loan.eval,
            loans, Bool.false_eq_true, ↓reduceIte, List.map_map]
          congr 1
          congr 1
          apply List.map_congr_left
          intro current _
          split <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
        · rw [guards_iff]
          intro current member
          obtain ⟨allocation, live, rfl⟩ := List.mem_map.mp member
          split <;> exact frame_layout values before prior allocation live
      · simp only [Shapes.execute, fresh, owner, loans, ↓reduceIte,
          bind, Except.bind, pure, Except.pure] at accepted
        cases accepted

theorem drop_step (values : Shapes.Valuation) (before : Shapes.Frame) (name : Symbol)
    (checked : Shapes.CheckedStep before (.drop name))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (.drop name) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases owner : Shapes.owner before name with
  | error problem => simp [Shapes.execute, owner] at accepted; cases accepted
  | ok allocation =>
    cases loans : before.loans.any (·.allocation == allocation.identity)
    · simp only [Shapes.execute, owner, loans, Bool.false_eq_true, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at accepted
      cases accepted

      have actualOwner := owner_realizes values before name allocation owner
      constructor
      · simp only [executeAction, actualOwner, bind, Except.bind, pure, Except.pure]
        simp only [Shapes.Frame.eval, Shapes.Allocation.eval, List.any_map, Function.comp_def, Shapes.Loan.eval,
          loans, Bool.false_eq_true, ↓reduceIte, List.filter_map, invalidateDependencies, List.map_nil]
      · rw [guards_iff]
        intro current member
        exact frame_layout values before prior current (List.mem_filter.mp member).1
    · simp only [Shapes.execute, owner, loans, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at accepted
      cases accepted

theorem release_step (values : Shapes.Valuation) (before : Shapes.Frame) (name : Symbol)
    (checked : Shapes.CheckedStep before (.release name))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (.release name) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases found : before.loan? name with
  | none => simp [Shapes.execute, found] at accepted; cases accepted
  | some loan =>
    cases suspended : before.suspended name
    · simp only [Shapes.execute, found, Option.isNone_some, suspended, Bool.false_eq_true,
        ↓reduceIte, pure, Except.pure] at accepted
      cases accepted
      constructor
      · simp only [executeAction, releaseTransition, eval_loan, found, Option.map_some,
          Option.isNone_some, eval_suspended, suspended, Bool.false_eq_true, ↓reduceIte,
          pure, Except.pure]
        simp only [Shapes.Frame.eval, List.filter_map, Function.comp_def, Shapes.Loan.eval]
      · exact prior
    · simp only [Shapes.execute, found, Option.isNone_some, suspended, Bool.false_eq_true,
        ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted

theorem usable_origins (frame : Shapes.Frame) (name : Symbol) (write : Bool)
    (loan : Shapes.Loan) (allocation : Shapes.Allocation)
    (accepted : Shapes.usable frame name write = .ok (loan, allocation)) :
    frame.loan? name = some loan ∧ frame.allocation? loan.allocation = some allocation ∧
      frame.suspended name = false ∧ (write && !loan.access.writes) = false ∧
      (!write && !loan.access.reads) = false := by
  cases found : frame.loan? name with
  | none => simp [Shapes.usable, found] at accepted; cases accepted
  | some actual =>
    cases suspended : frame.suspended name
    · cases writes : write && !actual.access.writes
      · cases reads : !write && !actual.access.reads
        · cases allocated : frame.allocation? actual.allocation with
          | none => simp [Shapes.usable, found, suspended, writes, reads, allocated] at accepted; cases accepted
          | some data =>
            simp [Shapes.usable, found, suspended, writes, reads, allocated] at accepted
            rcases accepted with ⟨rfl, rfl⟩
            exact ⟨rfl, allocated, rfl, writes, reads⟩
        · simp [Shapes.usable, found, suspended, writes, reads] at accepted; cases accepted
      · simp [Shapes.usable, found, suspended, writes] at accepted; cases accepted
    · simp [Shapes.usable, found, suspended] at accepted; cases accepted

theorem usable_layout (frame : Shapes.Frame) (audited : Shapes.auditFrame frame = true)
    (name : Symbol) (write : Bool) (loan : Shapes.Loan) (allocation : Shapes.Allocation)
    (accepted : Shapes.usable frame name write = .ok (loan, allocation)) :
    loan.layout = allocation.layout := by
  obtain ⟨found, allocated, _⟩ := usable_origins frame name write loan allocation accepted
  simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at audited
  have valid := (audited.1.2 loan (List.mem_of_find?_eq_some found)).2
  simp only [Shapes.Loan.valid, allocated, Bool.and_eq_true] at valid
  exact eq_of_beq valid.1.1.2

theorem fill_step (values : Shapes.Valuation) (before : Shapes.Frame) (name : Symbol) (value : Literal)
    (checked : Shapes.CheckedStep before (.fill name value))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (.fill name value) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases used : Shapes.usable before name true with
  | error problem => simp [Shapes.execute, used] at accepted; cases accepted
  | ok pair =>
    rcases pair with ⟨loan, allocation⟩
    cases same : value.scalar == allocation.scalar
    · simp only [Shapes.execute, used, same, Bool.false_eq_true, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
    · simp only [Shapes.execute, used, same, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      have actual := usable_realizes values before name true loan allocation used
      have shape := usable_layout before audited name true loan allocation used
      have live := List.mem_of_find?_eq_some (usable_origins before name true loan allocation used).2.1
      constructor
      · simp only [executeAction, actual, bind, Except.bind, pure, Except.pure,
          Shapes.Allocation.eval, Shapes.Loan.eval, bne, same, Bool.not_true, Bool.false_eq_true, ↓reduceIte, shape]
        rw [written_realizes values before audited allocation live]
      · exact written_guards values before allocation.identity prior

theorem owner_origin (frame : Shapes.Frame) (name : Symbol) (allocation : Shapes.Allocation)
    (accepted : Shapes.owner frame name = .ok allocation) : frame.owner? name = some allocation := by
  cases found : frame.owner? name with
  | none => simp [Shapes.owner, found] at accepted; cases accepted
  | some actual =>
    simp only [Shapes.owner, found, pure, Except.pure] at accepted
    have same := Except.ok.inj accepted
    simp only [same]

theorem borrow_owner_step (values : Shapes.Valuation) (before : Shapes.Frame)
    (name owner : Symbol) (access : Access)
    (checked : Shapes.CheckedStep before (.borrow name (.owner owner) access))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (Shapes.action values before (.borrow name (.owner owner) access)) =
        .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases fresh : Shapes.fresh before name with
  | error problem => simp [Shapes.execute, fresh] at accepted; cases accepted
  | ok token =>
    cases token
    cases owned : Shapes.owner before owner with
    | error problem => simp [Shapes.execute, fresh, owned] at accepted; cases accepted
    | ok allocation =>
      let loan : Shapes.Loan := ⟨name, allocation.identity, allocation.layout, access, none⟩
      let next : Shapes.Frame := {before with loans := loan :: before.loans, used := name :: before.used}
      cases reads : access.reads && allocation.initialization.layouts.isEmpty
      · cases compatible : before.loans.all (Shapes.loansCompatible next loan)
        · simp only [Shapes.execute, fresh, owned, reads, compatible, loan, next,
            Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
        · simp only [Shapes.execute, fresh, owned, reads, Bool.false_eq_true, ↓reduceIte,
            bind, Except.bind, pure, Except.pure] at accepted
          rw [ite_eq_left compatible] at accepted
          cases accepted
          have origin := owner_origin before owner allocation owned
          have live := List.mem_of_find?_eq_some origin
          have layout := frame_layout values before prior allocation live
          have canonical := allocation_history before audited allocation live
          have initialized : (access.reads &&
              !(allocation.initialization.eval values allocation.scalar).covers allocation.scalar
                (allocation.layout.eval values)) = false := by
            cases reading : access.reads
            · simp
            · have written : allocation.initialization.layouts.isEmpty = false := by
                simpa [reading] using reads
              simp [history_covers values allocation.scalar allocation.initialization allocation.layout canonical written]
          have aliases : (before.eval values).loans.all
              (loansCompatible (next.eval values) (loan.eval values)) = true := by
            apply List.all_eq_true.mpr
            intro actual member
            obtain ⟨previous, livePrevious, rfl⟩ := List.mem_map.mp member
            exact loans_compatible values next loan previous (List.all_eq_true.mp compatible previous livePrevious)
          constructor
          · have fresh' := fresh_realizes values before name fresh
            have owned' := owner_realizes values before owner allocation owned
            simp only [Shapes.action, origin, Option.map_some, Option.getD_some, executeAction,
              borrowTransition, fresh', owned', bind, Except.bind, pure, Except.pure,
              Shapes.Allocation.eval, layout, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            simp only [initialized, Bool.false_eq_true, ↓reduceIte]
            change (if (!((before.eval values).loans.all
              (loansCompatible (next.eval values) (loan.eval values)))) = true then _
              else (Except.ok (next.eval values) : Except Error State)) = Except.ok (next.eval values)
            simp only [aliases, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          · exact prior
      · simp only [Shapes.execute, fresh, owned, reads, ↓reduceIte,
          bind, Except.bind, pure, Except.pure] at accepted
        cases accepted

theorem borrow_child_step (values : Shapes.Valuation) (before : Shapes.Frame)
    (name parent : Symbol) (access : Access)
    (checked : Shapes.CheckedStep before (.borrow name (.loan parent) access))
    (prior : Shapes.guardsHold values before.guards) :
    executeAction (before.eval values) (Shapes.action values before (.borrow name (.loan parent) access)) =
        .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, emitted, accepted, afterValid⟩
  simp only at ⊢
  cases fresh : Shapes.fresh before name with
  | error problem => simp [Shapes.execute, fresh] at accepted; cases accepted
  | ok token =>
    cases token
    cases found : before.loan? parent with
    | none => simp [Shapes.execute, fresh, found] at accepted; cases accepted
    | some parentLoan =>
      cases allocated : before.allocation? parentLoan.allocation with
      | none => simp [Shapes.execute, fresh, found, allocated] at accepted; cases accepted
      | some allocation =>
        cases writes : access.writes && !parentLoan.access.writes
        · cases readPermission : access.reads && !parentLoan.access.reads
          · let loan : Shapes.Loan := ⟨name, allocation.identity, allocation.layout, access, some parent⟩
            let next : Shapes.Frame := {before with loans := loan :: before.loans, used := name :: before.used}
            cases reads : access.reads && allocation.initialization.layouts.isEmpty
            · cases compatible : before.loans.all (Shapes.loansCompatible next loan)
              · simp only [Shapes.execute, fresh, found, allocated, writes, readPermission,
                  reads, compatible, loan, next, Bool.false_eq_true, ↓reduceIte,
                  bind, Except.bind, pure, Except.pure] at accepted
                cases accepted
              · simp only [Shapes.execute, fresh, found, allocated, writes, readPermission,
                  reads, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
                rw [ite_eq_left compatible] at accepted
                cases accepted
                have live := List.mem_of_find?_eq_some allocated
                have layout := frame_layout values before prior allocation live
                have canonical := allocation_history before audited allocation live
                have audit := audited
                simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at audit
                have parentValid := (audit.1.2 parentLoan (List.mem_of_find?_eq_some found)).2
                simp only [Shapes.Loan.valid, allocated, Bool.and_eq_true] at parentValid
                have parentShape : parentLoan.layout = allocation.layout := eq_of_beq parentValid.1.1.2
                have initialized : (access.reads &&
                    !(allocation.initialization.eval values allocation.scalar).covers allocation.scalar
                      (allocation.layout.eval values)) = false := by
                  cases reading : access.reads
                  · simp
                  · have written : allocation.initialization.layouts.isEmpty = false := by
                      simpa [reading] using reads
                    simp [history_covers values allocation.scalar allocation.initialization allocation.layout canonical written]
                have aliases : (before.eval values).loans.all
                    (loansCompatible (next.eval values) (loan.eval values)) = true := by
                  apply List.all_eq_true.mpr
                  intro actual member
                  obtain ⟨previous, livePrevious, rfl⟩ := List.mem_map.mp member
                  exact loans_compatible values next loan previous (List.all_eq_true.mp compatible previous livePrevious)
                constructor
                · have fresh' := fresh_realizes values before name fresh
                  simp only [Shapes.action, Option.bind_some, Option.map_some,
                    Option.getD_some, executeAction, borrowTransition, fresh', eval_loan, found,
                    bind, Except.bind, pure, Except.pure, Shapes.Loan.eval,
                    eval_allocation, allocated, Option.map_some, Shapes.Allocation.eval,
                    writes, readPermission, Bool.false_eq_true, ↓reduceIte, parentShape,
                    whole_layout_covers, Bool.not_true, layout]
                  simp only [Bool.false_eq_true, ↓reduceIte, initialized]
                  change (if (!((before.eval values).loans.all
                    (loansCompatible (next.eval values) (loan.eval values)))) = true then _
                    else (Except.ok (next.eval values) : Except Error State)) = Except.ok (next.eval values)
                  simp only [aliases, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                · exact prior
            · simp only [Shapes.execute, fresh, found, allocated, writes, readPermission,
                reads, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
              cases accepted
          · simp only [Shapes.execute, fresh, found, allocated, writes, readPermission,
              Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
            cases accepted
        · simp only [Shapes.execute, fresh, found, allocated, writes,
            ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted

theorem cell_covered {layout : Storage.Layout} {scalar : Scalar} {capacity row column : Nat}
    (valid : checkLayout scalar capacity layout = true) (inside : layout.InDomain row column) :
    layout.covers (cellLayout layout scalar row column) scalar = true := by
  obtain ⟨hr, hc⟩ := StorageLayout.physical_indices inside
  have nonempty := StorageLayout.nonempty_of_index inside
  have width : 0 < scalar.width := by cases scalar <;> decide
  have leading : layout.rows ≤ layout.leading := by
    have bound := (StorageLayout.checked_layout valid).2.2.2.2.2.1
    omega
  have rowStride : layout.physicalRow row column * scalar.width < layout.leading * scalar.width :=
    Nat.mul_lt_mul_of_pos_right (by omega) width
  have stridePositive : 0 < layout.leading * scalar.width := by omega
  have difference : (cellLayout layout scalar row column).offset - layout.offset =
      layout.physicalRow row column * scalar.width +
        layout.physicalColumn row column * (layout.leading * scalar.width) := by
    simp only [cellLayout, Layout.address]
    omega
  have aligned : ((cellLayout layout scalar row column).offset - layout.offset) % scalar.width = 0 := by
    rw [difference]
    simp [Nat.add_mod, Nat.mul_mod]
  have remainder : ((cellLayout layout scalar row column).offset - layout.offset) %
      (layout.leading * scalar.width) = layout.physicalRow row column * scalar.width := by
    rw [difference, Nat.add_comm, Nat.mul_add_mod']
    exact Nat.mod_eq_of_lt rowStride
  have quotient : ((cellLayout layout scalar row column).offset - layout.offset) /
      (layout.leading * scalar.width) = layout.physicalColumn row column := by
    rw [difference, Nat.add_comm, Nat.mul_comm (layout.physicalColumn row column),
      Nat.mul_add_div stridePositive]
    simp [Nat.div_eq_of_lt rowStride]
  have notBelow : ¬(cellLayout layout scalar row column).offset < layout.offset := by
    simp only [cellLayout, Layout.address]
    omega
  have cellEmpty : (cellLayout layout scalar row column).empty = false := rfl
  have sameOrigin : (((cellLayout layout scalar row column).offset - layout.offset) %
      scalar.width != 0) = false := by simp [aligned]
  simp only [Layout.covers, cellEmpty, Bool.false_eq_true, ↓reduceIte,
    nonempty, notBelow, decide_false, Bool.or_self, sameOrigin]
  cases contiguous : layout.contiguous
  · dsimp only [cellLayout] at aligned remainder quotient ⊢
    simp only [Bool.false_eq_true, ↓reduceIte, aligned, remainder, quotient,
      Nat.mul_div_cancel _ width, Nat.le_refl, decide_true, Bool.true_or,
      beq_self_eq_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · have mr := Nat.mul_le_mul_right scalar.width (show layout.physicalRow row column ≤ layout.rows - 1 by omega)
    have mc := Nat.mul_le_mul_right (layout.leading * scalar.width)
      (show layout.physicalColumn row column ≤ layout.columns - 1 by omega)
    simp only [↓reduceIte, Layout.endByte, cellEmpty, nonempty, Bool.false_eq_true, ↓reduceIte]
    dsimp only [cellLayout, Layout.address]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero, decide_eq_true_eq]
    omega

theorem readable_covered (values : Shapes.Valuation) (frame : Shapes.Frame)
    (audited : Shapes.auditFrame frame = true) (name : Symbol)
    (loan : Shapes.Loan) (allocation : Shapes.Allocation)
    (accepted : Shapes.usable frame name false = .ok (loan, allocation)) :
    (allocation.initialization.eval values allocation.scalar).covers allocation.scalar
      (allocation.layout.eval values) = true := by
  obtain ⟨found, allocated, _, _, reads⟩ := usable_origins frame name false loan allocation accepted
  have live := List.mem_of_find?_eq_some allocated
  have canonical := allocation_history frame audited allocation live
  simp only [Shapes.auditFrame, Bool.and_eq_true, List.all_eq_true] at audited
  have valid := (audited.1.2 loan (List.mem_of_find?_eq_some found)).2
  have reading : loan.access.reads = true := by simpa using reads
  simp only [Shapes.Loan.valid, allocated, reading, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at valid
  exact history_covers values allocation.scalar allocation.initialization allocation.layout
    canonical (by simpa using valid.1.2)

theorem history_cell (values : Shapes.Valuation) (scalar : Scalar)
    (history : Shapes.Initialization) (layout : Shapes.Layout) (capacity row column : Nat)
    (canonical : history.layouts.all (· == layout) = true)
    (covered : (history.eval values scalar).covers scalar (layout.eval values) = true)
    (valid : checkLayout scalar capacity (layout.eval values) = true)
    (inside : (layout.eval values).InDomain row column) :
    (history.eval values scalar).covers scalar
      (cellLayout (layout.eval values) scalar row column) = true := by
  rcases history_forms values scalar history layout canonical with empty | written
  · have width : 0 < scalar.width := by cases scalar <;> decide
    have byte := StorageRegions.cell_bytes inside width
    have initialized := StorageRegions.initialization_bytes covered byte
    simp only [empty, StorageRegions.Initialized] at initialized
  · simp only [written, Initialization.covers, Initialization.remaining,
      Initialization.coversRectangle, cell_covered valid inside, Bool.true_or]

theorem expect_step (values : Shapes.Valuation) (before : Shapes.Frame)
    (name row column : Nat) (value : Literal)
    (checked : Shapes.CheckedStep before (.expect name row column value))
    (prior : Shapes.guardsHold values before.guards)
    (emitted : Shapes.guardsHold values checked.guards) :
    executeAction (before.eval values) (.expect name row column value) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, guards, accepted, afterValid⟩
  simp only at emitted ⊢
  cases used : Shapes.usable before name false with
  | error problem => simp [Shapes.execute, used] at accepted; cases accepted
  | ok pair =>
    rcases pair with ⟨loan, allocation⟩
    cases same : value.scalar == allocation.scalar
    · simp only [Shapes.execute, used, same, Bool.false_eq_true, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
    · simp only [Shapes.execute, used, same, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      have actual := usable_realizes values before name false loan allocation used
      have shape := usable_layout before audited name false loan allocation used
      have live := List.mem_of_find?_eq_some (usable_origins before name false loan allocation used).2.1
      have physical := frame_layout values before prior allocation live
      have canonical := allocation_history before audited allocation live
      have covered := readable_covered values before audited name loan allocation used
      have inside : (allocation.layout.eval values).InDomain row column := by
        exact of_decide_eq_true (emitted (.cell allocation.layout row column) (by simp))
      have cell := history_cell values allocation.scalar allocation.initialization allocation.layout
        (allocation.elements.eval values * allocation.scalar.width) row column canonical covered physical inside
      constructor
      · simp only [executeAction, actual, bind, Except.bind, pure, Except.pure,
          Shapes.Allocation.eval, Shapes.Loan.eval, bne, same, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, shape, decide_eq_true inside, cell]
      · exact prior

private def literalMatches (scalar : Scalar) : Option Coefficient → Prop
  | none => True
  | some (.literal value) => (value.scalar == scalar) = true
  | some (.loan _) => False

private theorem coefficient_realizes (state : State) (scalar : Scalar) (output : Loan)
    (coefficient : Option Coefficient) (matching : literalMatches scalar coefficient) :
    ∃ checked, checkCoefficient state scalar output coefficient = .ok checked := by
  cases coefficient with
  | none => exact ⟨⟨.default, rfl⟩, by simp [checkCoefficient, coefficientValid, pure, Except.pure, bind, Except.bind]⟩
  | some value =>
    cases value with
    | loan name => exact False.elim matching
    | literal value =>
      have self : (value == value) = true := beq_self_eq_true value
      change (value.scalar == scalar) = true at matching
      refine ⟨⟨.literal value, ?_⟩, ?_⟩
      · simpa only [coefficientValid, self, Bool.true_and] using matching
      · simp only [checkCoefficient, coefficientValid, self, Bool.true_and,
          matching, ↓reduceDIte, bind, Except.bind, pure, Except.pure]

@[simp] theorem logical_rows (values : Shapes.Valuation) (layout : Shapes.Layout) :
    (layout.eval values).logicalRows = layout.logicalRows.eval values := by
  cases h : layout.transposed <;> simp [h, Layout.logicalRows, Shapes.Layout.logicalRows, Shapes.Layout.eval]

@[simp] theorem logical_columns (values : Shapes.Valuation) (layout : Shapes.Layout) :
    (layout.eval values).logicalColumns = layout.logicalColumns.eval values := by
  cases h : layout.transposed <;> simp [h, Layout.logicalColumns, Shapes.Layout.logicalColumns, Shapes.Layout.eval]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem gemm_conditions (before : Shapes.Frame) (request : Gemm)
    (left right output : Shapes.Loan) (a b c : Shapes.Allocation)
    (leftUsed : Shapes.usable before request.left false = .ok (left, a))
    (rightUsed : Shapes.usable before request.right false = .ok (right, b))
    (outputUsed : Shapes.usable before request.output true = .ok (output, c))
    (after : Shapes.Frame) (guards : List Shapes.Guard)
    (accepted : Shapes.execute before (.gemm request) = .ok (after, guards)) :
    (a.scalar == b.scalar && a.scalar == c.scalar) = true ∧
    c.layout.transposed = false ∧ (a.identity == c.identity || b.identity == c.identity) = false ∧
    (request.mode == .accumulate && (!output.access.reads || c.initialization.layouts.isEmpty)) = false ∧
    (request.mode == .overwrite && request.beta.isSome) = false ∧
    literalMatches a.scalar request.alpha ∧ literalMatches a.scalar request.beta ∧
    after = before.markWritten c.identity ∧ guards =
      [.equal a.layout.logicalColumns b.layout.logicalRows,
       .equal c.layout.logicalRows a.layout.logicalRows,
       .equal c.layout.logicalColumns b.layout.logicalColumns] := by
  simp only [Shapes.execute, Shapes.reject, leftUsed, rightUsed, outputUsed,
    bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  next scalars =>
    split at accepted
    · cases accepted
    next transposed =>
      split at accepted
      · cases accepted
      next aliases =>
        split at accepted
        · cases accepted
        next accumulate =>
          split at accepted
          · cases accepted
          next overwrite =>
            refine ⟨scalars, by simpa using transposed, by simpa using aliases,
              by simpa using accumulate, by simpa using overwrite, ?_⟩
            cases alpha : request.alpha <;> cases beta : request.beta
            all_goals repeat first | cases ‹Coefficient›
            all_goals simp only [alpha, beta, List.forIn_cons, List.forIn_nil, bind, Except.bind,
              pure, Except.pure] at accepted
            all_goals repeat first | split at accepted | contradiction
            all_goals simp_all [literalMatches]
            all_goals grind

  · cases accepted

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem gemm_step (values : Shapes.Valuation) (before : Shapes.Frame) (request : Gemm)
    (checked : Shapes.CheckedStep before (.gemm request))
    (prior : Shapes.guardsHold values before.guards)
    (emitted : Shapes.guardsHold values checked.guards) :
    executeAction (before.eval values) (.gemm request) = .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  rcases checked with ⟨audited, after, guards, accepted, afterValid⟩
  simp only at emitted ⊢
  cases leftUsed : Shapes.usable before request.left false with
  | error problem => simp only [Shapes.execute, leftUsed, bind, Except.bind, reduceCtorEq] at accepted
  | ok pair =>
    rcases pair with ⟨left, a⟩
    cases rightUsed : Shapes.usable before request.right false with
    | error problem => simp only [Shapes.execute, leftUsed, rightUsed, bind, Except.bind, reduceCtorEq] at accepted
    | ok pair =>
      rcases pair with ⟨right, b⟩
      cases outputUsed : Shapes.usable before request.output true with
      | error problem => simp only [Shapes.execute, leftUsed, rightUsed, outputUsed, bind, Except.bind, reduceCtorEq] at accepted
      | ok pair =>
        rcases pair with ⟨output, c⟩
        obtain ⟨scalars, transposed, aliases, accumulate, overwrite, alpha, beta, rfl, rfl⟩ :=
          gemm_conditions before request left right output a b c leftUsed rightUsed outputUsed after guards accepted
        obtain ⟨lf, la, ls, _, lr⟩ := usable_origins before request.left false left a leftUsed
        obtain ⟨rf, ra, rs, _, rr⟩ := usable_origins before request.right false right b rightUsed
        obtain ⟨of, oa, os, ow, _⟩ := usable_origins before request.output true output c outputUsed
        have lread : left.access.reads = true := by simpa using lr
        have rread : right.access.reads = true := by simpa using rr
        have owrite : output.access.writes = true := by simpa using ow
        have li : a.identity = left.allocation := by
          have found := List.find?_some la
          exact eq_of_beq found
        have ri : b.identity = right.allocation := by
          have found := List.find?_some ra
          exact eq_of_beq found
        have oi : c.identity = output.allocation := by
          have found := List.find?_some oa
          exact eq_of_beq found
        have ll := usable_layout before audited request.left false left a leftUsed
        have rl := usable_layout before audited request.right false right b rightUsed
        have ol := usable_layout before audited request.output true output c outputUsed
        have lc := readable_covered values before audited request.left left a leftUsed
        have rc := readable_covered values before audited request.right right b rightUsed
        have live := List.mem_of_find?_eq_some oa
        have canonical := allocation_history before audited c live
        have readMode : (request.mode != .accumulate || output.access.reads) = true := by
          cases mode : request.mode <;> simp_all
        have initMode : (request.mode != .accumulate ||
            (c.initialization.eval values c.scalar).covers c.scalar (c.layout.eval values)) = true := by
          cases mode : request.mode
          · simp
          · have both : output.access.reads = true ∧ c.initialization.layouts.isEmpty = false := by simpa [mode] using accumulate
            have initialized := both.2
            simp [history_covers values c.scalar c.initialization c.layout canonical initialized]
        have overwrites : request.mode = .overwrite → request.beta = none := by
          intro mode
          cases beta : request.beta <;> simp_all
        have dims := emitted
        simp only [Shapes.guardsHold, List.mem_cons, List.not_mem_nil, or_false] at dims
        have inner := dims _ (Or.inl rfl)
        have rows := dims _ (Or.inr (Or.inl rfl))
        have columns := dims _ (Or.inr (Or.inr rfl))
        dsimp only [Shapes.Guard.eval] at inner rows columns
        let operands : GemmOperands := ⟨left.eval values, right.eval values, output.eval values,
          a.eval values, b.eval values, c.eval values⟩
        have valid : operands.valid (before.eval values) request = true := by
          dsimp only [operands]
          simp only [GemmOperands.valid, Shapes.Loan.eval, Shapes.Allocation.eval,
            eval_loan, eval_allocation, eval_suspended, lf, rf, of, la, ra, oa,
            Option.map_some, decide_true, ls, rs, os, Bool.not_false, Bool.true_and,
            lread, rread, owrite, readMode, ll, rl, ol, logical_rows, logical_columns,
            inner, rows, columns, initMode, lc, rc]
          simp only [Shapes.Layout.eval, transposed, Bool.not_false]
          have kinds : (a.scalar == b.scalar) = true ∧ (a.scalar == c.scalar) = true := by simpa only [Bool.and_eq_true] using scalars
          have scalarAB := kinds.1
          have scalarAC := kinds.2
          have distinct : (left.allocation != output.allocation) = true ∧
              (right.allocation != output.allocation) = true := by
            simpa [li, ri, oi] using aliases
          simp only [scalarAB, scalarAC, Bool.and_true,
            distinct.1, distinct.2, Bool.true_or]
        obtain ⟨actualAlpha, checkedAlpha⟩ := coefficient_realizes (before.eval values) a.scalar (output.eval values) request.alpha alpha
        obtain ⟨actualBeta, checkedBeta⟩ := coefficient_realizes (before.eval values) a.scalar (output.eval values) request.beta beta
        have actualLeft := usable_realizes values before request.left false left a leftUsed
        have actualRight := usable_realizes values before request.right false right b rightUsed
        have actualOutput := usable_realizes values before request.output true output c outputUsed
        have actual : ∃ result : CheckedGemm (before.eval values) request,
            checkGemm (before.eval values) request = .ok result ∧ result.operands = operands := by
          refine ⟨⟨operands, valid, actualAlpha, actualBeta, overwrites⟩, ?_, rfl⟩
          simp only [checkGemm, actualLeft, actualRight, actualOutput, bind, Except.bind,
            pure, Except.pure]
          dsimp only [operands] at valid
          rw [dite_eq_left valid, dite_eq_left overwrites]
          simp only [Shapes.Allocation.eval, checkedAlpha, checkedBeta]
          rfl

        obtain ⟨result, checkedResult, same⟩ := actual
        constructor
        · simp only [executeAction, checkedResult, bind, Except.bind, pure, Except.pure, same]
          dsimp only [operands, Shapes.Allocation.eval, Shapes.Loan.eval]
          rw [ol, written_realizes values before audited c live]
        · exact written_guards values before c.identity prior

/-- Each accepted symbolic transition realizes the actual concrete checker,
including its independent input/output audits, for every guard valuation. -/
theorem step_realizes (values : Shapes.Valuation) (before : Shapes.Frame)
    (operation : Shapes.Action) (checked : Shapes.CheckedStep before operation)
    (prior : Shapes.guardsHold values before.guards)
    (emitted : Shapes.guardsHold values checked.guards) :
    checkAction (before.eval values) (Shapes.action values before operation) =
        .ok (checked.after.eval values) ∧
      Shapes.guardsHold values checked.after.guards := by
  have executed : executeAction (before.eval values) (Shapes.action values before operation) =
      .ok (checked.after.eval values) ∧ Shapes.guardsHold values checked.after.guards := by
    cases operation with
    | allocate name scalar elements layout => exact allocation_step values before name scalar elements layout checked prior emitted
    | move source target => exact move_step values before source target checked prior
    | drop name => exact drop_step values before name checked prior
    | borrow name source access =>
      cases source with
      | owner owner => exact borrow_owner_step values before name owner access checked prior
      | loan parent => exact borrow_child_step values before name parent access checked prior
    | release name => exact release_step values before name checked prior
    | fill name value => exact fill_step values before name value checked prior
    | expect name row column value => exact expect_step values before name row column value checked prior emitted
    | gemm request => exact gemm_step values before request checked prior emitted
  refine ⟨?_, executed.2⟩
  simp only [checkAction, frame_audited values before checked.beforeValid prior,
    executed.1, frame_audited values checked.after checked.afterValid executed.2, ↓reduceIte]

/-- Acceptance supplies the exact concrete instruction list, not merely a
separately chosen schedule with the same final dimensions. The checker traverses
that entire list with the same fuel and returns precisely the interpreted frame. -/
theorem run_realizes (values : Shapes.Valuation) (fuel : Nat) (before : Shapes.Frame)
    (code : List Shapes.Action) (after : Shapes.Frame) (guards : List Shapes.Guard)
    (accepted : Shapes.run fuel before code = .ok (after, guards))
    (audited : Shapes.auditFrame before = true)
    (prior : Shapes.guardsHold values before.guards)
    (emitted : Shapes.guardsHold values guards) :
    ∃ concrete, Shapes.instantiate values fuel before code = .ok concrete ∧
      Storage.run fuel (before.eval values) concrete = .ok (after.eval values) ∧
      Shapes.guardsHold values after.guards := by
  induction fuel generalizing before code after guards with
  | zero =>
    cases code with
    | nil =>
      simp only [Shapes.run, pure, Except.pure] at accepted
      cases accepted
      exact ⟨[], rfl, rfl, prior⟩
    | cons first rest => simp [Shapes.run, Shapes.reject] at accepted
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [Shapes.run, pure, Except.pure] at accepted
      cases accepted
      exact ⟨[], rfl, rfl, prior⟩
    | cons first rest =>
      cases checked : Shapes.checkStep before first with
      | error problem => simp [Shapes.run, checked, bind, Except.bind] at accepted
      | ok step =>
        cases next : Shapes.run fuel step.after rest with
        | error problem => simp [Shapes.run, checked, next, bind, Except.bind] at accepted
        | ok pair =>
          rcases pair with ⟨tailAfter, tailGuards⟩
          simp only [Shapes.run, checked, next, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
          have firstGuards : Shapes.guardsHold values step.guards := by
            intro guard member
            exact emitted guard (List.mem_append_left _ member)
          have restGuards : Shapes.guardsHold values tailGuards := by
            intro guard member
            exact emitted guard (List.mem_append_right _ member)
          have actual := step_realizes values before first step prior firstGuards
          obtain ⟨tail, instantiated, executed, valid⟩ :=
            ih step.after rest after tailGuards next step.afterValid actual.2 restGuards
          refine ⟨.action (Shapes.action values before first) :: tail, ?_, ?_, valid⟩
          · simp only [Shapes.instantiate, checked, instantiated, bind, Except.bind, pure, Except.pure]
          · simp only [Storage.run, actual.1, bind, Except.bind, executed]

/-- Public checked-template corollary. Slot typing remains in the actual
certificate; the universal valuation premise is exactly the emitted physical
and operation guards, independent of any particular probe or native run. -/
theorem checked_realizes (values : Shapes.Valuation) (slots : Shapes.Slots)
    (before : Shapes.Frame) (code : List Shapes.Action) (checked : Shapes.Checked slots before code)
    (prior : Shapes.guardsHold values before.guards)
    (emitted : Shapes.guardsHold values checked.guards) :
    ∃ concrete, Shapes.instantiate values 4096 before code = .ok concrete ∧
      Storage.run 4096 (before.eval values) concrete = .ok (checked.after.eval values) ∧
      auditState (checked.after.eval values) = true := by
  obtain ⟨concrete, instantiated, executed, guards⟩ :=
    run_realizes values 4096 before code checked.after checked.guards checked.accepted checked.beforeValid prior emitted
  exact ⟨concrete, instantiated, executed, frame_audited values checked.after checked.afterValid guards⟩

/-- Frame topology is audited by each accepted step, including at the empty
suffix. This is a property of the actual run, not an assumed post-state. -/
theorem run_after_audited (fuel : Nat) (before : Shapes.Frame) (code : List Shapes.Action)
    (after : Shapes.Frame) (guards : List Shapes.Guard)
    (accepted : Shapes.run fuel before code = .ok (after, guards))
    (audited : Shapes.auditFrame before = true) : Shapes.auditFrame after = true := by
  induction fuel generalizing before code after guards with
  | zero =>
    cases code with
    | nil =>
      simp only [Shapes.run, pure, Except.pure] at accepted
      cases accepted
      exact audited
    | cons first rest => simp [Shapes.run, Shapes.reject] at accepted
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [Shapes.run, pure, Except.pure] at accepted
      cases accepted
      exact audited
    | cons first rest =>
      cases checked : Shapes.checkStep before first with
      | error problem => simp [Shapes.run, checked, bind, Except.bind] at accepted
      | ok step =>
        cases next : Shapes.run fuel step.after rest with
        | error problem => simp [Shapes.run, checked, next, bind, Except.bind] at accepted
        | ok pair =>
          rcases pair with ⟨tailAfter, tailGuards⟩
          simp only [Shapes.run, checked, next, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
          exact ih step.after rest after tailGuards next step.afterValid

/-- A real call receipt restores all original caller loans and every caller
allocation's identity, owner, scalar and capacity after its exact concrete
schedule. Only actual initialization/version changes may survive. -/
theorem call_realizes (values : Shapes.Valuation) (receipt : Shapes.Functions.CallReceipt)
    (audited : Shapes.auditFrame receipt.before.resources = true)
    (prior : Shapes.guardsHold values receipt.before.resources.guards)
    (emitted : Shapes.guardsHold values receipt.guards) :
    ∃ concrete,
      Shapes.instantiate values 4096 receipt.before.resources receipt.slice = .ok concrete ∧
      Storage.run 4096 (receipt.before.resources.eval values) concrete =
        .ok (receipt.after.resources.eval values) ∧
      auditState (receipt.after.resources.eval values) = true ∧
      (receipt.after.resources.eval values).loans = (receipt.before.resources.eval values).loans ∧
      (receipt.after.resources.eval values).allocations.map (fun a => (a.identity, a.owner, a.scalar, a.capacity)) =
        (receipt.before.resources.eval values).allocations.map (fun a => (a.identity, a.owner, a.scalar, a.capacity)) := by
  obtain ⟨concrete, instantiated, executed, guards⟩ := run_realizes values 4096
    receipt.before.resources receipt.slice receipt.after.resources receipt.guards receipt.replayed audited prior emitted
  have afterValid := run_after_audited 4096 receipt.before.resources receipt.slice
    receipt.after.resources receipt.guards receipt.replayed audited
  refine ⟨concrete, instantiated, executed,
    frame_audited values receipt.after.resources afterValid guards, ?_, ?_⟩
  · simp only [Shapes.Frame.eval, receipt.exited.1]
  · have preserved := congrArg
      (List.map fun a : Nat × Symbol × Scalar × Shapes.Extent × Shapes.Layout =>
        (a.1, a.2.1, a.2.2.1, a.2.2.2.1.eval values * a.2.2.1.width)) receipt.exited.2
    simpa only [Shapes.Frame.eval, List.map_map, Function.comp_def, Shapes.Allocation.eval] using preserved

end VastitasOracle.StorageShapes
