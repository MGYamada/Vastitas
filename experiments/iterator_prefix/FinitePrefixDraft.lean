import Std
import Lean.Elab.Tactic.Omega

/-!
UNCHECKED LEAN DRAFT for experiments/iterator_prefix/model.py.
Not imported by lean-kernel/ or lean/; not a Vastitas acceptance theorem.

This is an independent, scalar-only abstract cursor/lease model. The intended
invariant concerns one traversal's logical frame ledger, not real memory.
All proof bodies below are candidates: no Lean elaboration or axiom audit has
been run for this file. There are no placeholder axioms or proof holes.
See README.md for the outstanding actual-checker/Core/store obligations.
-/

namespace IteratorPrefixDraft

inductive MapOp where
  | identity | square | add
  deriving DecidableEq, Repr

inductive Predicate where
  | alwaysFalse | alwaysTrue | even | atLeast
  deriving DecidableEq, Repr

def evalMap : MapOp → Nat → Nat → Nat
  | .identity, _, x => x
  | .square, _, x => x * x
  | .add, environment, x => x + environment

def evalPredicate : Predicate → Nat → Nat → Bool
  | .alwaysFalse, _, _ => false
  | .alwaysTrue, _, _ => true
  | .even, _, x => x % 2 == 0
  | .atLeast, environment, x => decide (environment ≤ x)

/-- Pure reusable description. No live capabilities or host callbacks. -/
inductive Plan where
  | countFrom (start stride : Nat)
  | map (op : MapOp) (environment : Nat) (source : Plan)
  | filter (predicate : Predicate) (environment : Nat) (source : Plan)
  | take (limit : Nat) (source : Plan)
  deriving Repr

/-- Residual state; callers access it only through the ownership transition. -/
inductive Cursor where
  | countFrom (nextValue stride : Nat)
  | map (op : MapOp) (environment : Nat) (source : Cursor)
  | filter (predicate : Predicate) (environment : Nat) (source : Cursor)
  | take (remaining : Nat) (source : Cursor)
  deriving Repr

def initialize : Plan → Cursor
  | .countFrom start stride => .countFrom start stride
  | .map op env source => .map op env (initialize source)
  | .filter predicate env source => .filter predicate env (initialize source)
  | .take limit source => .take limit (initialize source)

def Cursor.size : Cursor → Nat
  | .countFrom .. => 1
  | .map _ _ source | .filter _ _ source | .take _ source => source.size + 1

inductive Pulse where
  | yielded (value : Nat) (next : Cursor)
  | skipped (next : Cursor)
  | done
  deriving Repr

/-- Structural recursion on the FINITE cursor, never on the output demand. -/
def pulse : Cursor → Pulse
  | .countFrom x stride => .yielded x (.countFrom (x + stride) stride)
  | .map op env source =>
    match pulse source with
    | .yielded x next => .yielded (evalMap op env x) (.map op env next)
    | .skipped next => .skipped (.map op env next)
    | .done => .done
  | .filter predicate env source =>
    match pulse source with
    | .yielded x next =>
      if evalPredicate predicate env x then
        .yielded x (.filter predicate env next)
      else .skipped (.filter predicate env next)
    | .skipped next => .skipped (.filter predicate env next)
    | .done => .done
  | .take 0 _ => .done
  | .take (remaining + 1) source =>
    match pulse source with
    | .yielded x next => .yielded x (.take remaining next)
    | .skipped next => .skipped (.take (remaining + 1) next)
    | .done => .done

def Pulse.KeepsSize (result : Pulse) (size : Nat) : Prop :=
  match result with
  | .yielded _ next | .skipped next => next.size = size
  | .done => True

theorem pulse_keeps_size (cursor : Cursor) :
    (pulse cursor).KeepsSize cursor.size := by
  induction cursor with
  | countFrom x stride => rfl
  | map op env source ih =>
    cases h : pulse source <;>
      simp_all [pulse, Pulse.KeepsSize, Cursor.size]
  | filter predicate env source ih =>
    cases h : pulse source with
    | yielded x next =>
      by_cases keep : evalPredicate predicate env x = true <;>
        simp_all [pulse, Pulse.KeepsSize, Cursor.size]
    | skipped next => simp_all [pulse, Pulse.KeepsSize, Cursor.size]
    | done => simp_all [pulse, Pulse.KeepsSize, Cursor.size]
  | take remaining source ih =>
    cases remaining with
    | zero => simp [pulse, Pulse.KeepsSize]
    | succ remaining =>
      cases h : pulse source <;>
        simp_all [pulse, Pulse.KeepsSize, Cursor.size]

theorem yielded_size {cursor next : Cursor} {value : Nat}
    (h : pulse cursor = .yielded value next) : next.size = cursor.size := by
  simpa only [h, Pulse.KeepsSize] using pulse_keeps_size cursor

theorem skipped_size {cursor next : Cursor}
    (h : pulse cursor = .skipped next) : next.size = cursor.size := by
  simpa only [h, Pulse.KeepsSize] using pulse_keeps_size cursor

structure Handle where
  run : Nat
  generation : Nat
  deriving DecidableEq, Repr

structure State where
  run : Nat
  generation : Nat
  cursor : Option Cursor
  frames : List Nat       -- local IDs, globally qualified by run
  released : List Nat     -- release events, not a set hiding duplicates
  disposals : Nat
  deriving Repr

def ticket (s : State) : Handle := ⟨s.run, s.generation⟩

def Owns (s : State) (h : Handle) : Prop :=
  h.run = s.run ∧ h.generation = s.generation ∧ ∃ c, s.cursor = some c

/-- Independent ledger property; Step does NOT assume this predicate. -/
def Invariant (s : State) : Prop :=
  s.frames.Nodup ∧
    match s.cursor with
    | some cursor => s.released = [] ∧ s.disposals = 0 ∧
        s.frames.length = cursor.size
    | none => s.released = s.frames ∧ s.disposals = 1

def initial (run : Nat) (plan : Plan) : State :=
  { run, generation := 0, cursor := some (initialize plan),
    frames := List.range (initialize plan).size, released := [], disposals := 0 }

def advance (s : State) (next : Cursor) : State :=
  { s with generation := s.generation + 1, cursor := some next }

def finish (s : State) : State :=
  { s with generation := s.generation + 1, cursor := none,
    released := s.released ++ s.frames, disposals := s.disposals + 1 }

inductive Action where
  | next (handle : Handle)
  | dispose (handle : Handle)
  deriving Repr

def Action.handle : Action → Handle
  | .next h | .dispose h => h

inductive Event where
  | yielded (value : Nat)
  | skipped
  | done
  | cancelled
  deriving Repr

/-- Four operational rules, including explicit cancellation.
The input handle must be this state's current ticket; no rule for a closed state.
-/
inductive Step : State → Action → Event → State → Prop where
  | yielded {s : State} {c next : Cursor} {value : Nat} :
    s.cursor = some c → pulse c = .yielded value next →
    Step s (.next (ticket s)) (.yielded value) (advance s next)
  | skipped {s : State} {c next : Cursor} :
    s.cursor = some c → pulse c = .skipped next →
    Step s (.next (ticket s)) .skipped (advance s next)
  | done {s : State} {c : Cursor} :
    s.cursor = some c → pulse c = .done →
    Step s (.next (ticket s)) .done (finish s)
  | cancelled {s : State} {c : Cursor} :
    s.cursor = some c → Step s (.dispose (ticket s)) .cancelled (finish s)

theorem initial_invariant (run : Nat) (plan : Plan) :
    Invariant (initial run plan) := by
  simp [initial, Invariant]

theorem advance_preserves {s : State} {c next : Cursor}
    (safe : Invariant s) (active : s.cursor = some c)
    (size : next.size = c.size) : Invariant (advance s next) := by
  have parts : s.frames.Nodup ∧ s.released = [] ∧ s.disposals = 0 ∧
      s.frames.length = c.size := by
    simpa [Invariant, active] using safe
  simpa [Invariant, advance, size] using parts

theorem finish_preserves {s : State} {c : Cursor}
    (safe : Invariant s) (active : s.cursor = some c) :
    Invariant (finish s) := by
  have parts : s.frames.Nodup ∧ s.released = [] ∧ s.disposals = 0 ∧
      s.frames.length = c.size := by
    simpa [Invariant, active] using safe
  simp [Invariant, finish, parts.1, parts.2.1, parts.2.2.1]

theorem step_preserves {s t : State} {action : Action} {event : Event}
    (safe : Invariant s) (step : Step s action event t) : Invariant t := by
  cases step with
  | yielded active hp => exact advance_preserves safe active (yielded_size hp)
  | skipped active hp => exact advance_preserves safe active (skipped_size hp)
  | done active _ => exact finish_preserves safe active
  | cancelled active => exact finish_preserves safe active

structure Frame where
  action : Action
  event : Event
  after : State

/-- Every finite operational prefix; no totality or eventual-Yield premise. -/
inductive Prefix : State → List Frame → State → Prop where
  | refl (s : State) : Prefix s [] s
  | cons {s middle last : State} {action : Action} {event : Event} {rest : List Frame} :
    Step s action event middle → Prefix middle rest last →
    Prefix s (⟨action, event, middle⟩ :: rest) last

/-- Intended finite-prefix preservation, including every intermediate state. -/
theorem finite_prefix_preserves {s t : State} {trace : List Frame}
    (execution : Prefix s trace t) :
    Invariant s → Invariant t ∧ ∀ frame ∈ trace, Invariant frame.after := by
  induction execution with
  | refl => intro safe; exact ⟨safe, by simp⟩
  | cons step rest ih =>
    intro safe
    have nextSafe := step_preserves safe step
    obtain ⟨lastSafe, allSafe⟩ := ih nextSafe
    refine ⟨lastSafe, ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with equal | member
    · subst frame; exact nextSafe
    · exact allSafe frame member

theorem step_advances {s t : State} {a : Action} {e : Event}
    (step : Step s a e t) : t.generation = s.generation + 1 := by
  cases step <;> rfl

theorem step_uses_current {s t : State} {a : Action} {e : Event}
    (step : Step s a e t) : a.handle.generation = s.generation := by
  cases step <;> rfl

theorem prefix_generation_monotone {s t : State} {trace : List Frame}
    (execution : Prefix s trace t) : s.generation ≤ t.generation := by
  induction execution with
  | refl => exact Nat.le_refl _
  | cons step rest ih =>
    have advanced := step_advances step
    omega

/-- In particular a Skip invalidates its input ticket forever in this run. -/
theorem consumed_never_owned {s middle last : State} {a : Action} {e : Event}
    {rest : List Frame} (step : Step s a e middle)
    (tail : Prefix middle rest last) : ¬ Owns last a.handle := by
  have used := step_uses_current step
  have advanced := step_advances step
  have later := prefix_generation_monotone tail
  intro owns
  have sameGeneration := owns.2.1
  omega

theorem closed_cannot_step {s t : State} {a : Action} {e : Event}
    (closed : s.cursor = none) (step : Step s a e t) : False := by
  cases step <;> simp_all

/-- Each frame appears once in the release ledger of a closed safe state. -/
theorem closed_released_exactly_once {s : State}
    (safe : Invariant s) (closed : s.cursor = none) :
    s.disposals = 1 ∧ s.released = s.frames ∧ s.released.Nodup := by
  have parts : s.frames.Nodup ∧ s.released = s.frames ∧ s.disposals = 1 := by
    simpa [Invariant, closed] using safe
  exact ⟨parts.2.2, parts.2.1, parts.2.1.symm ▸ parts.1⟩

theorem take_zero_immediate (source : Cursor) :
    pulse (.take 0 source) = .done := rfl

theorem false_filter_skip_keeps_demand (x stride remaining : Nat) :
    pulse (.take (remaining + 1) (.filter .alwaysFalse 0 (.countFrom x stride))) =
      .skipped (.take (remaining + 1)
        (.filter .alwaysFalse 0 (.countFrom (x + stride) stride))) := rfl

end IteratorPrefixDraft
