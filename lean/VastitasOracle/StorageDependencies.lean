import VastitasKernel.StorageFunctions

/-! Provenance of live dependency entries through the actual accepted storage
schedule. Dependencies describe logical versions/layouts, not packing semantics
or native-memory refinement. -/
namespace VastitasOracle.StorageDependencies
open VastitasKernel.Storage

def LiveEntry (state : State) (name : Symbol) (dependency : Dependency) : Prop :=
  ⟨name, some dependency⟩ ∈ state.dependencies

private theorem execute_of_checked {before after : State} {action : Action}
    (accepted : checkAction before action = .ok after) :
    executeAction before action = .ok after := by
  unfold checkAction at accepted
  split at accepted
  · split at accepted
    · contradiction
    next result step =>
      split at accepted
      · cases accepted
        exact step
      · contradiction
  · contradiction

private theorem invalidation_backwards {entries : List DependencyEntry}
    {allocation name : Nat} {dependency : Dependency}
    (live : (⟨name, some dependency⟩ : DependencyEntry) ∈ invalidateDependencies entries allocation) :
    (⟨name, some dependency⟩ : DependencyEntry) ∈ entries := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp live
  split at same
  · have impossible := congrArg DependencyEntry.value same
    contradiction
  · exact same ▸ member

private theorem written_backwards {state : State} {allocation : Nat} {layout : Layout}
    {name : Symbol} {dependency : Dependency}
    (live : LiveEntry (state.markWritten allocation layout) name dependency) :
    LiveEntry state name dependency :=
  invalidation_backwards live

theorem action_live_origin {before after : State} {action : Action}
    {name : Symbol} {dependency : Dependency}
    (accepted : checkAction before action = .ok after)
    (live : LiveEntry after name dependency) :
    LiveEntry before name dependency ∨
      ∃ source target, action = .captureDependency name source target := by
  have executed := execute_of_checked accepted
  cases action <;> simp only [executeAction, Bind.bind, Except.bind] at executed
  all_goals repeat' (split at executed <;> try simp_all only [reduceCtorEq])
  all_goals try (have same := Except.ok.inj executed; subst after)
  all_goals try contradiction
  all_goals first
    | exact Or.inl live
    | exact Or.inl (written_backwards live)
    | exact Or.inl (invalidation_backwards live)
    | exact Or.inl (List.mem_filter.mp live).1
    | grind [LiveEntry]


theorem join_has_no_live_entry {left right after : State}
    (accepted : join left right = .ok after) (name : Symbol) (dependency : Dependency) :
    ¬ LiveEntry after name dependency := by
  unfold join at accepted
  simp only [Bind.bind, Except.bind] at accepted
  repeat' (split at accepted <;> try simp_all only [reduceCtorEq])
  all_goals try contradiction
  all_goals have same := Except.ok.inj accepted
  all_goals subst after
  all_goals
    intro live
    obtain ⟨entry, _, same⟩ := List.mem_map.mp live
    have impossible := congrArg DependencyEntry.value same
    contradiction

/-- Every statement in this suffix is an actual accepted action, and the same
live dependency is present at every intermediate state. There is no join step. -/
inductive LivePath (name : Symbol) (dependency : Dependency) :
    State → List Statement → State → Prop where
  | nil (live : LiveEntry state name dependency) : LivePath name dependency state [] state
  | step (live : LiveEntry before name dependency)
      (accepted : checkAction before action = .ok after)
      (rest : LivePath name dependency after statements finalState) :
      LivePath name dependency before (.action action :: statements) finalState

theorem LivePath.start {name dependency before statements after}
    (path : LivePath name dependency before statements after) : LiveEntry before name dependency := by
  cases path with
  | nil live => exact live
  | step live _ _ => exact live

/-- A live entry at the end of this exact accepted run either survived from its
input, or came from an actual capture in this very statement list. Its suffix
has no joins and preserves the same live entry action by action. -/
theorem run_live_origin {fuel : Nat} {before after : State} {statements : List Statement}
    {name : Symbol} {dependency : Dependency}
    (accepted : run fuel before statements = .ok after)
    (live : LiveEntry after name dependency) :
    LivePath name dependency before statements after ∨
      ∃ earlier suffix source target captureBefore captureAfter,
        statements = earlier ++ .action (.captureDependency name source target) :: suffix ∧
        run fuel before earlier = .ok captureBefore ∧
        checkAction captureBefore (.captureDependency name source target) = .ok captureAfter ∧
        LivePath name dependency captureAfter suffix after := by
  induction fuel generalizing before after statements with
  | zero =>
    cases statements with
    | nil =>
      cases accepted
      exact Or.inl (.nil live)
    | cons statement rest => contradiction
  | succ fuel ih =>
    cases statements with
    | nil =>
      cases accepted
      exact Or.inl (.nil live)
    | cons statement rest =>
      cases statement with
      | action action =>
        cases step : checkAction before action with
        | error diagnostic => simp [run, step, Bind.bind, Except.bind] at accepted
        | ok next =>
          have tail : run fuel next rest = .ok after := by simpa only [run, step, Bind.bind, Except.bind] using accepted
          rcases ih tail live with path | ⟨earlier, suffix, source, target, a, b, shape, pre, capture, path⟩
          · rcases action_live_origin step path.start with prior | ⟨source, target, rfl⟩
            · exact Or.inl (.step prior step path)
            · exact Or.inr ⟨[], rest, source, target, before, next, rfl, rfl, step, path⟩
          · refine Or.inr ⟨.action action :: earlier, suffix, source, target, a, b, ?_, ?_, capture, path⟩
            · simp [shape]
            · simpa only [run, step, Bind.bind, Except.bind] using pre
      | branch condition yes no =>
        cases first : run fuel before yes with
        | error diagnostic => simp [run, first, Bind.bind, Except.bind] at accepted
        | ok left =>
          cases second : run fuel {before with nextAllocation := left.nextAllocation} no with
          | error diagnostic => simp [run, first, second, Bind.bind, Except.bind] at accepted
          | ok right =>
            cases merged : join left right with
            | error diagnostic => simp [run, first, second, merged, Bind.bind, Except.bind] at accepted
            | ok next =>
              have tail : run fuel next rest = .ok after := by
                simpa only [run, first, second, merged, Bind.bind, Except.bind] using accepted
              rcases ih tail live with path | ⟨earlier, suffix, source, target, a, b, shape, pre, capture, path⟩
              · exact False.elim (join_has_no_live_entry merged name dependency path.start)
              · refine Or.inr ⟨.branch condition yes no :: earlier, suffix, source, target, a, b, ?_, ?_, capture, path⟩
                · simp [shape]
                · simpa only [run, first, second, merged, Bind.bind, Except.bind] using pre

private theorem checked_after_valid {before after : State} {action : Action}
    (accepted : checkAction before action = .ok after) : auditState after = true := by
  unfold checkAction at accepted
  split at accepted
  · split at accepted
    · contradiction
    next result step =>
      split at accepted
      next valid => cases accepted; exact valid
      · contradiction
  · contradiction

theorem action_used_mono {before after : State} {action : Action} {name : Symbol}
    (accepted : checkAction before action = .ok after)
    (used : name ∈ before.used) : name ∈ after.used := by
  have executed := execute_of_checked accepted
  cases action <;> simp only [executeAction, Bind.bind, Except.bind] at executed
  all_goals repeat' (split at executed <;> try simp_all only [reduceCtorEq])
  all_goals try (have same := Except.ok.inj executed; subst after)
  all_goals try contradiction
  all_goals first
    | exact used
    | exact List.mem_cons_of_mem _ used

theorem capture_used {before after : State} {name source target : Symbol}
    (accepted : checkAction before (.captureDependency name source target) = .ok after) :
    after.used = name :: before.used := by
  have executed := execute_of_checked accepted
  simp only [executeAction, Bind.bind, Except.bind] at executed
  repeat' (split at executed <;> try simp_all only [reduceCtorEq])
  all_goals try contradiction
  all_goals have same := Except.ok.inj executed
  all_goals subst after
  all_goals rfl

/-- The actual capture cannot reuse even a forgotten or tombstoned handle. -/
theorem capture_fresh {before after : State} {name source target : Symbol}
    (accepted : checkAction before (.captureDependency name source target) = .ok after) :
    name ∉ before.used := by
  have valid := checked_after_valid accepted
  have shape := capture_used accepted
  have unique : after.used.all (fun n => after.used.count n == 1) = true := by
    simp only [auditState, Bool.and_eq_true] at valid
    exact valid.1.1.1.2
  have counted := List.all_eq_true.mp unique name (shape ▸ List.mem_cons_self)
  rw [shape] at counted
  exact List.not_mem_of_count_eq_zero (by simpa using counted)

private theorem join_used_left {left right after : State} {name : Symbol}
    (accepted : join left right = .ok after) (used : name ∈ left.used) :
    name ∈ after.used := by
  unfold join at accepted
  simp only [Bind.bind, Except.bind] at accepted
  repeat' (split at accepted <;> try simp_all only [reduceCtorEq])
  all_goals try contradiction
  all_goals have same := Except.ok.inj accepted
  all_goals subst after
  all_goals exact List.mem_append_left _ used

theorem run_used_mono {fuel : Nat} {before after : State} {statements : List Statement}
    {name : Symbol} (accepted : run fuel before statements = .ok after)
    (used : name ∈ before.used) : name ∈ after.used := by
  induction fuel generalizing before after statements with
  | zero =>
    cases statements with
    | nil => cases accepted; exact used
    | cons statement rest => contradiction
  | succ fuel ih =>
    cases statements with
    | nil => cases accepted; exact used
    | cons statement rest =>
      cases statement with
      | action action =>
        cases step : checkAction before action with
        | error diagnostic => simp [run, step, Bind.bind, Except.bind] at accepted
        | ok next =>
          have tail : run fuel next rest = .ok after := by
            simpa only [run, step, Bind.bind, Except.bind] using accepted
          exact ih tail (action_used_mono step used)
      | branch condition yes no =>
        cases first : run fuel before yes with
        | error diagnostic => simp [run, first, Bind.bind, Except.bind] at accepted
        | ok left =>
          cases second : run fuel {before with nextAllocation := left.nextAllocation} no with
          | error diagnostic => simp [run, first, second, Bind.bind, Except.bind] at accepted
          | ok right =>
            cases merged : join left right with
            | error diagnostic => simp [run, first, second, merged, Bind.bind, Except.bind] at accepted
            | ok next =>
              have tail : run fuel next rest = .ok after := by
                simpa only [run, first, second, merged, Bind.bind, Except.bind] using accepted
              exact ih tail (join_used_left merged (ih first used))

/-- Once a name has entered the actual used-name ledger, a later live entry
under that name must have survived every action; it cannot be recaptured. -/
theorem run_existing_live_path {fuel : Nat} {before after : State} {statements : List Statement}
    {name : Symbol} {dependency : Dependency}
    (accepted : run fuel before statements = .ok after)
    (used : name ∈ before.used) (live : LiveEntry after name dependency) :
    LivePath name dependency before statements after := by
  rcases run_live_origin accepted live with path | ⟨_, _, _, _, _, _, _, pre, capture, _⟩
  · exact path
  · exact False.elim (capture_fresh capture (run_used_mono pre used))

/-- Tombstoning or forgetting a handle cannot be undone later in an accepted
schedule: no entry with any dependency payload can reappear under that name. -/
theorem run_no_resurrection {fuel : Nat} {before after : State} {statements : List Statement}
    {name : Symbol} {dependency : Dependency}
    (accepted : run fuel before statements = .ok after)
    (used : name ∈ before.used) (absent : ¬ LiveEntry before name dependency) :
    ¬ LiveEntry after name dependency := by
  intro live
  exact absent (run_existing_live_path accepted used live).start

/-- Lookup evidence used by the actual tensor checker denotes a real table entry. -/
theorem selected_live {state : State} {name : Symbol} {dependency : Dependency}
    (selected : state.dependency? name = some ⟨name, some dependency⟩) :
    LiveEntry state name dependency :=
  List.mem_of_find?_eq_some selected

/-- Successful require is read-only and selects an actually live, valid stamp. -/
theorem require_live {before after : State} {name : Symbol}
    (accepted : checkAction before (.requireDependency name) = .ok after) :
    after = before ∧ ∃ dependency, LiveEntry before name dependency ∧ dependency.valid before = true := by
  have executed := execute_of_checked accepted
  cases found : before.dependency? name with
  | none => simp [executeAction, found] at executed; contradiction
  | some entry =>
    cases value : entry.value with
    | none => simp [executeAction, found, value] at executed; contradiction
    | some dependency =>
      have named : entry.name = name := by
        have namedEntry := List.find?_some found
        simpa using namedEntry
      have same : entry = ⟨name, some dependency⟩ := by cases entry; simp_all
      by_cases valid : dependency.valid before = true
      · have unchanged : before = after := by
          simp [executeAction, found, value, valid] at executed
          exact Except.ok.inj executed
        exact ⟨unchanged.symm, dependency, selected_live (same ▸ found), valid⟩
      · simp [executeAction, found, value, valid] at executed
        contradiction

theorem invalidation_kills {entries : List DependencyEntry} {allocation name : Nat}
    {dependency : Dependency} (mentioned : dependency.mentions allocation = true) :
    (⟨name, some dependency⟩ : DependencyEntry) ∉ invalidateDependencies entries allocation := by
  intro live
  obtain ⟨entry, _, same⟩ := List.mem_map.mp live
  split at same
  · have impossible := congrArg DependencyEntry.value same
    contradiction
  next untouched =>
    rw [same] at untouched
    simp [mentioned] at untouched

/-- Every logical write invalidates both sides of a captured dependency,
including writes to a disjoint subregion of the same allocation. -/
theorem written_kills {state : State} {allocation : Nat} {layout : Layout}
    {name : Symbol} {dependency : Dependency}
    (mentioned : dependency.mentions allocation = true) :
    ¬ LiveEntry (state.markWritten allocation layout) name dependency :=
  invalidation_kills mentioned

/-- Provenance from the exact accepted source-list prefix. The capture and live
suffix are part of that list, not independently postulated before/after states. -/
def CapturedHistory (fuel : Nat) (before : State) (statements : List Statement)
    (after : State) (name : Symbol) (dependency : Dependency) : Prop :=
  ∃ earlier suffix source target captureBefore captureAfter,
    statements = earlier ++ .action (.captureDependency name source target) :: suffix ∧
    run fuel before earlier = .ok captureBefore ∧
    checkAction captureBefore (.captureDependency name source target) = .ok captureAfter ∧
    LivePath name dependency captureAfter suffix after

theorem run_from_empty_live_history {fuel : Nat} {after : State} {statements : List Statement}
    {name : Symbol} {dependency : Dependency}
    (accepted : run fuel {} statements = .ok after)
    (live : LiveEntry after name dependency) :
    CapturedHistory fuel {} statements after name dependency := by
  rcases run_live_origin accepted live with path | history
  · have impossible := path.start
    simp [LiveEntry] at impossible
  · exact history

/-- At an actual accepted require after an exact prefix from the empty state,
the selected dependency traces to an earlier accepted capture in that prefix.
The suffix preserves its exact entry at every action and contains no join.
This statement does not assume that a branch-local receipt replays from `{}`. -/
theorem require_prefix_history {fuel : Nat} {statements : List Statement} {before after : State}
    {name : Symbol} (executed : run fuel {} statements = .ok before)
    (required : checkAction before (.requireDependency name) = .ok after) :
    after = before ∧ ∃ dependency, dependency.valid before = true ∧
      CapturedHistory fuel {} statements before name dependency := by
  obtain ⟨same, dependency, live, valid⟩ := require_live required
  exact ⟨same, dependency, valid, run_from_empty_live_history executed live⟩

/-- An actual checked packed cache and actual checked consumer connected by
this accepted intervening schedule have the same live dependency throughout.
The cache itself carries accepted nominal packing and post-pack capture; a raw
storage dependency alone cannot manufacture those certificates. -/
theorem cached_consumer_history {environment numerical resources values left right output policy}
    (cache : VastitasKernel.Storage.Tensor.Cache)
    (consumer : VastitasKernel.Storage.Tensor.CheckedCachedContraction environment numerical
      resources values cache left right output policy)
    {fuel : Nat} {intervening : List Statement}
    (executed : run fuel cache.after intervening = .ok resources) :
    LivePath cache.name cache.dependency cache.after intervening resources := by
  have used : cache.name ∈ cache.after.used := by rw [capture_used cache.captured]; simp
  exact run_existing_live_path executed used (selected_live consumer.dependency)

/-- Receipt connection with an explicit replay premise. `priorCode` is reset at
branch entry, so this premise is deliberately not claimed for all receipts. -/
theorem receipt_prefix_history (receipt : VastitasKernel.Storage.Functions.CachedContractionReceipt)
    {fuel : Nat} (executed : run fuel {} receipt.priorCode = .ok receipt.before) :
    CapturedHistory fuel {} receipt.priorCode receipt.before receipt.cache.name receipt.cache.dependency :=
  run_from_empty_live_history executed (selected_live receipt.checked.dependency)

/-- An actual right-arm prefix uses precisely the allocator reseed performed by
`Storage.run`, after validating the left arm. Left-arm mutations do not become
right-arm mutations: only `nextAllocation` is inherited from its result. -/
structure RightBranchPrefix (fuel : Nat) (before : State) (yes rightEarlier : List Statement)
    (after : State) where
  left : State
  leftAccepted : run fuel before yes = .ok left
  rightAccepted : run fuel {before with nextAllocation := left.nextAllocation} rightEarlier = .ok after

/-- A cache inherited by a right arm has actual history before the branch and
through that arm's accepted prefix, despite the administrative allocator reseed.
As with `cached_consumer_history` for the left arm, the prefix is an explicit
hypothesis; extraction of such prefixes from arbitrary nested source receipts
is a separate source-checker correspondence obligation. -/
theorem cached_consumer_right_prefix_history
    {environment numerical resources values left right output policy}
    (cache : VastitasKernel.Storage.Tensor.Cache)
    (consumer : VastitasKernel.Storage.Tensor.CheckedCachedContraction environment numerical
      resources values cache left right output policy)
    {earlierFuel branchFuel : Nat} {beforeBranch : State}
    {earlier yes rightEarlier : List Statement}
    (executed : run earlierFuel cache.after earlier = .ok beforeBranch)
    (branch : RightBranchPrefix branchFuel beforeBranch yes rightEarlier resources) :
    LivePath cache.name cache.dependency cache.after earlier beforeBranch ∧
    LivePath cache.name cache.dependency
      {beforeBranch with nextAllocation := branch.left.nextAllocation} rightEarlier resources := by
  have used : cache.name ∈ cache.after.used := by rw [capture_used cache.captured]; simp
  have beforeUsed := run_used_mono executed used
  have rightPath := run_existing_live_path branch.rightAccepted beforeUsed (selected_live consumer.dependency)
  exact ⟨run_existing_live_path executed used rightPath.start, rightPath⟩

/-- The same explicit inherited-prefix result for actual public checker receipts. -/
theorem receipt_cached_history (receipt : VastitasKernel.Storage.Functions.CachedContractionReceipt)
    {fuel : Nat} {intervening : List Statement}
    (executed : run fuel receipt.cache.after intervening = .ok receipt.before) :
    LivePath receipt.cache.name receipt.cache.dependency receipt.cache.after intervening receipt.before :=
  cached_consumer_history receipt.cache receipt.checked executed

end VastitasOracle.StorageDependencies
