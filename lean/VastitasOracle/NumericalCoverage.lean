import VastitasOracle.ResourceSource

/-! Converse coverage of the static numerical operations in a public resource
entry, with physical branch/offset, source-call order and nominal origin. -/
namespace VastitasOracle.NumericalCoverage
open VastitasKernel VastitasKernel.Storage VastitasKernel.Storage.NumericalCoverage
open VastitasKernel.ResourceSource (Execution numericalEnvironment)

/-- A selected instruction at an actual position in the nested storage schedule. -/
inductive At : Address → Action → Functions.ScheduleBlock → Nat → List Statement → Prop where
  | here : At (block, p) a block p (.action a :: rest)
  | tail : At address a block (p + 1) rest → At address a block p (s :: rest)
  | yes : At address a ((p, true) :: block) 0 left →
      At address a block p (.branch flag left right :: rest)
  | no : At address a ((p, false) :: block) 0 right →
      At address a block p (.branch flag left right :: rest)

theorem At.mem {keep : Action → Bool} {address a block p code}
    (atPosition : At address a block p code) (selected : keep a = true) :
    (address, a) ∈ entries keep block p code := by
  induction atPosition with
  | here => simp [entries, selected]
  | @tail _ _ _ _ _ s _ ih =>
    cases s with
    | action other => simp only [entries]; split <;> simp_all
    | branch cond left right => simp [entries, ih selected]
  | yes _ ih => simp [entries, ih selected]
  | no _ ih => simp [entries, ih selected]

def environment : Origin → Indexed.Environment
  | .product r => r.environment
  | .network r => r.environment
  | .evaluation r => r.environment
  | .tensor r => r.environment
  | .cached r => r.environment
  | .tree r => r.environment
  | .adjoint r => r.environment
  | .pairing r => r.environment

/-- These are the original prefix and post-emission code snapshots stored in
the dependent receipt, including intermediate actions of composite operations. -/
def history : Origin → List Statement × List Statement
  | .product r => (r.priorCode, r.code)
  | .network r => (r.priorCode, r.code)
  | .evaluation r => (r.priorCode, r.code)
  | .tensor r => (r.priorCode, r.code)
  | .cached r => (r.priorCode, r.code)
  | .tree r => (r.priorCode, r.code)
  | .adjoint r => (r.priorCode, r.code)
  | .pairing r => (r.priorCode, r.code)

theorem original_emission (origin : Origin) :
    origin.slice.address.2 = (history origin).1.length ∧
    (history origin).1 ++ origin.slice.code = (history origin).2 := by
  cases origin <;> rename_i r <;> exact ⟨r.location.start_eq, r.emitted⟩

theorem origin_environment {functions entry env signatures} (e : Execution functions entry env signatures)
    {origin : Origin} (member : origin ∈ origins e.checked.context) : environment origin = env := by
  cases origin with
  | product r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.numericalOrigins.2 r member.1
  | network r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.networkOrigins r member
  | evaluation r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.evaluationOrigins r member
  | tensor r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.tensorContractionOrigins r member
  | cached r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.cachedContractionOrigins r member
  | tree r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.treeOrigins r member
  | adjoint r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.adjointOrigins r member
  | pairing r =>
    simp [origins, -Array.mem_toList_iff] at member
    exact e.diagonalPairingOrigins r member

theorem coverage {functions entry env signatures} (e : Execution functions entry env signatures) :
    (entries required [] 0 e.checked.statements).Perm (recorded e.checked.context) ∧
    sourceTrace functions entry = some (originTrace (origins e.checked.context)) ∧
    slicesMatch e.checked.statements (origins e.checked.context) = true ∧
    (tagged (e.checked.context.networks.toList.map .network)).Perm
      (tagged ((e.checked.context.products.toList.filter (·.networkProduct)).map .product)) := by
  have h := e.numericalCoverage
  simp only [audit, Bool.and_eq_true, and_assoc, decide_eq_true_eq] at h
  exact ⟨sameEntries_perm h.1, h.2.1, h.2.2.1, sameEntries_perm h.2.2.2⟩

theorem full_slice {functions entry env signatures} (e : Execution functions entry env signatures)
    {origin : Origin} (member : origin ∈ origins e.checked.context) (address : Address) (a : Action)
    (inSlice : (address, a) ∈ origin.slice.entries (fun _ => true)) :
    (Std.HashMap.ofList (entries (fun _ => true) [] 0 e.checked.statements))[address]? = some a := by
  have h := (coverage e).2.2.1
  unfold slicesMatch at h
  split at h
  next empty =>
    have noEntries := List.isEmpty_iff.mp empty
    rw [noEntries] at member
    contradiction
  next =>
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h origin member) (address, a) inSlice)

/-- A GEMM, diagonal adjoint or diagonal pairing at any actual position has a
typed receipt at that same position in this public execution. -/
theorem public_action {json requireMain} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry) (address : Address) (a : Action)
    (atPosition : At address a [] 0 (input.checked.execution entry found).checked.statements)
    (selected : required a = true) :
    ∃ origin ∈ origins (input.checked.execution entry found).checked.context,
      (address, a) ∈ origin.slice.entries required ∧
        environment origin = numericalEnvironment input.checked.pureProgram := by
  let e := input.checked.execution entry found
  have present := (coverage e).1.mem_iff.mp (atPosition.mem selected)
  obtain ⟨origin, member, here⟩ := List.mem_flatMap.mp present
  exact ⟨origin, member, here, origin_environment e member⟩

end VastitasOracle.NumericalCoverage
