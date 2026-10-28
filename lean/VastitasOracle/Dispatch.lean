import VastitasKernel.Dispatch

/-! Soundness of the actual finite dispatch checker. Candidate optimality is
defined independently of checker execution. The theorem covers all admitted
keys, coverage of the declared domain, and permutation-independent selection;
it does not establish source parsing or native lowering correctness. -/
namespace VastitasOracle.Dispatch
open VastitasKernel.Dispatch

theorem mem_optimalCandidates (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) (method : NormalizedMethod) :
    method ∈ optimalCandidates hierarchy methods key ↔ Optimal hierarchy methods key method := by
  simp only [optimalCandidates, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_false, Bool.and_eq_true, Optimal]
  constructor
  · rintro ⟨member, applies, optimal⟩
    refine ⟨member, applies, ?_⟩
    intro other present applicable
    simpa [applicable] using optimal other present
  · rintro ⟨member, applies, optimal⟩
    refine ⟨member, applies, ?_⟩
    intro other present
    cases appliesOther : applicable hierarchy key other
    · simp
    · simp [optimal other present appliesOther]

theorem optimal_permutation (hierarchy : Hierarchy) {left right : List NormalizedMethod}
    (permutation : left.Perm right) (key : Key) (method : NormalizedMethod) :
    Optimal hierarchy left key method ↔ Optimal hierarchy right key method := by
  constructor
  · rintro ⟨member, applies, optimal⟩
    exact ⟨permutation.mem_iff.mp member, applies,
      fun other present => optimal other (permutation.mem_iff.mpr present)⟩
  · rintro ⟨member, applies, optimal⟩
    exact ⟨permutation.mem_iff.mpr member, applies,
      fun other present => optimal other (permutation.mem_iff.mp present)⟩

theorem selection_permutation (hierarchy : Hierarchy) {left right : List NormalizedMethod}
    (permutation : left.Perm right) (key : Key) (winner : Option Nat) :
    Selection hierarchy left key winner ↔ Selection hierarchy right key winner := by
  cases winner with
  | none =>
      simp only [Selection]
      exact ⟨fun absent method present => absent method
        ((optimal_permutation hierarchy permutation key method).mpr present),
        fun absent method present => absent method
          ((optimal_permutation hierarchy permutation key method).mp present)⟩
  | some id =>
      constructor
      · rintro ⟨method, identity, optimal, unique⟩
        exact ⟨method, identity, (optimal_permutation hierarchy permutation key method).mp optimal,
          fun other present => unique other
            ((optimal_permutation hierarchy permutation key other).mpr present)⟩
      · rintro ⟨method, identity, optimal, unique⟩
        exact ⟨method, identity, (optimal_permutation hierarchy permutation key method).mpr optimal,
          fun other present => unique other
            ((optimal_permutation hierarchy permutation key other).mp present)⟩

theorem selection_unique (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) {left right : Option Nat}
    (first : Selection hierarchy methods key left)
    (second : Selection hierarchy methods key right) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some id => obtain ⟨method, _, optimal, _⟩ := second; exact False.elim (first method optimal)
  | some id =>
      obtain ⟨method, identity, optimal, unique⟩ := first
      cases right with
      | none => exact False.elim (second method optimal)
      | some otherId =>
          obtain ⟨other, otherIdentity, otherOptimal, _⟩ := second
          have equal := unique other otherOptimal
          subst other
          simp [← identity, ← otherIdentity]

theorem candidates_nil_selection (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) (empty : optimalCandidates hierarchy methods key = []) :
    Selection hierarchy methods key none := by
  intro method optimal
  have member := (mem_optimalCandidates hierarchy methods key method).mpr optimal
  simp [empty] at member

theorem candidates_singleton_selection (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) (method : NormalizedMethod)
    (singleton : optimalCandidates hierarchy methods key = [method]) :
    Selection hierarchy methods key (some method.id) := by
  refine ⟨method, rfl, ?_, ?_⟩
  · apply (mem_optimalCandidates hierarchy methods key method).mp
    simp [singleton]
  · intro other optimal
    have member := (mem_optimalCandidates hierarchy methods key other).mpr optimal
    simpa [singleton] using member

/-- The actual row-selection loop validates every key, including those outside
the callable domain. Its output also preserves the entire enumerated key list. -/
theorem selectRows_sound (hierarchy : Hierarchy) (domain : List Key)
    (methods : List NormalizedMethod) (allKeys : List Key) (rows : List Row)
    (accepted : selectRows hierarchy domain methods allKeys = .ok rows) :
    rows.map (·.key) = allKeys ∧ RowsCorrect hierarchy methods rows ∧
      ∀ row ∈ rows, row.key ∈ domain → row.winner.isSome = true := by
  induction allKeys generalizing rows with
  | nil =>
      simp [selectRows, pure, Except.pure] at accepted
      subst rows
      simp [RowsCorrect]
  | cons key rest ih =>
      simp only [selectRows] at accepted
      cases candidates : optimalCandidates hierarchy methods key with
      | nil =>
          simp only [candidates] at accepted
          split at accepted
          · simp [throw, bind, Except.bind] at accepted
          · rename_i outside
            simp only [pure, Except.pure, bind, Except.bind] at accepted
            cases remaining : selectRows hierarchy domain methods rest with
            | error error => simp [remaining] at accepted
            | ok tail =>
                simp [remaining] at accepted
                subst rows
                obtain ⟨keys, correct, covered⟩ := ih tail remaining
                refine ⟨by simp [keys], ?_, ?_⟩
                · intro row member
                  rcases List.mem_cons.mp member with same | member
                  · subst row; exact candidates_nil_selection hierarchy methods key candidates
                  · exact correct row member
                · intro row member inDomain
                  rcases List.mem_cons.mp member with same | member
                  · subst row
                    exact False.elim (outside (by simpa using inDomain))
                  · exact covered row member inDomain
      | cons method remainingCandidates =>
          cases remainingCandidates with
          | nil =>
              simp only [candidates, pure, Except.pure, bind, Except.bind] at accepted
              cases remaining : selectRows hierarchy domain methods rest with
              | error error => simp [remaining] at accepted
              | ok tail =>
                  simp [remaining] at accepted
                  subst rows
                  obtain ⟨keys, correct, covered⟩ := ih tail remaining
                  refine ⟨by simp [keys], ?_, ?_⟩
                  · intro row member
                    rcases List.mem_cons.mp member with same | member
                    · subst row; exact candidates_singleton_selection hierarchy methods key method candidates
                    · exact correct row member
                  · intro row member inDomain
                    rcases List.mem_cons.mp member with same | member
                    · subst row; rfl
                    · exact covered row member inDomain
          | cons other more => simp [candidates, throw, bind, Except.bind] at accepted

theorem validateMethods_sound (hierarchy : Hierarchy) (allKeys : List Key)
    (methods : List NormalizedMethod)
    (accepted : validateMethods hierarchy allKeys methods = .ok ()) :
    (methods.map (·.id)).Nodup ∧
      methods.Pairwise (fun a b => sameSignature a b = false) ∧
      ∀ method ∈ methods, ∃ key ∈ allKeys, applicable hierarchy key method = true := by
  induction methods with
  | nil => simp
  | cons method rest ih =>
      simp only [validateMethods] at accepted
      split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · rename_i ids
        split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · rename_i signatures
          split at accepted
          · simp [throw, bind, Except.bind] at accepted
          · rename_i realizes
            obtain ⟨unique, different, realized⟩ := ih accepted
            have distinct : ∀ other ∈ rest, other.id ≠ method.id := by
              simpa using ids
            have noSignature : rest.find? (sameSignature method) = none := by
              cases found : rest.find? (sameSignature method) with
              | none => rfl
              | some other => exact False.elim (signatures other found)
            have signaturesDistinct : ∀ other ∈ rest, sameSignature method other = false := by
              simpa only [List.find?_eq_none, Bool.not_eq_true] using noSignature
            have realization : ∃ key ∈ allKeys, applicable hierarchy key method = true := by
              simpa using realizes
            refine ⟨?_, List.pairwise_cons.mpr ⟨signaturesDistinct, different⟩, ?_⟩
            · simp only [List.map_cons, List.nodup_cons, List.mem_map]
              exact ⟨by rintro ⟨other, member, equal⟩; exact distinct other member equal, unique⟩
            · intro other member
              rcases List.mem_cons.mp member with same | member
              · subst other; exact realization
              · exact realized other member

/-- Semantic postconditions of the entire reusable checker, including its
normalization result and all method/key pairs used for ground body checking. -/
structure Correct (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (source : List Method) (checked : Checked) : Prop where
  hierarchy_valid : hierarchyValid hierarchy = true
  key_bound : hierarchy.concrete.length ^ arity ≤ VastitasKernel.Limits.dispatchKeys
  enumerated : checked.keys = keys hierarchy.concrete arity
  domain_valid : ∀ key ∈ domain, key ∈ checked.keys
  normalized : source.mapM (normalizeMethod hierarchy arity) = .ok checked.methods
  method_ids : (checked.methods.map (·.id)).Nodup
  signatures : checked.methods.Pairwise (fun a b => sameSignature a b = false)
  realizable : ∀ method ∈ checked.methods, ∃ key ∈ checked.keys, applicable hierarchy key method = true
  row_keys : checked.rows.map (·.key) = checked.keys
  selections : RowsCorrect hierarchy checked.methods checked.rows
  coverage : ∀ row ∈ checked.rows, row.key ∈ domain → row.winner.isSome = true
  pairs : checked.applicablePairs = allApplicablePairs hierarchy checked.methods checked.keys

/-- Success of the actual checker implies the independent candidate contract.
No certificate supplied by the frontend is assumed. -/
theorem checkWith_sound (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (source : List Method) (checked : Checked)
    (accepted : checkWith hierarchy arity domain source = .ok checked) :
    Correct hierarchy arity domain source checked := by
  simp only [checkWith] at accepted
  split at accepted
  · simp [throw, bind, Except.bind] at accepted
  · rename_i valid
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · rename_i bound
      split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · rename_i domainValid
        cases normalized : source.mapM (normalizeMethod hierarchy arity) with
        | error error => simp [normalized, bind, Except.bind] at accepted
        | ok methods =>
            simp only [normalized, bind, Except.bind] at accepted
            cases validated : validateMethods hierarchy (keys hierarchy.concrete arity) methods with
            | error error => simp [validated] at accepted
            | ok result =>
                cases result
                simp only [validated] at accepted
                cases selected : selectRows hierarchy domain methods (keys hierarchy.concrete arity) with
                | error error => simp [selected] at accepted
                | ok rows =>
                    simp [selected, pure, Except.pure] at accepted
                    subst checked
                    obtain ⟨ids, signatures, realizable⟩ := validateMethods_sound hierarchy _ methods validated
                    obtain ⟨rowKeys, selections, coverage⟩ := selectRows_sound hierarchy domain methods _ rows selected
                    exact {
                      hierarchy_valid := by simpa using valid
                      key_bound := by
                        have bounds : ¬arity > VastitasKernel.Limits.dispatchKeys ∧ ¬hierarchy.concrete.length ^ arity > VastitasKernel.Limits.dispatchKeys := by
                          simpa using bound
                        exact Nat.le_of_not_gt bounds.2
                      enumerated := rfl
                      domain_valid := by simpa using domainValid
                      normalized := normalized
                      method_ids := ids
                      signatures := signatures
                      realizable := realizable
                      row_keys := rowKeys
                      selections := selections
                      coverage := coverage
                      pairs := rfl }

theorem check_sound (arity : Nat) (domain : List Key) (source : List Method)
    (checked : Checked) (accepted : check arity domain source = .ok checked) :
    Correct publicHierarchy arity domain source checked := by
  simp only [check] at accepted
  split at accepted
  · contradiction
  · exact checkWith_sound publicHierarchy arity domain source checked accepted

theorem winner_selection (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (source : List Method) (checked : Checked)
    (correct : Correct hierarchy arity domain source checked) (key : Key)
    (admitted : key ∈ checked.keys) :
    Selection hierarchy checked.methods key (checked.winner key) := by
  unfold Checked.winner
  cases found : checked.rows.find? (fun row => row.key == key) with
  | none =>
      obtain ⟨row, member, same⟩ := List.mem_map.mp (correct.row_keys ▸ admitted)
      have absent := List.find?_eq_none.mp found row member
      exact False.elim (absent (by simpa using same))
  | some row =>
      have same : row.key = key := by simpa using List.find?_some found
      simpa [same] using correct.selections row (List.mem_of_find?_eq_some found)

/-- The backend's actual selected ID names the unique optimal method record. -/
theorem winner_sound (arity : Nat) (domain : List Key) (source : List Method)
    (checked : Checked) (accepted : check arity domain source = .ok checked)
    (key : Key) (id : Nat) (selected : checked.winner key = some id) :
    Selection publicHierarchy checked.methods key (some id) := by
  have correct := check_sound arity domain source checked accepted
  unfold Checked.winner at selected
  cases found : checked.rows.find? (fun row => row.key == key) with
  | none => simp [found] at selected
  | some row =>
      simp only [found, Option.bind_some] at selected
      have same : row.key = key := by simpa using List.find?_some found
      simpa [same, selected] using correct.selections row (List.mem_of_find?_eq_some found)

/-- Coverage is about the declared domain; global coherence is stronger and
continues to include keys that the interface does not permit callers to use. -/
theorem domain_coverage (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (source : List Method) (checked : Checked)
    (correct : Correct hierarchy arity domain source checked) (key : Key)
    (declared : key ∈ domain) : ∃ id, checked.winner key = some id := by
  unfold Checked.winner
  cases found : checked.rows.find? (fun row => row.key == key) with
  | none =>
      obtain ⟨row, member, same⟩ := List.mem_map.mp (correct.row_keys ▸ correct.domain_valid key declared)
      have absent := List.find?_eq_none.mp found row member
      exact False.elim (absent (by simpa using same))
  | some row =>
      have same : row.key = key := by simpa using List.find?_some found
      have covered := correct.coverage row (List.mem_of_find?_eq_some found) (same ▸ declared)
      cases winner : row.winner with
      | none => simp [winner] at covered
      | some id => exact ⟨id, by simp [winner]⟩

theorem mapM_success_map {α β ε : Type} [Inhabited β] (f : α → Except ε β)
    (source : List α) (target : List β) (accepted : source.mapM f = .ok target) :
    source.map (fun value => (f value).toOption.getD default) = target := by
  induction source generalizing target with
  | nil => simpa [pure, Except.pure, eq_comm] using accepted
  | cons head rest ih =>
      simp only [List.mapM_cons] at accepted
      cases first : f head with
      | error error => simp [first, bind, Except.bind] at accepted
      | ok value =>
          cases remaining : rest.mapM f with
          | error error => simp [first, remaining, bind, Except.bind] at accepted
          | ok values =>
              simp [first, remaining, bind, Except.bind, pure, Except.pure] at accepted
              subst target
              rw [List.map_cons, ih values remaining]
              simp [first, Except.toOption]

/-- Stable identities travel with method records. Permuting declarations cannot
change any admitted key's selected ID in two successful checks. -/
theorem checkWith_order_independent (hierarchy : Hierarchy) (arity : Nat)
    (domain : List Key) (left right : List Method) (first second : Checked)
    (permutation : left.Perm right)
    (acceptedFirst : checkWith hierarchy arity domain left = .ok first)
    (acceptedSecond : checkWith hierarchy arity domain right = .ok second)
    (key : Key) (admitted : key ∈ keys hierarchy.concrete arity) :
    first.winner key = second.winner key := by
  have firstCorrect := checkWith_sound hierarchy arity domain left first acceptedFirst
  have secondCorrect := checkWith_sound hierarchy arity domain right second acceptedSecond
  have normalizedPerm := permutation.map (fun value =>
    ((normalizeMethod hierarchy arity) value).toOption.getD default)
  rw [mapM_success_map _ _ _ firstCorrect.normalized,
    mapM_success_map _ _ _ secondCorrect.normalized] at normalizedPerm
  have firstSelection := winner_selection hierarchy arity domain left first firstCorrect key
    (firstCorrect.enumerated ▸ admitted)
  have secondSelection := winner_selection hierarchy arity domain right second secondCorrect key
    (secondCorrect.enumerated ▸ admitted)
  exact selection_unique hierarchy second.methods key
    ((selection_permutation hierarchy normalizedPerm key _).mp firstSelection) secondSelection

theorem check_order_independent (arity : Nat) (domain : List Key)
    (left right : List Method) (first second : Checked) (permutation : left.Perm right)
    (acceptedFirst : check arity domain left = .ok first)
    (acceptedSecond : check arity domain right = .ok second)
    (key : Key) (admitted : key ∈ keys publicHierarchy.concrete arity) :
    first.winner key = second.winner key := by
  simp only [check] at acceptedFirst acceptedSecond
  split at acceptedFirst
  · contradiction
  · rename_i within
    rw [ite_eq_right within] at acceptedSecond
    exact checkWith_order_independent publicHierarchy arity domain left right first second
      permutation acceptedFirst acceptedSecond key admitted

theorem optimalCandidates_permutation (hierarchy : Hierarchy)
    {left right : List NormalizedMethod} (permutation : left.Perm right) (key : Key) :
    (optimalCandidates hierarchy left key).Perm (optimalCandidates hierarchy right key) := by
  simp only [optimalCandidates, permutation.any_eq]
  exact permutation.filter _

theorem validateMethods_complete (hierarchy : Hierarchy) (allKeys : List Key)
    (methods : List NormalizedMethod) (unique : (methods.map (·.id)).Nodup)
    (distinct : methods.Pairwise (fun a b => sameSignature a b = false))
    (realizable : ∀ method ∈ methods, ∃ key ∈ allKeys, applicable hierarchy key method = true) :
    validateMethods hierarchy allKeys methods = .ok () := by
  induction methods with
  | nil => rfl
  | cons method rest ih =>
      obtain ⟨idAbsent, ids⟩ := List.nodup_cons.mp unique
      obtain ⟨signatures, others⟩ := List.pairwise_cons.mp distinct
      have noId : rest.any (fun other => other.id == method.id) = false := by
        simp only [List.any_eq_false, beq_iff_eq]
        intro other member same
        exact idAbsent (List.mem_map.mpr ⟨other, member, same⟩)
      have noSignature : rest.find? (sameSignature method) = none := by
        apply List.find?_eq_none.mpr
        intro other member
        simp [signatures other member]
      have realization : allKeys.any (fun key => applicable hierarchy key method) = true := by
        simpa using realizable method (by simp)
      have tail := ih ids others (fun other member => realizable other (by simp [member]))
      simp [validateMethods, noId, noSignature, realization, tail]

theorem selectRows_permutation (hierarchy : Hierarchy) (domain : List Key)
    {left right : List NormalizedMethod} (permutation : left.Perm right)
    (allKeys : List Key) (rows : List Row)
    (accepted : selectRows hierarchy domain left allKeys = .ok rows) :
    selectRows hierarchy domain right allKeys = .ok rows := by
  induction allKeys generalizing rows with
  | nil => simpa only [selectRows] using accepted
  | cons key rest ih =>
      have candidatePermutation := optimalCandidates_permutation hierarchy permutation key
      cases candidates : optimalCandidates hierarchy left key with
      | nil =>
          rw [candidates] at candidatePermutation
          have rightCandidates := candidatePermutation.symm.eq_nil
          simp only [selectRows, candidates] at accepted
          simp only [selectRows, rightCandidates]
          split at accepted
          · simp [throw, bind, Except.bind] at accepted
          · rename_i outside
            simp only [ite_eq_right outside, pure, Except.pure, bind, Except.bind] at accepted ⊢
            cases remaining : selectRows hierarchy domain left rest with
            | error error => simp [remaining] at accepted
            | ok tail =>
                simp [remaining] at accepted
                subst rows
                simp [ih tail remaining]
      | cons method more =>
          cases more with
          | nil =>
              rw [candidates] at candidatePermutation
              have rightCandidates := candidatePermutation.symm.eq_singleton
              simp only [selectRows, candidates, pure, Except.pure, bind, Except.bind] at accepted
              simp only [selectRows, rightCandidates, pure, Except.pure, bind, Except.bind]
              cases remaining : selectRows hierarchy domain left rest with
              | error error => simp [remaining] at accepted
              | ok tail =>
                  simp [remaining] at accepted
                  subst rows
                  simp [ih tail remaining]
          | cons other more => simp [selectRows, candidates, throw, bind, Except.bind] at accepted

theorem mapM_success_each {α β ε : Type} [Inhabited β] (f : α → Except ε β)
    (source : List α) (target : List β) (accepted : source.mapM f = .ok target) :
    ∀ value ∈ source, f value = .ok ((f value).toOption.getD default) := by
  induction source generalizing target with
  | nil => simp
  | cons head rest ih =>
      simp only [List.mapM_cons] at accepted
      cases first : f head with
      | error error => simp [first, bind, Except.bind] at accepted
      | ok value =>
          cases remaining : rest.mapM f with
          | error error => simp [first, remaining, bind, Except.bind] at accepted
          | ok values =>
              intro item member
              rcases List.mem_cons.mp member with same | member
              · subst item; simp [first, Except.toOption]
              · exact ih values remaining item member

theorem mapM_complete {α β ε : Type} (f : α → Except ε β) (g : α → β)
    (source : List α) (success : ∀ value ∈ source, f value = .ok (g value)) :
    source.mapM f = .ok (source.map g) := by
  induction source with
  | nil => rfl
  | cons head rest ih =>
      have first := success head (by simp)
      have tail := ih (fun value member => success value (by simp [member]))
      simp [List.mapM_cons, first, tail, bind, Except.bind, pure, Except.pure]

/-- Reordering records also preserves acceptance, not just the result of two
checks already assumed successful. The exact winner rows are preserved. -/
theorem checkWith_permutation_success (hierarchy : Hierarchy) (arity : Nat)
    (domain : List Key) (left right : List Method) (first : Checked)
    (permutation : left.Perm right)
    (accepted : checkWith hierarchy arity domain left = .ok first) :
    ∃ second, checkWith hierarchy arity domain right = .ok second ∧ second.rows = first.rows := by
  have correct := checkWith_sound hierarchy arity domain left first accepted
  let total := fun value => ((normalizeMethod hierarchy arity) value).toOption.getD default
  let normalized := right.map total
  have normalizeRight : right.mapM (normalizeMethod hierarchy arity) = .ok normalized := by
    apply mapM_complete
    intro value member
    exact mapM_success_each _ _ _ correct.normalized value (permutation.mem_iff.mpr member)
  have normalizedPerm : first.methods.Perm normalized := by
    have perm := permutation.map total
    rw [mapM_success_map _ _ _ correct.normalized] at perm
    exact perm
  have validated : validateMethods hierarchy (keys hierarchy.concrete arity) normalized = .ok () := by
    apply validateMethods_complete
    · exact (normalizedPerm.map (·.id)).nodup_iff.mp correct.method_ids
    · apply correct.signatures.perm normalizedPerm
      intro a b different
      have symmetry : sameSignature b a = sameSignature a b := by
        apply Bool.eq_iff_iff.mpr
        simp only [sameSignature, Bool.and_eq_true, beq_iff_eq]
        exact ⟨fun ⟨one, two⟩ => ⟨one.symm, two.symm⟩,
          fun ⟨one, two⟩ => ⟨one.symm, two.symm⟩⟩
      rw [symmetry]
      exact different
    · intro method member
      obtain ⟨key, admitted, applies⟩ := correct.realizable method (normalizedPerm.mem_iff.mpr member)
      exact ⟨key, correct.enumerated ▸ admitted, applies⟩
  have selected : selectRows hierarchy domain normalized (keys hierarchy.concrete arity) = .ok first.rows := by
    apply selectRows_permutation hierarchy domain normalizedPerm
    simp only [checkWith] at accepted
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · simp only [correct.normalized, bind, Except.bind] at accepted
          cases validation : validateMethods hierarchy (keys hierarchy.concrete arity) first.methods with
          | error error => simp [validation] at accepted
          | ok value =>
              cases value
              simp only [validation] at accepted
              cases selection : selectRows hierarchy domain first.methods (keys hierarchy.concrete arity) with
              | error error => simp [selection] at accepted
              | ok rows =>
                  simp [selection, pure, Except.pure] at accepted
                  have equal := congrArg Checked.rows accepted
                  change rows = first.rows at equal
                  simp only [← equal]
  have bound : ¬(arity > VastitasKernel.Limits.dispatchKeys || hierarchy.concrete.length ^ arity > VastitasKernel.Limits.dispatchKeys) = true := by
    simp only [checkWith] at accepted
    split at accepted
    · simp [throw, bind, Except.bind] at accepted
    · split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · assumption
  have domainValid : domain.all (keys hierarchy.concrete arity).contains = true := by
    simpa only [List.all_eq_true, List.contains_iff_mem, ← correct.enumerated] using correct.domain_valid
  refine ⟨{ keys := keys hierarchy.concrete arity, methods := normalized, rows := first.rows, applicablePairs := allApplicablePairs hierarchy normalized (keys hierarchy.concrete arity) }, ?_, rfl⟩
  simp [checkWith, correct.hierarchy_valid, bound, domainValid, normalizeRight, validated, selected,
    bind, Except.bind, pure, Except.pure]

theorem check_permutation_success (arity : Nat) (domain : List Key)
    (left right : List Method) (first : Checked) (permutation : left.Perm right)
    (accepted : check arity domain left = .ok first) :
    ∃ second, check arity domain right = .ok second ∧ second.rows = first.rows := by
  simp only [check] at accepted
  split at accepted
  · contradiction
  · rename_i within
    obtain ⟨second, checked, rows⟩ :=
      checkWith_permutation_success publicHierarchy arity domain left right first permutation accepted
    exact ⟨second, by simpa only [check, ite_eq_right within] using checked, rows⟩

theorem mem_keys (concrete : List Nat) (arity : Nat) (key : Key) :
    key ∈ keys concrete arity ↔ key.length = arity ∧ ∀ ty ∈ key, ty ∈ concrete := by
  induction arity generalizing key with
  | zero => cases key <;> simp [keys]
  | succ arity ih =>
      cases key with
      | nil => simp [keys]
      | cons head tail =>
          simp only [keys, List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨ty, member, rest, present, same⟩
            cases same
            obtain ⟨length, contains⟩ := (ih tail).mp present
            exact ⟨by simp [length], by simpa using And.intro member contains⟩
          · rintro ⟨length, contains⟩
            refine ⟨head, contains head (by simp), tail, ?_, rfl⟩
            exact (ih tail).mpr ⟨by simpa using length,
              fun ty member => contains ty (by simp [member])⟩

theorem keys_length (concrete : List Nat) (arity : Nat) :
    (keys concrete arity).length = concrete.length ^ arity := by
  induction arity with
  | zero => simp [keys]
  | succ arity ih =>
      have count (items : List Nat) :
          (items.flatMap fun ty => (keys concrete arity).map (ty :: ·)).length =
            items.length * (keys concrete arity).length := by
        induction items with
        | nil => simp
        | cons item rest induct => simp [induct, Nat.add_mul, Nat.add_comm]
      simpa [keys, ih, Nat.pow_succ, Nat.mul_comm] using count concrete

/-- The checked universe is all concrete tuples, not the set of observed calls
or merely the declared domain. Its actual enumeration respects the key bound. -/
theorem check_key_universe (arity : Nat) (domain : List Key) (source : List Method)
    (checked : Checked) (accepted : check arity domain source = .ok checked) :
    checked.keys.length = 4 ^ arity ∧ checked.keys.length ≤ VastitasKernel.Limits.dispatchKeys ∧
      ∀ key, key ∈ checked.keys ↔ key.length = arity ∧ ∀ ty ∈ key, ty ∈ [0, 1, 2, 3] := by
  have correct := check_sound arity domain source checked accepted
  rw [correct.enumerated, keys_length]
  exact ⟨rfl, correct.key_bound, fun key => mem_keys publicHierarchy.concrete arity key⟩

theorem unique_method_identity (methods : List NormalizedMethod)
    (unique : (methods.map (·.id)).Nodup) (first second : NormalizedMethod)
    (firstMember : first ∈ methods) (secondMember : second ∈ methods)
    (sameId : first.id = second.id) : first = second := by
  induction methods with
  | nil => simp at firstMember
  | cons head rest ih =>
      obtain ⟨absent, remaining⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp firstMember with firstEqual | firstMember
      · subst first
        rcases List.mem_cons.mp secondMember with secondEqual | secondMember
        · exact secondEqual.symm
        · exact False.elim (absent (List.mem_map.mpr ⟨second, secondMember, sameId.symm⟩))
      · rcases List.mem_cons.mp secondMember with secondEqual | secondMember
        · subst second
          exact False.elim (absent (List.mem_map.mpr ⟨first, firstMember, sameId⟩))
        · exact ih remaining firstMember secondMember

/-- A selected stable ID cannot name a different method body in the accepted
family, even one which is inapplicable at this particular key. -/
theorem winner_identity_unique (arity : Nat) (domain : List Key) (source : List Method)
    (checked : Checked) (accepted : check arity domain source = .ok checked)
    (key : Key) (id : Nat) (selected : checked.winner key = some id) :
    ∃ method, method.id = id ∧ Optimal publicHierarchy checked.methods key method ∧
      ∀ other ∈ checked.methods, other.id = id → other = method := by
  obtain ⟨method, identity, optimal, _⟩ := winner_sound arity domain source checked accepted key id selected
  refine ⟨method, identity, optimal, ?_⟩
  intro other present same
  exact unique_method_identity checked.methods (check_sound arity domain source checked accepted).method_ids
    other method present optimal.1 (same.trans identity.symm)

/-- Every applicable method/key pair, including losing methods and keys outside
D, is exposed to the backend's ground-body checker. -/
theorem applicablePairs_complete (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (source : List Method) (checked : Checked)
    (correct : Correct hierarchy arity domain source checked) (id : Nat) (key : Key) :
    (id, key) ∈ checked.applicablePairs ↔ key ∈ checked.keys ∧
      ∃ method ∈ checked.methods, method.id = id ∧ applicable hierarchy key method = true := by
  rw [correct.pairs]
  simp only [allApplicablePairs, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨otherKey, admitted, method, ⟨member, applies⟩, identity, sameKey⟩
    subst otherKey
    exact ⟨admitted, method, member, identity, applies⟩
  · rintro ⟨admitted, method, member, identity, applies⟩
    exact ⟨key, admitted, method, ⟨member, applies⟩, identity, rfl⟩

end VastitasOracle.Dispatch
