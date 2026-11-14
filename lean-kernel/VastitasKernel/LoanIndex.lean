import VastitasKernel.FiniteIndex
import VastitasKernel.LoanChain
import Std.Data.HashSet.Lemmas

/-! The executable loan-audit index shared by `Storage.AuditIndex` and
`Shapes.AuditIndex`. A loan type supplies its name, parent and writer
projections and its own per-pair test. The equations hold for every loan
list, including duplicate names, cycles and dangling parents. The chain case
relies only on `Finite.LoanChain.check`. -/
namespace VastitasKernel.Finite.LoanIndex

variable {α : Type} (name : α → Nat) (parent : α → Option Nat)

/-- Compute one bounded ancestry row with indexed parent lookup. A missing
parent is still included, exactly as in the bounded parent walk; validity
rejects the link separately. No acyclicity or uniqueness premise is trusted by
this computation. -/
@[specialize] def lineage (loans : Std.HashMap Nat α) : Nat → α → Std.HashSet Nat
  | 0, _ => {}
  | fuel + 1, loan => match parent loan with
    | none => {}
    | some id =>
      let above := match loans[id]? with
        | none => {}
        | some prior => lineage loans fuel prior
      above.insert id

/-- The parent link of one loan. A missing parent fails, and `accept` checks
the actual parent loan. Unless the chain is proved, the bounded lineage of the
parent must not contain the loan. -/
@[inline] def parentValid (loans : Std.HashMap Nat α) (fuel : Nat) (loan : α) (chain : Bool)
    (accept : Nat → α → Bool) : Bool :=
  match parent loan with
  | none => true
  | some id => match loans[id]? with
    | none => false
    | some prior => accept id prior && (chain || !(lineage parent loans fuel prior).contains (name loan))

abbrev Row (β : Type) := β × Std.HashSet Nat

@[inline] def row (loans : Std.HashMap Nat α) (fuel : Nat) (loan : α) : Row α :=
  (loan, lineage parent loans fuel loan)

variable (writes : α → Bool)

/-- Read/read pairs are unconditionally compatible. All pairs involving a
writer are still checked, retaining both directions even for malformed loan
lists. -/
@[specialize] def pairs (compatible : Row α → Row α → Bool) (rows : List (Row α)) : Bool :=
  let writers := rows.filter (fun entry => writes entry.1)
  rows.all fun left =>
    (if writes left.1 then rows else writers).all (compatible left)

/-- Compare one loan with others. Read/read pairs are omitted as in `pairs`. -/
@[specialize] def scan (compatible : Row α → Row α → Bool) (rowOf : α → Row α) (left : α)
    (others : List α) : Bool :=
  let leftRow := rowOf left
  let relevant := if writes left then others else others.filter writes
  relevant.all fun right => compatible leftRow (rowOf right)

variable {name parent writes}

theorem lineage_contains (loans : List α) (fuel : Nat) (loan : α) (key : Nat) :
    (lineage parent (firstIndex name loans) fuel loan).contains key =
      LoanChain.walk parent (fun id => loans.find? (fun l => name l == id)) fuel key loan := by
  induction fuel generalizing loan with
  | zero => simp [lineage, LoanChain.walk]
  | succ fuel ih =>
    cases edge : parent loan with
    | none => simp [lineage, LoanChain.walk, edge]
    | some id =>
      simp only [lineage, LoanChain.walk, edge, firstIndex_lookup]
      cases found : loans.find? (fun l => name l == id) with
      | none =>
        by_cases same : key = id
        · simp [Std.HashSet.contains_insert, same]
        · simp [Std.HashSet.contains_insert, beq_eq_false_iff_ne.mpr same,
            beq_eq_false_iff_ne.mpr (Ne.symm same)]
      | some prior =>
        simp only [Std.HashSet.contains_insert, ih]
        by_cases same : key = id
        · simp [same]
        · simp [beq_eq_false_iff_ne.mpr same, beq_eq_false_iff_ne.mpr (Ne.symm same)]

/-- On a proved chain the lineage test of a member's parent link is redundant. -/
theorem parentValid_chain {loans : List α} (linked : LoanChain.check name parent loans = true)
    {loan : α} (member : loan ∈ loans) (fuel : Nat) (accept : Nat → α → Bool) :
    parentValid name parent (firstIndex name loans) fuel loan true accept =
      parentValid name parent (firstIndex name loans) fuel loan false accept := by
  unfold parentValid
  cases edge : parent loan with
  | none => rfl
  | some id =>
    dsimp only
    cases resolved : (firstIndex name loans)[id]? with
    | none => rfl
    | some prior =>
      have first : loans.find? (fun l => name l == id) = some prior := by
        simpa only [firstIndex_lookup] using resolved
      have h := LoanChain.acyclic linked member edge first fuel
      simp [lineage_contains, h]

section Reference

variable {loans : Std.HashMap Nat α} {fuel : Nat} {compatible : Row α → Row α → Bool}
  {reference : α → α → Bool}
  (agrees : ∀ left right, compatible (row parent loans fuel left) (row parent loans fuel right) =
    reference left right)
  (reads : ∀ left right, writes left = false → writes right = false → reference left right = true)
include agrees reads

theorem pairs_eq (live : List α) :
    pairs writes compatible (live.map (row parent loans fuel)) =
      live.all (fun left => live.all (reference left)) := by
  simp only [pairs, List.all_map, Function.comp_def]
  congr 1
  funext left
  change (if writes left then live.map (row parent loans fuel)
      else (live.map (row parent loans fuel)).filter (fun entry => writes entry.1)).all
      (compatible (row parent loans fuel left)) = _
  by_cases writer : writes left = true
  · rw [ite_eq_left writer]
    simp only [List.all_map, Function.comp_def]
    exact congrArg live.all (funext (agrees left))
  · rw [ite_eq_right writer]
    have readOnly : writes left = false := Bool.eq_false_iff.mpr writer
    simp only [List.all_filter, List.all_map, Function.comp_def]
    congr 1
    funext right
    change (!writes right || compatible (row parent loans fuel left) (row parent loans fuel right)) = _
    rw [agrees]
    cases rightWrites : writes right
    · simp [reads left right readOnly rightWrites]
    · simp

/-- On a proved chain every pair is compatible, so the pair scan is skipped. -/
theorem checkedPairs {live : List α}
    (chained : LoanChain.check name parent live = true →
      ∀ left ∈ live, ∀ right ∈ live, reference left right = true) :
    (LoanChain.check name parent live || pairs writes compatible (live.map (row parent loans fuel))) =
      live.all (fun left => live.all (reference left)) := by
  rw [pairs_eq agrees reads]
  cases linked : LoanChain.check name parent live with
  | false => rfl
  | true =>
    symm
    exact List.all_eq_true.mpr fun left hl => List.all_eq_true.mpr fun right hr =>
      chained linked left hl right hr

theorem scan_eq (left : α) (others : List α) :
    scan writes compatible (row parent loans fuel) left others = others.all (reference left) := by
  simp only [scan]
  cases writer : writes left
  · simp only [Bool.false_eq_true, ite_false, List.all_filter, agrees]
    congr 1
    funext right
    cases rightWrites : writes right
    · simp [reads left right writer rightWrites]
    · simp
  · simp only [ite_true, agrees]

end Reference

end VastitasKernel.Finite.LoanIndex
