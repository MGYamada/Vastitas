import VastitasKernel.MidIR.PackageObservation
import VastitasOracle.IndexedFunctions
import VastitasOracle.MidIR

set_option autoImplicit false

namespace VastitasOracle.PackageLink
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.MidIR.PackageLink
open Core.Semantics

private theorem same_mapM {α β : Type} (xs : List α) (f g : α → Option β)
    (agree : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, agree x (by simp), ih (by intro y h; exact agree y (by simp [h]))]

private theorem lookup_retained (m : Core.Module) (ids : Array Nat) (id : Nat)
    (keep : ids.contains id = true) :
    (selected m ids).functions.find? (·.id == id) = m.functions.find? (·.id == id) := by
  simp only [selected, List.find?_filter]
  congr 1
  funext f
  have member : id ∈ ids := by simpa using keep
  by_cases h : f.id = id <;> simp [h, member]

private theorem function_closed {m : Core.Module} {ids : Array Nat} (hclosed : closed m ids = true)
    {f : Core.Function} (mem : f ∈ (selected m ids).functions) :
    ∀ id ∈ f.body.callIds, ids.contains id = true :=
  List.all_eq_true.mp (List.all_eq_true.mp hclosed f mem)

private theorem individual {xs : List Core.Term} {ids : Array Nat}
    (all : ∀ id ∈ xs.flatMap Core.Term.callIds, ids.contains id = true)
    {t : Core.Term} (mem : t ∈ xs) :
    ∀ id ∈ t.callIds, ids.contains id = true :=
  fun id h => all id (List.mem_flatMap.mpr ⟨t,mem,h⟩)

/-- Filtering the original, independently checked Core module for closed
linkage preserves every bounded evaluation of a term whose calls are retained.
This equality includes failure and both branches at all fuel values. -/
theorem eval_selected (m : Core.Module) (ids : Array Nat) (hclosed : closed m ids = true)
    (fuel : Nat) (values : Values) (t : Core.Term)
    (calls : ∀ id ∈ t.callIds, ids.contains id = true) :
    eval (selected m ids) fuel values t = eval m fuel values t := by
  induction fuel generalizing t values with
  | zero => rfl
  | succ fuel ih =>
    cases t with
    | finiteTag | finiteLookup | integer | natural | boolean | unit | «variable» => rfl
    | unary op t r | project _ _ t | natToInt t | ascribe _ t | scope t =>
      simp only [Core.Term.callIds] at calls
      simp only [eval, ih _ t calls]
    | binary op x y r | pair _ x y | letE _ x y | unpack _ _ x y =>
      simp only [Core.Term.callIds, List.mem_append, or_imp] at calls
      simp only [eval, ih _ x (fun i h => (calls i).1 h), ih _ y (fun i h => (calls i).2 h)]
    | branch c y n r =>
      simp only [Core.Term.callIds, List.mem_append, or_imp] at calls
      have hc := ih values c (fun i h => ((calls i).1).1 h)
      have hy := ih values y (fun i h => ((calls i).1).2 h)
      have hn := ih values n (fun i h => (calls i).2 h)
      have arms (b : Bool) :
          eval (selected m ids) fuel values (if b then y else n) =
            eval m fuel values (if b then y else n) := by cases b <;> assumption
      simp only [eval, hc, arms]
    | primitive decl args r =>
      simp only [Core.Term.callIds] at calls
      have argsEq := same_mapM args _ _ (fun t h => ih values t (individual calls h))
      simp only [eval, argsEq]
      rfl
    | call id args sub r =>
      have keep : ids.contains id = true := calls id (by simp [Core.Term.callIds])
      have argsEq := same_mapM args _ _ (fun t h => ih values t (individual
        (fun i hi => calls i (by simp [Core.Term.callIds, hi])) h))
      have found := lookup_retained m ids id keep
      simp only [eval, argsEq]
      cases hit : (selected m ids).functions.find? (·.id == id) with
      | none => rw [← found, hit]; rfl
      | some f =>
        have hbody := function_closed hclosed (List.mem_of_find?_eq_some hit)
        rw [← found, hit]
        simp only [Option.bind_some, bind, ih _ f.body hbody]
    | pack decl obj fields =>
      simp only [Core.Term.callIds, List.mem_append, or_imp] at calls
      have ho := ih values obj (fun i hi => (calls i).1 hi)
      have fieldsEq := same_mapM fields
        (fun field => do
          let .indexed v ← eval (selected m ids) fuel values field | none
          pure v)
        (fun field => do
          let .indexed v ← eval m fuel values field | none
          pure v)
        (fun field h => by rw [ih values field (individual (fun i hi => (calls i).2 hi) h)])
      simp only [eval, ho]
      erw [fieldsEq]
      rfl

theorem retained_body {json main} {req : Request json main} (a : Artifact req)
    (f : Core.Function) (member : f ∈ (selected (core req) a.originals).functions)
    (fuel : Nat) (values : Values) :
    eval (selected (core req) a.originals) fuel values f.body = eval (core req) fuel values f.body :=
  eval_selected _ _ a.allCalls _ _ _ (function_closed a.allCalls member)

open Indexed.FunctionSource.Compiler in
/-- A static use in a retained specialization resolves to a prepared definition
of its exact Fn type. Every emitted sibling of that definition is retained,
including when the caller passes the value without invoking it. -/
theorem retained_static_use {json main} {req : Request json main} (a : Artifact req)
    (use : StaticUse) (used : use ∈ req.checked.pureProgram.executable.lowered.staticUses)
    {id : Nat} (retained : id ∈ a.originals) {caller : Key} (atCaller : use.caller = some caller)
    (origin : req.checked.pureProgram.executable.lowered.origins[id]? = some caller) :
    ∃ d p, use.target.name = .concrete d ∧ req.checked.pureProgram.compiler.input.prepared[d]? = some p ∧
      p.callable = some use.expected ∧ use.target.signature = use.expected ∧
      ∀ f ∈ (core req).functions, f.definition = p.definition.owner → f.id ∈ a.originals := by
  let src := req.checked.pureProgram
  obtain ⟨d, concrete⟩ := IndexedFunctions.executable_target_concrete src.executable use used
  obtain ⟨p, prepared, fnType, signature⟩ :=
    IndexedFunctions.target_signature_exact src.executable use used d concrete
  refine ⟨d, p, concrete, prepared, fnType, signature, ?_⟩
  have checked := a.staticTargets
  simp only [staticClosed, Bool.and_eq_true, List.all_eq_true] at checked
  have covered := checked.2 use used
  change src.compiler.input.prepared[d]? = some p at prepared
  simp only [atCaller, concrete] at covered
  change (src.compiler.input.prepared[d]?).any _ = true at covered
  simp [prepared] at covered
  intro f member owner
  apply Classical.byContradiction
  intro omitted
  exact covered.elim (fun missing => missing id retained origin)
    (fun missing => missing f member omitted owner)

/-- The original main remains the entry, independently of how many
dependency-owned functions were excluded or where the local address lies. -/
theorem entry_all_fuel {json main} {req : Request json main} (a : Artifact req) (fuel : Nat) :
    LLVM.FiniteCost.coreEntry (selected (core req) a.originals) fuel =
      LLVM.FiniteCost.coreEntry (core req) fuel := by
  have keep : a.originals.contains a.sourceEntry = true := by
    simpa using Array.mem_of_getElem? a.entryMap
  have found := lookup_retained (core req) a.originals a.sourceEntry keep
  simp only [LLVM.FiniteCost.coreEntry, show (selected (core req) a.originals).main = _ from a.originalEntry,
    a.originalEntry, Option.bind_some, bind]
  rw [← found]
  cases hit : (selected (core req) a.originals).functions.find? (·.id == a.sourceEntry) with
  | none => rfl
  | some f =>
    have body := retained_body a f (List.mem_of_find?_eq_some hit) fuel
    simp only [Option.bind_some, body]

def entry {p : VastitasKernel.MidIR.Phase} (m : VastitasKernel.MidIR.Module p)
    (depth : Nat) : Option Value := do
  let id ← m.entry
  let f ← m.functions[id]?
  MidIR.invoke m depth f.target []

/-- Package acceptance links the actual full Core and selected submodule to
both MidIR phases at the observed closed entry; all use the same entire Int. -/
theorem observed_entry {json main} {req : Request json main} (a : Artifact req)
    (w : LLVM.FiniteCost.Observation (core req)) (checked : Observation a w) :
    LLVM.FiniteCost.coreEntry (core req) w.fuel = some (.integer w.value) ∧
    LLVM.FiniteCost.coreEntry (selected (core req) a.originals) w.fuel = some (.integer w.value) ∧
    entry a.opt w.fuel = some (.integer w.value) ∧ entry a.exe w.fuel = some (.integer w.value) := by
  refine ⟨w.evaluated, (entry_all_fuel a w.fuel).trans w.evaluated, ?_, ?_⟩
  · simpa only [runEntry, entry, MidIR.checked_invoke] using checked.optimization
  · simpa only [runEntry, entry, MidIR.checked_invoke] using checked.execution

end VastitasOracle.PackageLink
