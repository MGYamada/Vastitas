import VastitasKernel.IndexedSourceProgram
import VastitasOracle.IndexedCore
import VastitasOracle.IndexedSource
import Std.Data.HashMap.Lemmas

/-! Exact-input acceptance of the internal data-function adapter. These results
cover structural typing, source coverage and provenance of the actual returned
Core. They do not assert source evaluation/native refinement or acceptance of
Fn, finite dispatch, edit authority or a public protocol-7 input. -/
namespace VastitasOracle.IndexedSourceBodies
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source
open Source.Bodies

theorem checked_program {program : Source.Program} (checked : CheckedProgram program requireMain) :
    Bodies.lower program checked.declarations.resolved.declarations = .ok checked.lowered ∧
    checked.core.module = checked.lowered.module ∧
    Core.Typing.ModuleTyped checked.lowered.module ∧
    Dependency.OrderedFrom [] (Core.Typing.dependencyEntries checked.lowered.module) ∧
    Core.Typing.MainValid checked.lowered.module requireMain := by
  refine ⟨checked.reconstructed, checked.coreInput, ?_, ?_, ?_⟩
  · simpa only [checked.coreInput] using checked.core.typed
  · simpa only [checked.coreInput] using IndexedCore.checked_module_ordered checked.core
  · simpa only [checked.coreInput] using checked.core.entry

theorem output_unique {program : Source.Program} (first second : CheckedProgram program requireMain) :
    first.lowered = second.lowered := by
  have declarations : first.declarations.resolved = second.declarations.resolved :=
    Except.ok.inj (first.declarations.lowered.symm.trans second.declarations.lowered)
  have equation := first.reconstructed
  rw [declarations, second.reconstructed] at equation
  exact (Except.ok.inj equation).symm

theorem function_source {program : Source.Program} (checked : CheckedProgram program requireMain)
    (function : Core.Function) (member : function ∈ checked.lowered.module.functions) :
    ∃ source, program.functions[function.id]? = some (function.definition, source) := by
  have origin := checked.origins.2 function member
  obtain ⟨⟨owner, source⟩, found, same⟩ := Option.map_eq_some_iff.mp origin
  change owner = function.definition at same
  subst owner
  exact ⟨source, by simpa using found⟩

theorem function_owner {program : Source.Program} (checked : CheckedProgram program requireMain)
    (function : Core.Function) (member : function ∈ checked.lowered.module.functions) :
    ∃ pkg ∈ program.packages, ∃ m ∈ pkg.modules, ∃ source ∈ m.functions,
      function.definition = ⟨⟨pkg.id, m.module.path⟩, source.name⟩ := by
  obtain ⟨source, found⟩ := function_source checked function member
  have present := List.mem_of_getElem? found
  simp only [Source.Program.functions, List.mem_flatMap, List.mem_map] at present
  obtain ⟨pkg, hp, m, hm, f, hf, equation⟩ := present
  exact ⟨pkg, hp, m, hm, f, hf, (congrArg Prod.fst equation).symm⟩

/-- Equal counts alone do not establish coverage. Actual Core ID uniqueness
and the independent source-position audit rule out replacing an unused body
with a second copy of another valid body. -/
theorem source_covered {program : Source.Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < program.functions.length) :
    ∃ function ∈ checked.lowered.module.functions, function.id = id := by
  let ids := checked.lowered.module.functions.map Core.Function.id
  have typed := (checked_program checked).2.2.1
  have subset : ids ⊆ List.range program.functions.length := by
    intro i member
    obtain ⟨function, hf, rfl⟩ := List.mem_map.mp member
    obtain ⟨source, found⟩ := function_source checked function hf
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp found).1
  have present : id ∈ ids := by
    by_cases absent : id ∈ ids
    · exact absent
    exfalso
    have unique : (id :: ids).Nodup := List.nodup_cons.mpr ⟨absent, typed.uniqueFunctions⟩
    have length := unique.length_le_of_subset (l₂ := List.range program.functions.length) (by
      intro i member
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_range.mpr bounded
      · exact subset member)
    have count := checked.origins.1
    simp only [List.length_cons, List.length_map, List.length_range, ids] at length
    omega
  exact List.mem_map.mp present

/-- This includes every unused input function, on the exact checked output;
it is stronger than merely inspecting the reachable/native subset. -/
theorem source_body_checked {program : Source.Program} (checked : CheckedProgram program requireMain)
    (id : Nat) (bounded : id < program.functions.length) :
    ∃ function ∈ checked.lowered.module.functions, function.id = id ∧
      Core.Typing.FunctionTyped checked.lowered.module.declarations
        (Core.Typing.signatures checked.lowered.module) function := by
  obtain ⟨function, member, same⟩ := source_covered checked id bounded
  exact ⟨function, member, same, (checked_program checked).2.2.1.functions function member⟩

private theorem owners_lookup (functions : List Core.Function) (id : Nat) :
    (functions.foldr (fun f table => table.insert f.id f.definition) ({} : Std.HashMap Nat DeclId))[id]? =
      (functions.find? (fun f => f.id == id)).map Core.Function.definition := by
  induction functions with
  | nil => simp
  | cons head rest ih =>
    change ((rest.foldr _ ({} : Std.HashMap Nat DeclId)).insert head.id head.definition)[id]? = _
    rw [Std.HashMap.getElem?_insert, ih]
    cases same : head.id == id <;> simp [List.find?, same]

theorem call_resolves {program : Source.Program} (checked : CheckedProgram program requireMain)
    (reference : CallReference) (member : reference ∈ checked.lowered.calls) :
    reference.scope ∈ program.toNamespace.scopes ∧ reference.target.kind = .function ∧
    Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span = .ok reference.target ∧
    ∃ function ∈ checked.lowered.module.functions,
      function.id = reference.id ∧ function.definition = reference.target.owner := by
  obtain ⟨scope, kind, found, owner⟩ := checked.calls reference member
  refine ⟨scope, kind, ?_, ?_⟩
  · cases equation : Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span with
    | error _ => simp [equation, Except.toOption] at found
    | ok target =>
      simp [equation, Except.toOption] at found
      subst target
      rfl
  · change (checked.lowered.module.functions.foldr _ ({} : Std.HashMap Nat DeclId))[reference.id]? = _ at owner
    rw [owners_lookup] at owner
    obtain ⟨function, foundFunction, same⟩ := Option.map_eq_some_iff.mp owner
    exact ⟨function, List.mem_of_find?_eq_some foundFunction,
      by simpa using List.find?_some foundFunction, same⟩

theorem declaration_resolves {program : Source.Program} (checked : CheckedProgram program requireMain)
    (reference : Source.Reference) (member : reference ∈ checked.lowered.references) :
    reference.scope ∈ program.toNamespace.scopes ∧ reference.target.kind = .indexedDeclaration ∧
    Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span = .ok reference.target := by
  obtain ⟨scope, kind, found⟩ := checked.references reference member
  refine ⟨scope, kind, ?_⟩
  cases equation : Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span with
  | error _ => simp [equation, Except.toOption] at found
  | ok target =>
    simp [equation, Except.toOption] at found
    subst target
    rfl

/-- Unsupported legacy bodies or authority/dispatch envelopes cannot enter
this restricted certificate and disappear during reconstruction. -/
theorem data_only {program : Source.Program} (checked : CheckedProgram program requireMain) :
    dataOnly program = .ok () := by
  cases accepted : dataOnly program with
  | ok value => cases value; rfl
  | error diagnostic =>
    have reconstructed := checked.reconstructed
    simp [Bodies.lower, accepted, bind, Except.bind] at reconstructed

end VastitasOracle.IndexedSourceBodies
