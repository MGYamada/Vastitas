import VastitasKernel.ResourceProtocol
import VastitasOracle.StorageFunctions
import VastitasOracle.BinaryFloat
import VastitasOracle.IndexedAuthority
import VastitasOracle.IndexedSource
import VastitasOracle.FiniteOpposite
import VastitasOracle.IndexedProgramSafety

/-! Public resource/source composition facts, tied to actual reconstruction and
both independent checkers. Pure-Core totality does not establish mutable native
heap semantics, source operational correspondence or numerical correctness. -/
namespace VastitasOracle.ResourceSource
open VastitasKernel VastitasKernel.ResourceSource
open VastitasKernel.Storage VastitasKernel.Indexed

theorem exact_components {program : Program} (checked : Checked program requireMain) :
    Indexed.AuthoritySource.checkProgram program.pureProgram (requireMain && program.entry.isNone) = .ok checked.pureProgram ∧
    lower program = .ok checked.lowered ∧
    Functions.checkLibrary checked.lowered.functions (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok checked.library :=
  ⟨checked.pureAccepted, checked.reconstructed, checked.libraryAccepted⟩

theorem complete_resource_identity {program : Program} (checked : Checked program requireMain) :
    checked.lowered.owners = program.owned.map Prod.fst ∧
    checked.lowered.functions.map Functions.Function.id = List.range program.owned.length ∧
    checked.lowered.functions.length = program.owned.length := by
  refine ⟨checked.provenance.1, checked.provenance.2.1, ?_⟩
  have length := congrArg List.length checked.provenance.2.1
  simpa using length

theorem call_provenance {program : Program} (checked : Checked program requireMain)
    (reference : Reference) (member : reference ∈ checked.lowered.references) :
    (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.scope ∧
    reference.target.kind = .resourceFunction ∧
    (Namespace.resolve program.pureProgram.source.headers.indexed reference.scope reference.path.path reference.path.span).toOption = some reference.target ∧
    (program.owned[reference.callee]?).map Prod.fst = some reference.target.owner :=
  checked.provenance.2.2.1 reference member

theorem numerical_provenance {program : Program} (checked : Checked program requireMain)
    (reference : NumericalReference) (member : reference ∈ checked.lowered.numericalReferences) :
    (program.owned[reference.caller]?).map (fun entry => entry.1.scope) = some reference.reference.scope ∧
    reference.reference.Valid program.pureProgram.source.headers.indexed :=
  checked.provenance.2.2.2 reference member

theorem every_resource_body {program : Program} (checked : Checked program requireMain)
    (function : Functions.Function) (member : function ∈ checked.lowered.functions) :
    ∃ result ∈ checked.library.bodies, result.function = function.id ∧
      Functions.probe checked.lowered.functions function (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok result ∧
      Storage.checkPlan result.statements = .ok result.resources :=
  StorageFunctions.every_library_body checked.library member

theorem original_authority {program : Program} (checked : Checked program requireMain) :
    Authority.Trace program.pureProgram.source.headers.indexed checked.pureProgram.authority.headers.assembled.prepared {}
      checked.pureProgram.authority.headers.assembled.prepared.core.assembly.events
      checked.pureProgram.authority.headers.assembled.state ∧
    Authority.Exclusive checked.pureProgram.authority.headers.assembled.state ∧
    checked.pureProgram.authority.headers.assembled.state.loans = [] :=
  IndexedAuthority.authority_trace checked.pureProgram

/-- Every exact arithmetic site in the returned pure Core is present in the
published revision. Its ordinal and result identify the sole protected
method for that family's ordered argument key. -/
theorem published_operator_method {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (site : Nat × Indexed.ExactOperators.Selection)
    (member : site ∈ Indexed.ExactOperators.selections input.checked.pureProgram.executable.core.module) :
    let typed := input.checked.pureProgram.executable.core.typed
    let row := FunctionRevision.operatorSite typed site member
    let revision := FunctionRevision.artifact (Wire.revisionInput json) input.checked
    ∃ ordinal result, ∃ rows : List Lean.Json,
      Indexed.ExactOperators.candidates site.2 = [(ordinal, result)] ∧
      row.getObjVal? "method" = .ok (FunctionRevision.operatorMethod (ordinal, result)) ∧
      (revision.getObjVal? "pure").bind (·.getObjVal? "operator_sites") = .ok (Lean.toJson rows) ∧
      row ∈ rows := by
  let typed := input.checked.pureProgram.executable.core.typed
  let selected := Indexed.ExactOperators.methodAt typed site member
  refine ⟨selected.1, selected.2, FunctionRevision.operatorSites typed,
    Indexed.ExactOperators.methodAt_sole typed site member, ?_,
    FunctionRevision.artifact_operators _ input.checked, ?_⟩
  · rfl
  · exact List.mem_map.mpr ⟨⟨site, member⟩, List.mem_attach _ _, rfl⟩

theorem pure_value_bodies_typed {program : Program} (checked : Checked program requireMain) :
    Core.Typing.ModuleTyped checked.values.audit.lowered.module ∧
    Core.Typing.ModuleTyped checked.values.executable.lowered.module :=
  ⟨(IndexedFunctions.checked_pass checked.values.audit).2.2.1,
    (IndexedFunctions.checked_pass checked.values.executable).2.2.1⟩

/-- Pure value bodies called from a resource entry. The mixed emit path generates
their library from `checked.values.compiled.core`, this module with its
reverse passes compiled into Core (#623). -/
theorem pure_value_functions_total {program : Program} (checked : Checked program requireMain) :
    ∀ function ∈ checked.values.executable.core.module.functions,
      IndexedFunctionSafety.FunctionReturns checked.values.executable.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed checked.values.executable.core

/-- Without a resource entry, the emit path generates code from
`checked.pureProgram.compiled.core`, this module with its reverse passes
compiled into Core (see `ResourceCodegen.generated_pure_entry`). Every function
of this module has typed, finite evaluation. -/
theorem pure_entry_functions_total {program : Program} (checked : Checked program requireMain) :
    ∀ function ∈ checked.pureProgram.executable.core.module.functions,
      IndexedFunctionSafety.FunctionReturns checked.pureProgram.executable.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed checked.pureProgram.executable.core

private theorem main_total_of {required : Bool} (core : Core.Typing.CheckedModule required)
    (same : required = true) :
    ∃ id function result,
      core.module.main = some id ∧
      core.module.functions.find? (fun function => function.id == id) = some function ∧
      IndexedEvaluation.Evaluates core.module (fun _ => none) function.body (.integer result) := by
  subst same
  exact IndexedProgramSafety.checked_main_total core

/-- A pure-entry program accepted with a required `main` has a parameterless
`main` whose body evaluates to an `Int` in the actual indexed evaluator. -/
theorem pure_entry_main_total {program : Program} (checked : Checked program true)
    (found : program.entry = none) :
    ∃ id function result,
      checked.pureProgram.executable.core.module.main = some id ∧
      checked.pureProgram.executable.core.module.functions.find? (fun function => function.id == id) =
        some function ∧
      IndexedEvaluation.Evaluates checked.pureProgram.executable.core.module (fun _ => none)
        function.body (.integer result) :=
  main_total_of checked.pureProgram.executable.core (by simp [found])

/-- The accepted public entry uses the original library's complete probe list
and starts executable expansion from the actual closed program. -/
theorem entry_uses_checked_library {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let p : Functions.Program := ⟨checked.lowered.functions, entry⟩
    let e := checked.execution entry found
    Functions.checkWithLibrary p checked.library = .ok e.checked ∧
      e.checked.bodies = checked.library.bodies ∧
      Functions.executable p (numericalEnvironment checked.pureProgram) checked.targets.signatures =
        .ok e.checked.context := by
  let e := checked.execution entry found
  let p : Functions.Program := ⟨checked.lowered.functions, entry⟩
  have reused := Functions.checkWithLibrary_eq_check p checked.library
  have same : e.checked.bodies = checked.library.bodies :=
    Except.ok.inj (e.checked.bodiesFrom.symm.trans checked.library.bodiesFrom)
  exact ⟨reused.trans e.accepted, same, e.checked.expanded⟩

theorem library_work_bound {program : Program} (checked : Checked program requireMain) :
    (checked.library.bodies.map Functions.Probe.units).sum = checked.library.work.val ∧
      checked.library.work.val ≤ Limits.resourceWork := by
  have total := (Work.collect_exact checked.library.collected).2
  exact ⟨by simpa [Work.zero] using total.symm, Nat.le_of_lt_succ checked.library.work.isLt⟩

theorem entry_work_bound {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let e := (checked.execution entry found).checked
    (checked.library.bodies.map Functions.Probe.units).sum + e.context.work.val +
      e.resources.work.val + e.shapes.resources.work.val ≤ Limits.resourceWork := by
  have same := (entry_uses_checked_library checked entry found).2.1
  rw [← same]
  exact (checked.execution entry found).checked.workBound

theorem actual_entry_closed {program : Program} (checked : Checked program requireMain)
    (entry : Nat) (found : program.entry = some entry) :
    let execution := checked.execution entry found
    Functions.check ⟨checked.lowered.functions, entry⟩ (numericalEnvironment checked.pureProgram) checked.targets.signatures = .ok execution.checked ∧
    Storage.run 4096 {} execution.checked.statements = .ok execution.checked.resources.finalState ∧
    execution.checked.resources.finalState.allocations = [] ∧ execution.checked.resources.finalState.loans = [] :=
  ⟨(checked.execution entry found).accepted, (checked.execution entry found).checked.resources.accepted,
    (checked.execution entry found).checked.resources.closed⟩

theorem namespace_work_bound {json : Lean.Json} (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    Namespace.priceInput input.input.pureProgram.source.headers.indexed json = .ok input.namespaceReceipt.inputUnits ∧
    input.namespaceReceipt.inputUnits.val + VastitasKernel.ResourceSource.Wire.namespaceUnits input.checked ≤ Limits.namespaceProgramWork :=
  ⟨input.namespaceReceipt.priced, input.namespaceReceipt.bounded⟩

/-- The checked entry file's lexical projection agrees with the structured
wire commands. Expanding either yields the exact events and spans in the
independently accepted authority trace. File acquisition and the non-edit
grammar are frontend premises. -/
theorem structured_assembly_trace {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    let a := input.checked.pureProgram.authority.headers.assembled
    ∃ file items trace, AssemblySource.rootFile json = .ok file ∧
      AssemblyText.parse file.text file.offset = .ok items ∧
      AssemblySource.read json = .ok items ∧ AssemblySource.expand items = .ok trace ∧
      trace.events = a.prepared.core.assembly.events ∧
      trace.span.all (· == a.prepared.core.assembly.span) = true ∧
      VastitasKernel.Authority.Trace _ a.prepared {} trace.events a.state := by
  let source := input.assemblySource
  refine ⟨source.file, source.items, source.trace, source.supplied, source.lexical,
    source.decoded, source.expanded, source.exactEvents, source.exactSpan, ?_⟩
  rw [source.exactEvents]
  exact (VastitasOracle.Authority.assembled_trace _).1

/-- Each file-backed package has a manifest at its own path in the accepted
request. Its physical fields supply the name and version in the package ID
and the edition admitted by the wire decoder. -/
theorem physical_manifest_metadata {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (disk : input.input.root ≠ flatPackageId.source) {pkg : Package} (hp : pkg ∈ input.input.packages) :
    ∃ (layout : PhysicalSources.Layout) (i : Nat) (file : PhysicalSources.File),
      PhysicalSources.layout json = .ok layout ∧ layout.files[i]? = some file ∧
      file.path = pkg.id.source.toUTF8 ∧
      ManifestMetadata.read? file.text = some ⟨pkg.id.name, pkg.id.version, currentEdition⟩ := by
  have checked := Wire.exactSources_of_program input.decoded
  cases h : PhysicalSources.layout json with
  | error msg => simp [Wire.exactSources, h, Bind.bind, Except.bind] at checked
  | ok layout =>
    cases he : Wire.mismatchedManifest? layout input.input with
    | some other => simp [Wire.exactSources, h, he, Bind.bind, Except.bind, throw] at checked
    | none =>
      simp [Wire.mismatchedManifest?, disk, List.find?_eq_none] at he
      have found := he pkg hp
      cases f : Wire.manifestFile? layout (Wire.physicalFileIndex layout) pkg.id.source with
      | none => simp [f] at found
      | some file =>
        have fields : ManifestMetadata.read? file.text = some ⟨pkg.id.name, pkg.id.version, currentEdition⟩ := by
          simpa [f] using found
        simp only [Wire.manifestFile?, ManifestBindings.manifestFile?, Option.bind_eq_some_iff, bind] at f
        obtain ⟨i, _, record, situated, accepted⟩ := f
        simp [guard, pure] at accepted
        obtain ⟨path, rfl⟩ := accepted
        exact ⟨layout, i, record, rfl, situated, congrArg ByteArray.mk path, fields⟩

/-- Every file-backed package declares exactly its admitted dependency aliases and its
exported legacy geometry roles. The loader resolves paths relative to the manifest. -/
theorem physical_manifest_bindings {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (disk : input.input.root ≠ flatPackageId.source) :
    ∃ layout, PhysicalSources.layout json = .ok layout ∧
      ∀ pkg ∈ input.input.packages, ManifestBindings.Corresponds layout pkg := by
  obtain ⟨_, layout, _, _, physical, _, _, bindings, _⟩ := EditSourceFiles.all_evidence input.editSources
  exact ⟨layout, physical, fun _ member => ManifestBindings.check_sound bindings disk member⟩

/-- The public request carries the physical edit declaration comparison for
the very program whose contributions and assembly passed the authority checker. -/
theorem physical_edit_declarations {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      checked.edits.any (·.isEmpty) = true ∧
      ∀ item ∈ EditSourceFiles.sourceMethods input.input,
        EditSourceFiles.BodyCorresponds layout checked item := by
  obtain ⟨expected, layout, checked, collected, physical, scan, empty, bodies, _⟩ :=
    EditSourceFiles.check_evidence input.editSources
  exact ⟨expected, layout, checked, collected, physical, scan, empty,
    fun _ member => EditSourceFiles.checkBodies_sound bodies member⟩

/-- Rational interpretation of the exact-literal checker’s extracted IEEE fields. -/
def componentValue (c : ResourceLiteralText.Component) : Option Rat :=
  if c.finite then
    let scale : Rat := if c.exponent < 0 then Rat.divInt 1 (2^c.exponent.natAbs : Nat) else (2^c.exponent.toNat : Nat)
    let q := (c.significand : Rat) * scale
    some (if c.negative then -q else q)
  else none

/-- At both widths the extracted fields have the Oracle’s rational value for every bit pattern. -/
theorem literal_component_value {f : BinaryFloat.Format} (x : BinaryFloat.Scalar f) :
    componentValue (ResourceLiteralText.component x.bits.toNat f.fractionBits (f.width - f.fractionBits - 1)) =
      BinaryFloat.denote? x := by
  unfold BinaryFloat.denote? componentValue
  have classify (n infinity : Nat) : decide (n < infinity) = !(decide (n = infinity) || decide (n > infinity)) := by
    rcases Nat.lt_trichotomy n infinity with h | h | h
    · simp [h, Nat.ne_of_lt h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
    · simp [h]
    · simp [h, Nat.ne_of_gt h, Nat.not_lt_of_ge (Nat.le_of_lt h)]
  have finite : (ResourceLiteralText.component x.bits.toNat f.fractionBits (f.width - f.fractionBits - 1)).finite =
      !(BinaryFloat.isInf x || BinaryFloat.isNaN x) := by
    cases f <;> apply classify
  rw [finite]
  cases BinaryFloat.isInf x || BinaryFloat.isNaN x <;> cases f <;> rfl
/-- Every literal cell operation in a checked resource body consumes its complete
physical statement at the same function and branch position. The inventories
agree even when a function or branch does not execute. -/
theorem physical_resource_cells {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      Finite.sameCounts checked.cells.keys ((ResourceCellSource.items input.input).map (·.span.start)) = true ∧
      ∀ i ∈ ResourceCellSource.items input.input, ResourceCellSource.Corresponds layout checked.cells i := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, _, cells, _, _, _, _, _⟩ :=
    EditSourceFiles.all_evidence input.editSources
  obtain ⟨inventory, all⟩ := ResourceCellSource.check_sound cells
  exact ⟨expected, layout, checked, collected, physical, scan, inventory, all⟩

/-- Every accepted product operation matches the physical operands, mode, policy and
optional literal or loan coefficients in the statement at its lexical position. -/
theorem physical_resource_products {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      Finite.sameCounts checked.products.keys ((ResourceProductSource.items input.input).map (·.span.start)) = true ∧
      ∀ i ∈ ResourceProductSource.items input.input, ResourceProductSource.Corresponds layout checked.products i := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, _, _, products, _, _, _, _⟩ :=
    EditSourceFiles.all_evidence input.editSources
  obtain ⟨inventory, all⟩ := ResourceStatementSource.check_sound products
  exact ⟨expected, layout, checked, collected, physical, scan, inventory, all⟩

/-- The selected allocation, borrow, transfer and cleanup statements have exactly
the scanned positions and operands, including runtime dimension slots and layouts. -/
theorem physical_resource_ownership {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      Finite.sameCounts checked.ownership.keys ((ResourceOwnershipSource.items input.input).map (·.span.start)) = true ∧
      ∀ i ∈ ResourceOwnershipSource.items input.input, ResourceOwnershipSource.Corresponds layout checked.ownership i := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, _, _, _, ownership, _, _, _⟩ :=
    EditSourceFiles.all_evidence input.editSources
  obtain ⟨inventory, all⟩ := ResourceStatementSource.check_sound ownership
  exact ⟨expected, layout, checked, collected, physical, scan, inventory, all⟩

/-- Each resource signature, conditional guard, binding and call replays at its
lexical owner. The final result block follows the function's last statement. -/
theorem physical_resource_values {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      Finite.sameCounts checked.values.keys ((ResourceValueSource.items input.input).map (·.span.start)) = true ∧
      ∀ i ∈ ResourceValueSource.items input.input, ResourceValueSource.Corresponds layout checked.values i := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, _, _, _, _, values, _, _⟩ :=
    EditSourceFiles.all_evidence input.editSources
  obtain ⟨inventory, all⟩ := ResourceStatementSource.check_sound values
  exact ⟨expected, layout, checked, collected, physical, scan, inventory, all⟩

/-- Every finite carrier, table, schema, instance and static-indexed function in this accepted program
replays in its declaring file. The inventory also accounts for uncalled and
unused declarations in the physical modules. -/
theorem physical_finite_declarations {json : Lean.Json} (input : Wire.CheckedInput json requireMain) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      Finite.sameCounts checked.finiteSites.keys ((FiniteSourceFiles.declarations input.input).map (·.span.start)) = true ∧
      ∀ item ∈ FiniteSourceFiles.declarations input.input, FiniteSourceFiles.Corresponds layout checked.finiteSites item := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, _, finite⟩ :=
    EditSourceFiles.check_evidence input.editSources
  obtain ⟨inventory, all⟩ := FiniteSourceFiles.check_sound finite
  exact ⟨expected, layout, checked, collected, physical, scan, inventory, all⟩

/-- Each presented affine object, fiber product, localization and smooth
affine space in an accepted request replays at its original declaration. -/
theorem physical_affine_declaration {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    (selected : AffineDeclarationText.applies d = true) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, d.span, d.isPublic, .affine d⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm,
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ ?_))⟩⟩
  exact List.mem_filterMap.mpr ⟨d, hd, by simp [selected]⟩

/-- Locate the actual token stream for a named map in the accepted package.
The replay compares its family, endpoints and the complete defining graph. -/
theorem physical_morphism {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    {family : Indexed.Source.Path} {indices : List Indexed.Source.Path} {definition : Indexed.Source.MorphismDefinition}
    (body : d.body = .morphism family indices definition) :
    ∃ expected layout, ∃ (checked : AssemblyText.SourceChecks) (site : AssemblyText.FiniteSite)
      (file : PhysicalSources.File) (first : SourceText.Token),
      EditSourceFiles.collect input.input = .ok expected ∧ PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      checked.finiteSites[d.span.start]? = some site ∧
      layout.files[site.fileIndex]? = some file ∧
      (site.packageSource, site.modulePath, site.isPublic) = (pkg.id.source, m.pureModule.module.path, d.isPublic) ∧
      (SourceText.File.mk file.text file.offset).next site.before = .ok first ∧
      AffineDeclarationText.check ⟨file.text, file.offset⟩ first d = .ok () := by
  obtain ⟨expected, layout, checked, edits, physical, scan, site, file, atSite, atFile, owner, _, _, replay⟩ :=
    physical_affine_declaration input hp hm hd (by simp [AffineDeclarationText.applies, body])
  let source := SourceText.File.mk file.text file.offset
  change FiniteSourceFiles.replay source site.before _ = .ok () at replay
  cases tok : source.next site.before with
  | error msg => simp [FiniteSourceFiles.replay, tok, Except.mapError, Bind.bind, Except.bind] at replay
  | ok first =>
    refine ⟨expected, layout, checked, site, file, first, edits, physical, scan, atSite, atFile, owner, tok, ?_⟩
    simpa [FiniteSourceFiles.replay, tok, Except.mapError, Bind.bind, Except.bind] using replay

/-- An accepted non-root module carries its visibility and its declaring
module's path at the original inline or external declaration. -/
theorem physical_module {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {name : String} (named : m.pureModule.module.path.getLast? = some name) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path.dropLast, m.pureModule.module.span,
          m.pureModule.module.isPublic, .namespaceModule name⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm,
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))⟩⟩
  exact List.mem_map.mpr ⟨name, by simp [named], rfl⟩

/-- Every import in the checked program replays the written target, its explicit
or implicit alias, visibility and terminator in its declaring module. -/
theorem physical_import {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {i : Namespace.Import} (hi : i ∈ m.pureModule.module.imports) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, i.span, i.isPublic, .namespaceImport i⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))⟩⟩
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- The abstract parents and concrete memberships used by dispatch come from the
same accepted request as its assembly. This includes selectors without a call. -/
theorem physical_selector_hierarchy {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      (∀ t ∈ m.pureModule.module.abstractTypes, FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, t.span, t.isPublic, .abstractType t⟩) ∧
      (∀ s ∈ m.pureModule.module.subtypes, FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, s.span, false, .subtype s⟩) := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, ?_, ?_⟩
  · intro t ht
    apply all
    apply List.mem_flatMap.mpr
    refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, ?_⟩⟩
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map.mpr ⟨t, ht, rfl⟩))))
  · intro s hs
    apply all
    apply List.mem_flatMap.mpr
    refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, ?_⟩⟩
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩))))

/-- Each finite-indexed function, including an unused overload, replays its own
binders, parameter and result types and body in its declaring module. -/
theorem physical_finite_function {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {f : Indexed.FunctionSource.Function} (hf : f ∈ m.pureModule.functions) (finite : f.finiteBinders.isEmpty = false) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, f.span, f.isPublic, .function f⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, List.mem_append_right _ ?_⟩⟩
  exact List.mem_map.mpr ⟨f, hf, by simp [finite]⟩

/-- Each ordinary singleton replays at its defining file's tokens. The list
of observations selects exactly the top-level source initializers wrapped in
`show!`; labels remain presentation metadata. -/
theorem physical_singleton_function {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {f : Indexed.FunctionSource.Function} (hf : f ∈ m.pureModule.functions) (ordinary : f.finiteBinders.isEmpty = true) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, f.span, f.isPublic,
          .singleton f (((m.observations.lookup f.name).getD []).map (·.statement))⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_finite_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, List.mem_append_right _ ?_⟩⟩
  exact List.mem_map.mpr ⟨f, hf, by simp [ordinary]⟩

/-- Even an unapplied contribution has a replay of its decoded method's
complete syntax, in its original package, module and physical file. -/
theorem contributed_method_body {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {c : Indexed.DispatchSource.Contribution} (hc : c ∈ m.pureModule.contributions)
    {d : Indexed.DispatchSource.Method} (hd : d ∈ c.methods) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      EditSourceFiles.BodyCorresponds layout checked ⟨pkg.id.source, m.pureModule.module.path, some c.name, d⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_edit_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, List.mem_append_right _ ?_⟩⟩
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨d, hd, rfl⟩⟩

/-- The public request replays each original defining method, including a
fallback with no call site in the compiled entry. -/
theorem defining_method_body {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    {pkg : Package} (hp : pkg ∈ input.input.packages) {m : Module} (hm : m ∈ pkg.modules)
    {d : Indexed.DispatchSource.Method} (hd : d ∈ m.pureModule.methods) :
    ∃ expected layout checked, EditSourceFiles.collect input.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout input.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      EditSourceFiles.BodyCorresponds layout checked ⟨pkg.id.source, m.pureModule.module.path, none, d⟩ := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, all⟩ := physical_edit_declarations input
  refine ⟨expected, layout, checked, collected, physical, scan, all _ ?_⟩
  unfold EditSourceFiles.sourceMethods
  apply List.mem_flatMap.mpr
  refine ⟨pkg, hp, List.mem_flatMap.mpr ⟨m, hm, List.mem_append_left _ ?_⟩⟩
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

/-- Supplying a revision cannot select a method. Acceptance implies exact
equality with the complete receipt reconstructed from this program's checked
authority and Core passes. No claim about LLVM or native execution follows. -/
theorem expected_function_revision_exact {json expected : Lean.Json}
    (input : Wire.CheckedInput json requireMain)
    (supplied : json.getObjVal? "expected_function_revision" = .ok expected) :
    expected.compress = (FunctionRevision.artifact (Wire.revisionInput json) input.checked).compress := by
  have h := input.revisionMatches
  simp only [Wire.RevisionMatches, supplied] at h
  exact h.2.2

/-- At this same replayed revision the source owner/key selects the exact
method and definition of each executable dispatch edge; the callee symbol
is the specialization emitted for that definition. -/
theorem expected_revision_selects_method {json expected : Lean.Json}
    (input : Wire.CheckedInput json requireMain)
    (supplied : json.getObjVal? "expected_function_revision" = .ok expected)
    (call : FunctionSource.Compiler.DispatchCall)
    (member : call ∈ input.checked.pureProgram.executable.lowered.dispatchCalls) :
    expected.compress = (FunctionRevision.artifact (Wire.revisionInput json) input.checked).compress ∧
    input.checked.pureProgram.executable.lowered.origins[call.emittedId]? =
      some (FunctionSource.Compiler.Key.mk call.definition []) ∧
    ∃ family, input.checked.pureProgram.compiler.input.dispatch.families[call.target.owner]? = some family ∧
      call.key ∈ family.domain ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      input.checked.pureProgram.compiler.input.dispatch.definitions[(call.method, call.key)]? = some call.definition :=
  ⟨expected_function_revision_exact input supplied,
    IndexedDispatch.dispatch_call_emitted input.checked.pureProgram.executable call member,
    (IndexedDispatch.dispatch_call_selected input.checked.pureProgram.executable call member).2.2.2⟩

theorem public_input {json : Lean.Json} (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    VastitasKernel.ResourceSource.Wire.program json = .ok input.input ∧
    VastitasKernel.ResourceSource.check input.input requireMain = .ok input.checked ∧
    lower input.input = .ok input.checked.lowered :=
  ⟨input.decoded, input.accepted, input.checked.reconstructed⟩

/-- The public wire uses the same numerical declaration contract as the
actual complete authority checker. This is not a floating-point result theorem. -/
theorem public_numerical_declaration {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (id marker : DeclId) (representation : Indexed.Representation) (capabilities : List Capability)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    representation.Valid input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
      marker capabilities :=
  (IndexedSource.checked_implementation_contract _ input.checked.pureProgram.authority.headers.declarations
    id marker representation capabilities member).2.2

/-- The public protocol checks every named functor, including unused ones,
in its own accepted declaration environment at the input's checked revision. -/
theorem public_finite_functor {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteFunctor schema maps⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteFunctors.model (Indexed.FiniteCategories.view env) schema maps = some m ∧
        VastitasOracle.FiniteFunctors.Preserves m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteFunctors.checked_functor
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- A named functor from a declared opposite obeys the contravariant
composition equation in the base graph of this specific public revision. -/
theorem public_opposite_functor {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteFunctor schema maps⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed)
    (named : Indexed.FiniteCategories.view input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
      maps.source = some (.finiteOpposite categorySchema base))
    (direct : Indexed.FiniteCategories.view input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
      base = some (.finiteCategory categorySchema fields))
    (selected : Indexed.FiniteCategories.graph
      (Indexed.FiniteCategories.view input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed)
      categorySchema fields = some g) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteFunctors.model (Indexed.FiniteCategories.view env) schema maps = some m ∧
        ∀ h ∈ g.arrows, ∀ f ∈ g.arrows, g.composable h f = true →
          VastitasOracle.FiniteFunctors.Commutes
            ((g.composition[[h,f]]?).bind (Indexed.FiniteFunctors.image m.arrows))
            (m.mappedComposition f h) := by
  obtain ⟨revision, m, model, laws⟩ := public_finite_functor input member
  have source := FiniteOpposite.model_source model (FiniteOpposite.selected_view named direct selected)
  exact ⟨revision, m, model, fun _ h _ f pair => FiniteOpposite.map_reverses laws source h f pair⟩

/-- The named isomorphism uses the category, arrows and both identities of
this accepted public input. The same revision covers the unused declarations. -/
theorem public_finite_iso {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteIso schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteIso.select (Indexed.FiniteCategories.view env) schema fields = .ok m ∧
        VastitasOracle.FiniteIso.Inverses m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteIso.checked_iso
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- A transformation in the accepted module satisfies all its component
endpoint and naturality equations under the very same checked revision. -/
theorem public_finite_nat_trans {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteNatTrans schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteNatTrans.model (Indexed.FiniteCategories.view env) schema fields = some m ∧
        VastitasOracle.FiniteNatTrans.Natural m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteNatTrans.checked_transformation
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- A named Monad of the public checked module satisfies both unit laws
and associativity for the structure selected by this exact input revision. -/
theorem public_finite_monad {json : Lean.Json} (input : Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteMonads.model (Indexed.FiniteCategories.view env) schema fields = some m ∧
        VastitasOracle.FiniteMonads.Diagrams m :=
  ⟨input.revisionMatches, VastitasOracle.FiniteMonads.checked_monad
    input.checked.pureProgram.authority.headers.declarations member⟩

/-- Every actual product receipt belongs to the environment returned by this
same public source check, and records its own exact emitted resource operation. -/
theorem public_product_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.products.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkProduct receipt.environment receipt.resources receipt.values
      receipt.left receipt.right receipt.output receipt.mode receipt.policy receipt.alpha receipt.beta = .ok receipt.checked ∧
    receipt.priorCode ++ [.action (.gemm (receipt.checked.product.request receipt.mode receipt.policy))] = receipt.code ∧
    Storage.checkAction receipt.resources (.gemm (receipt.checked.product.request receipt.mode receipt.policy)) = .ok receipt.after :=
  ⟨(input.checked.execution entry found).numericalOrigins.2 receipt member,
    receipt.accepted, receipt.emitted, receipt.transitioned⟩

/-- Dependent inputs use the exact declaration environment accepted by the
same public request. Their certificates are from actual expansion, not probes. -/
theorem public_numerical_input_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalInputReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.inputs.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkInput receipt.environment receipt.callerResources receipt.callerValues
      receipt.input receipt.actual = .ok receipt.checked ∧
    Functions.NumericalBinding receipt.checked.value receipt.actual receipt.bound receipt.access
      receipt.before receipt.after receipt.values :=
  ⟨(input.checked.execution entry found).inputOrigins receipt member, receipt.accepted, receipt.binding⟩

theorem public_numerical_result_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.NumericalResultReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.outputs.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkInput receipt.environment receipt.resources receipt.values
      (.ownedMap receipt.source receipt.target) receipt.actual = .ok receipt.checked ∧
    receipt.checked.value = .ownedMap receipt.view ∧ receipt.returned.map = some receipt.view :=
  ⟨(input.checked.execution entry found).outputOrigins receipt member,
    receipt.accepted, receipt.selected, receipt.mapping⟩

theorem public_numerical_transform_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.TransformReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.transforms.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkTransform receipt.environment receipt.resources receipt.values receipt.name receipt.parent
      receipt.child receipt.operation = .ok receipt.checked ∧ receipt.checked.after = receipt.after :=
  ⟨(input.checked.execution entry found).transformOrigins receipt member, receipt.accepted, receipt.transitioned⟩

theorem public_vector_conjugation_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.VectorConjugateReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.vectorConjugates.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkVectorConjugate receipt.environment receipt.resources receipt.values receipt.name receipt.parent
      receipt.child receipt.basis receipt.selected = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).vectorOrigins receipt member, receipt.accepted⟩

theorem public_evaluation_origin {json : Lean.Json}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain)
    (entry : Nat) (found : input.input.entry = some entry)
    (receipt : Functions.EvaluationReceipt)
    (member : receipt ∈ (input.checked.execution entry found).checked.context.evaluations.toList) :
    receipt.environment = numericalEnvironment input.checked.pureProgram ∧
    Storage.Numerical.checkEvaluation receipt.environment receipt.resources receipt.values receipt.left receipt.right
      receipt.output receipt.leftChild receipt.rightChild receipt.operation receipt.mode receipt.policy receipt.alpha receipt.beta = .ok receipt.checked :=
  ⟨(input.checked.execution entry found).evaluationOrigins receipt member, receipt.accepted⟩

end VastitasOracle.ResourceSource
