import VastitasKernel.LLVM.FiniteProgram
import VastitasOracle.FiniteEntryEvaluation
import VastitasOracle.PackageLink
import VastitasOracle.ResourceSource

set_option autoImplicit false

namespace VastitasOracle.FiniteProgram
open VastitasKernel VastitasKernel.LLVM

/-- An accepted finite executable connects the original Core entry, its two
SSA evaluations and the externally visible LLVM entry to the complete parsed
bytes and target. Only the process exit applies the byte projection. -/
theorem correspondence {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.FiniteProgram.Artifact req header) (bytes : List UInt8)
    (parsed : FiniteModule.parse bytes = some a.model) :
    bytes = FiniteModule.print a.model ∧
    a.model.code.header = header ∧
    a.linked.exe.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput json) req.checked ∧
    (∀ n ≥ a.observed.fuel, FiniteCost.coreEntry (MidIR.PackageLink.core req) n =
      some (.integer a.observed.value)) ∧
    PackageLink.entry a.linked.opt a.observed.fuel = some (.integer a.observed.value) ∧
    PackageLink.entry a.linked.exe a.observed.fuel = some (.integer a.observed.value) ∧
    FiniteModule.lower a.linked.exe header = some a.model ∧
    a.model.code.entryStatus = some (ExitMain.statusOf a.observed.value).toUInt32 := by
  have obs := PackageLink.observed_entry a.linked a.observed a.stages
  exact ⟨(FiniteModule.parse_iff bytes a.model).mp parsed, a.target,
    (VastitasKernel.MidIR.execute_identity _ _ a.linked.executed).2.trans a.linked.revision,
    FiniteEntryEvaluation.entry_stable _ a.observed, obs.2.2.1, obs.2.2.2, a.lowered, a.status⟩

/-- The public finite emitter retains every physically written finite declaration
in both SSA environments, even when the entry never calls the declaration. -/
theorem physical_declaration_bytes {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.FiniteProgram.Artifact req header) (bytes : List UInt8)
    (parsed : FiniteModule.parse bytes = some a.model)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    (finite : (FiniteSourceFiles.form d).isSome = true) :
    let owner : Indexed.DeclId := ⟨⟨pkg.id, m.pureModule.module.path⟩, d.name⟩
    let decls := ResourceSource.Wire.finiteDeclarations req.input
    let index := req.checked.pureProgram.compiler.input.body.index
    let graphs := Indexed.Source.graphSources decls
    (∃ expected layout checked, EditSourceFiles.collect req.input = .ok expected ∧
      PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds layout checked.finiteSites
        ⟨pkg.id.source, owner.scope.path, d.span, d.isPublic, FiniteSourceFiles.indexedSyntax d⟩) ∧
    ResourceSource.Wire.resolveFiniteEntries index decls = .ok (ResourceSource.Wire.coreFiniteEntries a.linked.exe.env) ∧
    (∃ cache entry, (Indexed.Source.buildProjectionCache index graphs decls).run' [] = .ok cache ∧
      ResourceSource.Wire.resolveFiniteEntry index graphs cache (owner, d) = .ok entry ∧
      entry ∈ (MidIR.PackageLink.core req).declarations.indexed ∧
      entry ∈ a.linked.opt.env ∧ entry ∈ a.linked.exe.env) ∧
    a.linked.opt.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked ∧
    a.linked.exe.revision = a.linked.opt.revision ∧
    FiniteModule.lower a.linked.exe header = some a.model ∧ bytes = FiniteModule.print a.model := by
  obtain ⟨physical, cache, entry, built, resolved, member⟩ := ResourceSource.physical_finite_entry req hp hm hd finite
  obtain ⟨env, rev⟩ := VastitasKernel.MidIR.execute_identity _ _ a.linked.executed
  have opt : entry ∈ a.linked.opt.env := a.linked.environment.symm ▸ member
  have inventory := ResourceSource.finite_inventory req
  exact ⟨physical, by rw [env, a.linked.environment]; exact inventory,
    ⟨cache, entry, built, resolved, member, opt, env.symm ▸ opt⟩,
    a.linked.revision, rev, a.lowered, (FiniteModule.parse_iff _ _).mp parsed⟩

end VastitasOracle.FiniteProgram
