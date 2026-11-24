import VastitasKernel.LLVM.FiniteProgram
import VastitasOracle.FiniteEntryEvaluation
import VastitasOracle.FiniteJoins
import VastitasOracle.PackageLink
import VastitasOracle.ResourceSource
import VastitasOracle.IndexedDispatch

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

private theorem certified_code {c : FiniteModule.Code} {m : FiniteModule.Module}
    (accepted : FiniteModule.certify c = some m) : m.code = c := by
  unfold FiniteModule.certify at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  rfl

private theorem emitted_images {env entry} (fs : List (VastitasKernel.MidIR.Function .execution))
    (slot : Nat) (acc out : Array FiniteModule.Func)
    (emitted : FiniteModule.emitFunctions env entry fs slot acc = some out) :
    ∃ images, fs.mapM (FiniteModule.translateFn env entry) = some images ∧
      out.toList = acc.toList ++ ((images.zipIdx slot).flatMap fun (g,i) => g.helpers.toList ++ [g.body i]) := by
  induction fs generalizing slot acc with
  | nil =>
    cases emitted
    exact ⟨[], rfl, by simp⟩
  | cons f fs ih =>
    simp only [FiniteModule.emitFunctions, bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨head, lowered, rest⟩ := emitted
    obtain ⟨tail, mapped, layout⟩ := ih _ _ rest
    exact ⟨head :: tail, by simp [List.mapM_cons, lowered, mapped],
      by simpa [List.zipIdx_cons, List.append_assoc] using layout⟩

open VastitasKernel.MidIR in
/-- Every retained execution slot has one LLVM body. Its lookup helpers
immediately precede that body and the public C entry follows the last slot. -/
theorem function_inventory {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.FiniteProgram.Artifact req header) :
    ∃ entry images, a.linked.exe.entry = some entry ∧
      a.linked.exe.functions.toList.mapM (FiniteModule.translateFn a.linked.exe.env entry) = some images ∧
      images.length = a.linked.originals.size ∧
      a.model.code.functions =
        (images.zipIdx.flatMap fun (image,i) => image.helpers.toList ++ [image.body i]) ++ [FiniteModule.hostMain entry] ∧
      ∀ i image, images[i]? = some image → ∃ id orig key target opt exe,
        a.linked.originals[i]? = some id ∧
        (VastitasKernel.MidIR.PackageLink.core req).functions.toArray[id]? = some orig ∧
        orig.id = id ∧ req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
        validOrigin req.checked.pureProgram orig key = true ∧ CallTarget.ofCore orig key = some target ∧
        a.linked.opt.functions[i]? = some opt ∧ opt.target = {target with symbol := i} ∧
        a.linked.exe.functions[i]? = some exe ∧ exe.target = opt.target ∧
        FiniteModule.translateFn a.linked.exe.env entry exe = some image ∧
        FiniteModule.widthOf exe.result = some image.result ∧
        image.blocks.map FiniteCalls.blockTrace =
          FiniteCalls.expectedBlocks exe.coreId image.result exe.blocks.toList 0 ∧
        FiniteJoins.Corresponds opt image ∧ FiniteJoins.Corresponds exe image := by
  have accepted := a.lowered
  simp only [FiniteModule.lower, FiniteModule.translate, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨code, ⟨entry, atEntry, _, _, functions, emitted, final⟩, certified⟩ := accepted
  obtain ⟨images, mapped, layout⟩ := emitted_images _ _ _ _ emitted
  have size := (Support.mapM_some_index mapped).1
  have aligned := a.linked.lowering
  simp only [MidIR.PackageLink.aligned, Bool.and_eq_true, beq_iff_eq] at aligned
  have executed := a.linked.executed
  simp only [MidIR.Module.execute, bind, Option.bind_eq_some_iff] at executed
  obtain ⟨_, _, funcs, converted, endExec⟩ := executed
  have list : a.linked.opt.functions.toList.mapM (MidIR.Function.execute a.linked.opt.env) = some funcs.toList := by
    rw [← Array.toList_mapM, converted]; rfl
  refine ⟨entry, images, atEntry, mapped, ?_, ?_, ?_⟩
  · rw [size, ← Option.some.inj endExec]
    simpa using ((Support.mapM_some_index list).1.trans (by simpa using aligned.1.symm))
  · rw [certified_code certified, ← Option.some.inj final]
    simpa using congrArg (· ++ [FiniteModule.hostMain entry]) layout
  · intro i image atImage
    have slot := ((Support.mapM_some_index mapped).2 i).trans atImage
    simp only [Array.getElem?_toList] at slot
    obtain ⟨exe, atExe, lowered⟩ := Option.bind_eq_some_iff.mp slot
    obtain ⟨id, orig, key, target, opt, atId, found, symbol, origin, valid, signature, atOpt, remap, same⟩ :=
      PackageLink.executed_origin a.linked atExe
    have step := (Support.mapM_some_index list).2 i
    simp only [Array.getElem?_toList, atOpt, Option.bind_some] at step
    have localSlot := atExe
    rw [← Option.some.inj endExec] at localSlot
    have joins := FiniteJoins.translate_joins lowered
    obtain ⟨width, calls⟩ := FiniteCalls.translate_calls lowered
    exact ⟨id, orig, key, target, opt, exe, atId, found, symbol, origin, valid, signature,
      atOpt, remap, atExe, same, lowered, width, calls, FiniteJoins.before_execute (step.trans localSlot) joins, joins⟩

open VastitasKernel.MidIR Indexed.FunctionSource.Compiler in
/-- A selected method retains its checked family, specialization and signature
at the local LLVM body slot, even when other slots emit table helpers. The
equations describe the entire parsed executable and its function revision. -/
theorem dispatch_method_bytes {json main header} {req : ResourceSource.Wire.CheckedInput json main}
    (a : LLVM.FiniteProgram.Artifact req header) (bytes : List UInt8)
    (parsed : FiniteModule.parse bytes = some a.model) (call : DispatchCall)
    (recorded : call ∈ req.checked.pureProgram.executable.lowered.dispatchCalls)
    {i : Nat} (relocated : a.linked.originals[i]? = some call.emittedId) :
    ∃ (entry : Nat) (images : List FiniteModule.FunctionImage), ∃ image family orig opt exe,
      req.checked.pureProgram.compiler.input.dispatch.families[call.target.owner]? = some family ∧
      call.key ∈ family.domain ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      req.checked.pureProgram.compiler.input.dispatch.definitions[(call.method, call.key)]? = some call.definition ∧
      (VastitasKernel.MidIR.PackageLink.core req).functions.toArray[call.emittedId]? = some orig ∧
      a.linked.opt.functions[i]? = some opt ∧ a.linked.exe.functions[i]? = some exe ∧
      exe.target = opt.target ∧ exe.target.family = ⟨orig.definition⟩ ∧ exe.target.symbol = i ∧
      exe.target.key = Key.mk call.definition [] ∧
      a.linked.exe.entry = some entry ∧ FiniteModule.translateFn a.linked.exe.env entry exe = some image ∧
      image.blocks.map FiniteCalls.blockTrace =
        FiniteCalls.expectedBlocks exe.coreId image.result exe.blocks.toList 0 ∧
      FiniteJoins.Corresponds opt image ∧ FiniteJoins.Corresponds exe image ∧
      images[i]? = some image ∧ a.model.code.functions =
        (images.zipIdx.flatMap fun (g,j) => g.helpers.toList ++ [g.body j]) ++ [FiniteModule.hostMain entry] ∧
      a.linked.opt.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked ∧
      a.linked.exe.revision = a.linked.opt.revision ∧ bytes = FiniteModule.print a.model := by
  obtain ⟨entry, images, atEntry, _, size, layout, slots⟩ := function_inventory a
  have bound : i < images.length := size ▸ (Array.getElem?_eq_some_iff.mp relocated).1
  let image := images[i]
  have atImage : images[i]? = some image := List.getElem?_eq_getElem bound
  obtain ⟨id, orig, key, target, opt, exe, atId, found, _, origin, _, signature, atOpt, remap, atExe, same,
    lowered, _, calls, optJoins, exeJoins⟩ :=
    slots i image atImage
  cases Option.some.inj (atId.symm.trans relocated)
  let src := req.checked.pureProgram.executable
  obtain ⟨family, atFamily, domain, selected, definition⟩ :=
    (IndexedDispatch.dispatch_call_selected src call recorded).2.2.2
  have keyEq := Option.some.inj (origin.symm.trans (IndexedDispatch.dispatch_call_emitted src call recorded))
  simp only [CallTarget.ofCore, bind, Option.bind_eq_some_iff] at signature
  obtain ⟨_, _, _, _, result⟩ := signature
  cases Option.some.inj result
  exact ⟨entry, images, image, family, orig, opt, exe, atFamily, domain, selected, definition, found,
    atOpt, atExe, same, by rw [same, remap], by rw [same, remap], by simpa [same, remap] using keyEq,
    atEntry, lowered, calls, optJoins, exeJoins, atImage, layout, a.linked.revision,
    (execute_identity _ _ a.linked.executed).2,
    (FiniteModule.parse_iff _ _).mp parsed⟩

end VastitasOracle.FiniteProgram
