import VastitasOracle.FlowCertificate.Subject
import VastitasOracle.ExactFlow
import VastitasOracle.Support
import VastitasOracle.ResourceSource
import VastitasOracle.IndexedDispatch
import VastitasOracle.IndexedReverseCore
import VastitasKernel.LLVM.Emission

set_option autoImplicit false

namespace VastitasOracle.FlowCertificate
open VastitasKernel VastitasKernel.LLVM

/-- Witnesses that this particular subject came from the exact public result. -/
structure Publication (s : Subject) (requireMain : Bool) where
  main : Bool
  req : ResourceSource.Wire.CheckedInput s.wire main
  artifact : LLVM.ExactFlow.Artifact req s.header
  text : String
  parsed : LLVM.ExactFlow.parse text.toUTF8.data.toList = some artifact.model
  returned : Emission.check s.wire s.header requireMain = .ok (.exactFlow artifact text parsed)
  revision : artifact.linked.exe.revision = s.revision
  graph : artifact.model = s.code

/-- Capture all fields in one execution of the real public emitter. The typed
publication equation stays available to the composition theorem. -/
def capture (wire : Lean.Json) (header : TargetHeader) (requireMain : Bool) :
    Option ((s : Subject) × Publication s requireMain) :=
  match h : Emission.check wire header requireMain with
  | .ok (.exactFlow (main := m) (req := req) a text parsed) =>
    (PhysicalSources.layout wire).toOption.map fun sources =>
      let s : Subject := ⟨wire, a.linked.exe.revision, sources, header, a.model, text.toUTF8.data.toList, a.value⟩
      ⟨s, ⟨m, req, a, text, parsed, h, rfl, rfl⟩⟩
  | _ => none

theorem corresponds {s : Subject} (valid : Valid s) {requireMain : Bool} (p : Publication s requireMain) :
    p.text.toUTF8.data.toList = s.bytes ∧
    LLVM.ExactFlow.parse s.bytes = some s.code ∧
    p.artifact.linked.exe.revision = s.revision ∧
    FiniteCost.coreEntry (VastitasKernel.MidIR.PackageLink.core p.req) p.artifact.fuel = some (.integer s.value) ∧
    PackageLink.entry p.artifact.linked.opt p.artifact.fuel = some (.integer s.value) ∧
    PackageLink.entry p.artifact.linked.exe p.artifact.fuel = some (.integer s.value) ∧
    (ExitMain.statusOf p.artifact.value).toNat = (s.value % 256).toNat ∧
    PhysicalSources.layout s.wire = .ok s.sources ∧
    s.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput s.wire) p.req.checked := by
  have obs := ExactFlow.correspondence p.artifact _ p.parsed
  have bytes := obs.1.trans ((congrArg LLVM.ExactFlow.Code.print p.graph).trans valid.printed)
  have value : p.artifact.value = s.value := Option.some.inj
    (p.artifact.modeled.symm.trans ((congrArg LLVM.ExactFlow.Code.entryValue p.graph).trans valid.evaluated))
  refine ⟨bytes, bytes ▸ p.graph ▸ p.parsed, p.revision, ?_, ?_, ?_, ?_, valid.physical,
    p.revision.symm.trans obs.2.2.2.1⟩
  · exact value ▸ p.artifact.core
  · exact value ▸ obs.2.2.2.2.2.1
  · exact value ▸ obs.2.2.2.2.2.2.1
  · simp [value, ExitMain.statusOf_exact]

/-- The physical file of each package root belongs to the source layout of
this published graph and its complete LLVM bytes. -/
theorem published_root_modules {s : Subject} (v : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) (disk : p.req.input.root ≠ flatPackageId.source) :
    ∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      (∀ pkg ∈ p.req.input.packages, FiniteSourceFiles.RootCorresponds s.sources checked.packageRoots pkg) ∧
      p.artifact.linked.exe.revision = s.revision ∧ p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨expected, layout, checked, inputs, physical, scan, roots⟩ := ResourceSource.physical_root_modules p.req disk
  cases Except.ok.inj (physical.symm.trans v.physical)
  exact ⟨expected, checked, inputs, scan, roots, p.revision, (corresponds v p).1⟩

private theorem map_at {α β : Type} {xs : Array α} {ys : Array β}
    {f : α → Option β} (mapped : xs.mapM f = some ys) (i : Nat) :
    xs[i]?.bind f = ys[i]? := by
  have list : xs.toList.mapM f = some ys.toList := by rw [← Array.toList_mapM, mapped]; rfl
  simpa using (Support.mapM_some_index list).2 i

open VastitasKernel.MidIR in
/-- Each function slot in the published graph, including an uncalled method,
comes from the same checked Core owner and specialization in both SSA phases.
Only the dense module address replaces the original Core symbol. -/
theorem published_function {s : Subject} (v : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) (i : Nat) (body : LLVM.ExactFlow.Func)
    (emitted : s.code.functions[i]? = some body) :
    ∃ id orig key target opt exe,
      p.artifact.linked.originals[i]? = some id ∧
      (VastitasKernel.MidIR.PackageLink.core p.req).functions.toArray[id]? = some orig ∧
      orig.id = id ∧ p.req.checked.pureProgram.executable.lowered.origins[id]? = some key ∧
      validOrigin p.req.checked.pureProgram orig key = true ∧ CallTarget.ofCore orig key = some target ∧
      p.artifact.linked.opt.functions[i]? = some opt ∧ opt.target = {target with symbol := i} ∧
      p.artifact.linked.exe.functions[i]? = some exe ∧ exe.target = opt.target ∧
      LLVM.ExactFlow.translateFn p.artifact.linked.exe.env exe = some body ∧
      p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
      p.text.toUTF8.data.toList = s.bytes := by
  have mapped := p.artifact.lowered
  simp only [LLVM.ExactFlow.translate, bind, Option.bind_eq_some_iff] at mapped
  obtain ⟨_, _, funcs, hf, _, _, _, _, endFlow⟩ := mapped
  rw [← p.graph, ← Option.some.inj endFlow] at emitted
  obtain ⟨exe, atExe, lowered⟩ := Option.bind_eq_some_iff.mp ((map_at hf i).trans emitted)
  obtain ⟨id, orig, key, target, opt, original, found, same, origin, valid, signature, atOpt, relocated, targetEq⟩ :=
    PackageLink.executed_origin p.artifact.linked atExe
  exact ⟨id, orig, key, target, opt, exe, original, found, same, origin, valid, signature,
    atOpt, relocated, atExe, targetEq, lowered,
    (execute_identity _ _ p.artifact.linked.executed).2.symm.trans p.revision,
    p.revision, (corresponds v p).1⟩

open VastitasKernel.MidIR in
/-- Read every direct invocation from the parsed LLVM caller. Both SSA phases
preserve the instruction order. Remapping the local addresses recovers precisely
the multiset of call occurrences in the final Core body. -/
theorem published_calls {s : Subject} (v : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) {i : Nat} {body : LLVM.ExactFlow.Func}
    (emitted : s.code.functions[i]? = some body) :
    ∃ (id : Nat) (orig : Indexed.Core.Function) (opt : Function .optimization) (exe : Function .execution) (called : List Nat),
      p.artifact.linked.originals[i]? = some id ∧
      (VastitasKernel.MidIR.PackageLink.core p.req).functions.toArray[id]? = some orig ∧
      p.artifact.linked.opt.functions[i]? = some opt ∧ p.artifact.linked.exe.functions[i]? = some exe ∧
      VastitasKernel.MidIR.PackageLink.callIds opt = VastitasKernel.MidIR.PackageLink.callIds exe ∧
      VastitasKernel.MidIR.PackageLink.callIds exe = ExactFlow.callIds body ∧
      (ExactFlow.callIds body).mapM (p.artifact.linked.originals[·]?) = some called ∧
      called.Perm orig.body.callIds ∧ p.artifact.linked.exe.revision = s.revision ∧
      LLVM.ExactFlow.parse s.bytes = some s.code := by
  obtain ⟨_, _, _, _, opt, exe, _, _, _, _, _, _, atOpt, _, atExe, _, lowered, _, rev, _⟩ :=
    published_function v p i body emitted
  obtain ⟨id, orig, called, atId, found, mapped, counts⟩ :=
    VastitasKernel.MidIR.PackageLink.aligned_calls p.artifact.linked.lowering atOpt
  have executed := p.artifact.linked.executed
  simp only [Module.execute, bind, Option.bind_eq_some_iff] at executed
  obtain ⟨_, _, _, translated, final⟩ := executed
  rw [← Option.some.inj final] at atExe
  have step := (map_at translated i).trans atExe
  rw [atOpt] at step
  have same := ExactFlow.execute_calls step
  have llvm := ExactFlow.translate_calls lowered
  exact ⟨id, orig, opt, exe, called, atId, found, atOpt, Option.some.inj final ▸ atExe,
    same, llvm, (by rwa [← llvm, ← same]), counts, rev, (corresponds v p).2.1⟩

open VastitasKernel.MidIR Indexed.FunctionSource.Compiler in
/-- A retained dispatch callee has the method and specialization selected by
assembly in the revision of these published bytes. -/
theorem published_dispatch_method {s : Subject} (v : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) (call : DispatchCall)
    (recorded : call ∈ p.req.checked.pureProgram.executable.lowered.dispatchCalls)
    (i : Nat) (body : LLVM.ExactFlow.Func) (emitted : s.code.functions[i]? = some body)
    (relocated : p.artifact.linked.originals[i]? = some call.emittedId) :
    ∃ family orig opt exe,
      p.req.checked.pureProgram.compiler.input.dispatch.families[call.target.owner]? = some family ∧
      call.key ∈ family.domain ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      p.req.checked.pureProgram.compiler.input.dispatch.definitions[(call.method, call.key)]? = some call.definition ∧
      (VastitasKernel.MidIR.PackageLink.core p.req).functions.toArray[call.emittedId]? = some orig ∧
      p.artifact.linked.opt.functions[i]? = some opt ∧ p.artifact.linked.exe.functions[i]? = some exe ∧
      exe.target = opt.target ∧ exe.target.family = ⟨orig.definition⟩ ∧ exe.target.symbol = i ∧
      exe.target.key = Key.mk call.definition [] ∧ LLVM.ExactFlow.translateFn p.artifact.linked.exe.env exe = some body ∧
      p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
      p.text.toUTF8.data.toList = s.bytes := by
  let src := p.req.checked.pureProgram.executable
  obtain ⟨fam, family, domain, chosen, definition⟩ :=
    (IndexedDispatch.dispatch_call_selected src call recorded).2.2.2
  obtain ⟨id, orig, key, target, opt, exe, atId, found, _, origin, _, signature, atOpt,
    remap, atExe, same, lowered, optRev, exeRev, bytes⟩ := published_function v p i body emitted
  cases Option.some.inj (atId.symm.trans relocated)
  have keyEq := Option.some.inj (origin.symm.trans (IndexedDispatch.dispatch_call_emitted src call recorded))
  simp only [CallTarget.ofCore, bind, Option.bind_eq_some_iff] at signature
  obtain ⟨_, _, _, _, result⟩ := signature
  cases Option.some.inj result
  exact ⟨fam, orig, opt, exe, family, domain, chosen, definition, found, atOpt, atExe, same,
    by rw [same, remap], by rw [same, remap], by simpa [same, remap] using keyEq,
    lowered, optRev, exeRev, bytes⟩

private theorem map_size {α β : Type} {xs : Array α} {ys : Array β} {f : α → Option β}
    (mapped : xs.mapM f = some ys) : ys.size = xs.size := by
  have h : xs.toList.mapM f = some ys.toList := by rw [← Array.toList_mapM, mapped]; rfl
  simpa using (Support.mapM_some_index h).1

open VastitasKernel.MidIR in
private theorem published_size {s : Subject} {requireMain : Bool} (p : Publication s requireMain) :
    s.code.functions.size = p.artifact.linked.originals.size := by
  have aligned := p.artifact.linked.lowering
  simp only [VastitasKernel.MidIR.PackageLink.aligned, Bool.and_eq_true, beq_iff_eq] at aligned
  have ex := p.artifact.linked.executed
  simp only [Module.execute, bind, Option.bind_eq_some_iff] at ex
  obtain ⟨_, _, _, hfs, endExec⟩ := ex
  have tr := p.artifact.lowered
  simp only [LLVM.ExactFlow.translate, bind, Option.bind_eq_some_iff] at tr
  obtain ⟨_, _, _, hllvm, _, _, _, _, endFlow⟩ := tr
  rw [← p.graph, ← Option.some.inj endFlow]
  exact (map_size hllvm).trans (by rw [← Option.some.inj endExec]; exact (map_size hfs).trans aligned.1.symm)

open VastitasKernel.MidIR Indexed.FunctionSource.Compiler in
/-- An actual direct LLVM invocation whose remapped target belongs to a dispatch
definition has a recorded call from this Core caller. Assembly selects its printed
callee at the same revision. The witness and callee are recovered from the graph. -/
theorem published_dispatch_call {s : Subject} (v : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) {i slot : Nat} {body : LLVM.ExactFlow.Func}
    (printed : s.code.functions[i]? = some body) (invoked : slot ∈ ExactFlow.callIds body)
    (generic : (p.artifact.linked.originals[slot]?).any (dispatchTarget
      (dispatchDefinitions p.req.checked.pureProgram.compiler.input)
      p.req.checked.pureProgram.executable.lowered) = true) :
    ∃ callerId caller call family callee opt exe,
      p.artifact.linked.originals[i]? = some callerId ∧
      (VastitasKernel.MidIR.PackageLink.core p.req).functions.toArray[callerId]? = some caller ∧
      call ∈ p.req.checked.pureProgram.executable.lowered.dispatchCalls ∧
      p.req.checked.pureProgram.executable.lowered.origins[caller.id]? = some call.caller ∧
      p.artifact.linked.originals[slot]? = some call.emittedId ∧
      call.emittedId ∈ caller.body.callIds ∧
      (Namespace.resolve p.req.checked.pureProgram.compiler.input.body.index
        call.scope call.path.path call.path.span).toOption = some call.target ∧
      p.req.checked.pureProgram.compiler.input.dispatch.families[call.target.owner]? = some family ∧
      Dispatch.Selection family.nominals.hierarchy family.checked.methods call.key (some call.method) ∧
      p.req.checked.pureProgram.compiler.input.dispatch.definitions[(call.method, call.key)]? = some call.definition ∧
      s.code.functions[slot]? = some callee ∧ p.artifact.linked.opt.functions[slot]? = some opt ∧
      p.artifact.linked.exe.functions[slot]? = some exe ∧ exe.target = opt.target ∧
      exe.target.key = Key.mk call.definition [] ∧ exe.target.symbol = slot ∧
      LLVM.ExactFlow.translateFn p.artifact.linked.exe.env exe = some callee ∧
      p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
      p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨callerId, caller, _, _, _, atCaller, found, _, _, _, _, mapped, perm, _, _⟩ :=
    published_calls v p printed
  obtain ⟨index, atIndex⟩ := List.getElem?_of_mem invoked
  obtain ⟨id, atId, remap⟩ := Support.mapM_some_getElem? mapped atIndex
  have called := perm.mem_iff.mp (List.mem_of_getElem? atId)
  let src := p.req.checked.pureProgram
  have valid := src.compiled.validated
  rw [show src.compiled.entries = [] from p.artifact.linked.noReverse] at valid
  have unchanged := (IndexedReverseCore.validate_no_entries valid).trans src.executable.coreInput
  have present : caller ∈ src.executable.lowered.module.functions := by
    rw [← unchanged]
    exact List.mem_of_getElem? (by simpa using found)
  obtain ⟨call, recorded, origin, same⟩ := IndexedDispatch.core_dispatch_call_recorded src.executable
    caller present id called (by simpa [remap] using generic)
  have relocated := remap.trans (congrArg some same.symm)
  have bound : slot < s.code.functions.size := by
    rw [published_size p]
    exact (Array.getElem?_eq_some_iff.mp remap).1
  have atCallee := Array.getElem?_eq_getElem (xs := s.code.functions) bound
  obtain ⟨family, _, opt, exe, fam, _, selection, defn, _, atOpt, atExe, target,
    _, symbol, key, translated, revOpt, revExe, bytes⟩ :=
    published_dispatch_method v p call recorded slot _ atCallee relocated
  exact ⟨callerId, caller, call, family, _, opt, exe, atCaller, found, recorded, origin,
    relocated, same ▸ called, (IndexedDispatch.dispatch_call_selected src.executable call recorded).2.2.1,
    fam, selection, defn, atCallee, atOpt, atExe, target, key, symbol, translated, revOpt, revExe, bytes⟩

end VastitasOracle.FlowCertificate
