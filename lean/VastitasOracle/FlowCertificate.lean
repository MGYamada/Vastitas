import VastitasOracle.FlowCertificate.Subject
import VastitasOracle.ExactFlow
import VastitasOracle.Support
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
  have converted := p.artifact.linked.executed
  simp only [Module.execute, bind, Option.bind_eq_some_iff] at converted
  obtain ⟨_, _, _, hfs, endExec⟩ := converted
  rw [← Option.some.inj endExec] at atExe
  obtain ⟨opt, atOpt, step⟩ := Option.bind_eq_some_iff.mp ((map_at hfs i).trans atExe)
  have targetEq : exe.target = opt.target := by
    simp only [Function.execute, bind, Option.bind_eq_some_iff] at step
    obtain ⟨_, _, _, _, _, _, last⟩ := step
    cases Option.some.inj last
    rfl
  obtain ⟨id, orig, key, target, original, found, same, origin, valid, signature, relocated⟩ :=
    VastitasKernel.MidIR.PackageLink.aligned_target p.req _ _ p.artifact.linked.lowering i opt atOpt
  exact ⟨id, orig, key, target, opt, exe, original, found, same, origin, valid, signature,
    atOpt, relocated, Option.some.inj endExec ▸ atExe, targetEq, lowered,
    (execute_identity _ _ p.artifact.linked.executed).2.symm.trans p.revision,
    p.revision, (corresponds v p).1⟩

end VastitasOracle.FlowCertificate
