import VastitasOracle.ExactProgram
import VastitasOracle.ResourceSource
import VastitasKernel.LLVM.Emission

set_option autoImplicit false

/-! The concrete proof subject for the boxed execution-to-bytes stage. Its
wire, revision, target, complete module and mathematical value are explicit
data. The compiled checker supplies the linked source artifact separately. -/
namespace VastitasOracle.BoxedCertificate
open VastitasKernel VastitasKernel.LLVM

structure Subject where
  wire : Lean.Json
  revision : Lean.Json
  sources : PhysicalSources.Layout
  header : TargetHeader
  code : ExactProgram.Code
  bytes : List UInt8
  value : Int

/-- A stage certificate never turns an unchecked wire into an accepted program. -/
structure Valid (s : Subject) : Prop where
  input : s.revision.getObjVal? "input" = .ok s.wire
  physical : PhysicalSources.layout s.wire = .ok s.sources
  target : s.code.header = s.header
  typed : s.code.valid = true
  evaluated : s.code.entryValue = some s.value
  printed : s.code.print = s.bytes

/-- Check the two printed header lines and the remaining text separately,
then recover equality of every octet, including both terminal newlines. -/
theorem printedLines (c : LLVM.ExactProgram.Code) (header : List UInt8) (lines : List String)
    (h : c.header.print = header) (l : c.bodyLines = lines) :
    c.print = header ++ ("\n" ++ String.intercalate "\n" lines ++ "\n").toUTF8.data.toList := by
  unfold LLVM.ExactProgram.Code.print
  rw [h, l]

/-- Witnesses that this particular subject came from the exact public result. -/
structure Publication (s : Subject) (requireMain : Bool) where
  main : Bool
  req : ResourceSource.Wire.CheckedInput s.wire main
  artifact : LLVM.ExactProgram.Artifact req s.header
  text : String
  parsed : LLVM.ExactProgram.parse text.toUTF8.data.toList = some artifact.model
  returned : Emission.check s.wire s.header requireMain = .ok (.exactProgram artifact text parsed)
  revision : artifact.linked.exe.revision = s.revision
  graph : artifact.model = s.code

/-- The manifest of each package in this published module occurs in the
physical files bound to the stage certificate, with the same nominal owner. -/
theorem published_manifest_metadata {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) (disk : p.req.input.root ≠ flatPackageId.source)
    {pkg : VastitasKernel.ResourceSource.Package} (member : pkg ∈ p.req.input.packages) :
    ∃ (i : Nat) (file : PhysicalSources.File), s.sources.files[i]? = some file ∧
      file.path = pkg.id.source.toUTF8 ∧
      ManifestMetadata.read? file.text = some ⟨pkg.id.name, pkg.id.version, currentEdition⟩ := by
  obtain ⟨layout, i, file, physical, atIndex, path, fields⟩ :=
    ResourceSource.physical_manifest_metadata p.req disk member
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  exact ⟨i, file, same ▸ atIndex, path, fields⟩

/-- Capture all fields in one execution of the real public emitter. The typed
publication equation stays available to the composition theorem. -/
def capture (wire : Lean.Json) (header : TargetHeader) (requireMain : Bool) :
    Option ((s : Subject) × Publication s requireMain) :=
  match h : Emission.check wire header requireMain with
  | .ok (.exactProgram (main := m) (req := req) a text parsed) =>
    (PhysicalSources.layout wire).toOption.map fun sources =>
      let s : Subject := ⟨wire, a.linked.exe.revision, sources, header, a.model, text.toUTF8.data.toList, a.value⟩
      ⟨s, ⟨m, req, a, text, parsed, h, rfl, rfl⟩⟩
  | _ => none

theorem corresponds {s : Subject} (valid : Valid s) {requireMain : Bool} (p : Publication s requireMain) :
    p.text.toUTF8.data.toList = s.bytes ∧
    LLVM.ExactProgram.parse s.bytes = some s.code ∧
    p.artifact.linked.exe.revision = s.revision ∧
    FiniteCost.coreEntry (VastitasKernel.MidIR.PackageLink.core p.req) p.artifact.fuel = some (.integer s.value) ∧
    PackageLink.entry p.artifact.linked.opt p.artifact.fuel = some (.integer s.value) ∧
    PackageLink.entry p.artifact.linked.exe p.artifact.fuel = some (.integer s.value) ∧
    (ExitMain.statusOf p.artifact.value).toNat = (s.value % 256).toNat ∧
    PhysicalSources.layout s.wire = .ok s.sources ∧
    s.revision = ResourceSource.FunctionRevision.artifact
      (ResourceSource.Wire.revisionInput s.wire) p.req.checked := by
  have obs := ExactProgram.correspondence p.artifact _ p.parsed
  have bytes := obs.1.trans ((congrArg LLVM.ExactProgram.Code.print p.graph).trans valid.printed)
  have value : p.artifact.value = s.value := Option.some.inj
    (p.artifact.modeled.symm.trans ((congrArg LLVM.ExactProgram.Code.entryValue p.graph).trans valid.evaluated))
  refine ⟨bytes, bytes ▸ p.graph ▸ p.parsed, p.revision, ?_, ?_, ?_, ?_, valid.physical,
    p.revision.symm.trans obs.2.2.2.1⟩
  · exact value ▸ p.artifact.core
  · exact value ▸ obs.2.2.2.2.2.1
  · exact value ▸ obs.2.2.2.2.2.2.1
  · simp [value, ExitMain.statusOf_exact]

end VastitasOracle.BoxedCertificate
