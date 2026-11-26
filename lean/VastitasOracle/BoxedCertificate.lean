import VastitasOracle.CertificatePackages
import VastitasOracle.ExactProgram
import VastitasOracle.IndexedReverseCore
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
  packages : CertificatePackages.Graph
  header : TargetHeader
  code : ExactProgram.Code
  bytes : List UInt8
  value : Int

/-- A stage certificate never turns an unchecked wire into an accepted program. -/
structure Valid (s : Subject) : Prop where
  input : s.revision.getObjVal? "input" = .ok s.wire
  physical : PhysicalSources.layout s.wire = .ok s.sources
  owners : CertificatePackages.read s.wire = .ok s.packages
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

/-- The physical inputs of the selected certificate also fix each package's dependency
aliases and its complete optional legacy geometry export. -/
theorem published_manifest_bindings {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain) (disk : p.req.input.root ≠ flatPackageId.source)
    {pkg : VastitasKernel.ResourceSource.Package} (member : pkg ∈ p.req.input.packages) :
    ManifestBindings.Corresponds s.sources pkg := by
  obtain ⟨layout, physical, bindings⟩ := ResourceSource.physical_manifest_bindings p.req disk
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  exact same ▸ bindings pkg member

/-- The closed certificate and the public checker recover the same package
identities, root and ordered dependency targets before method selection. -/
theorem published_packages {s : Subject} (v : Valid s) {requireMain : Bool} (p : Publication s requireMain) :
    CertificatePackages.ofProgram p.req.input = s.packages :=
  Except.ok.inj ((CertificatePackages.of_decoded p.req.decoded).symm.trans v.owners)

/-- Capture all fields in one execution of the real public emitter. The typed
publication equation stays available to the composition theorem. -/
def capture (wire : Lean.Json) (header : TargetHeader) (requireMain : Bool) :
    Option ((s : Subject) × Publication s requireMain) :=
  match h : Emission.check wire header requireMain with
  | .ok (.exactProgram (main := m) (req := req) a text parsed) =>
    (PhysicalSources.layout wire).toOption.map fun sources =>
      let s : Subject := ⟨wire, a.linked.exe.revision, sources, CertificatePackages.ofProgram req.input, header, a.model, text.toUTF8.data.toList, a.value⟩
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

/-- A physical implementation, classification or indexed family in a published boxed program
resolves to the same entry in Core and both MidIR environments. Its source
layout, function revision and complete LLVM bytes belong to this certificate. -/
theorem published_indexed_definition {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ p.req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    (action : Indexed.Source.ResolveM Indexed.Entry)
    (selected : ResourceSource.Wire.definitionEntry? p.req.checked.pureProgram.compiler.input.body.index
      ⟨⟨pkg.id, m.pureModule.module.path⟩, d.name⟩ d.body = some action) :
    (∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds s.sources checked.finiteSites
        ⟨pkg.id.source, m.pureModule.module.path, d.span, d.isPublic, FiniteSourceFiles.indexedSyntax d⟩) ∧
    (∃ entry, action.run' [] = .ok entry ∧ entry ∈ (VastitasKernel.MidIR.PackageLink.core p.req).declarations.indexed ∧
      entry ∈ p.artifact.linked.opt.env ∧ entry ∈ p.artifact.linked.exe.env) ∧
    p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
    p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨expected, layout, checked, collected, physical, scan, _, site⟩ :=
    ResourceSource.physical_indexed_item p.req hp hm hd
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  subst layout
  obtain ⟨entry, member, resolved⟩ := ResourceSource.resolved_physical_definition p.req hp hm hd action selected
  obtain ⟨env, rev⟩ := VastitasKernel.MidIR.execute_identity _ _ p.artifact.linked.executed
  have optMember : entry ∈ p.artifact.linked.opt.env := p.artifact.linked.environment.symm ▸ member
  exact ⟨⟨expected, checked, collected, scan, site⟩, ⟨entry, resolved, member, optMember, env.symm ▸ optMember⟩,
    rev.symm.trans p.revision, p.revision, (corresponds valid p).1⟩

/-- A published integer program retains the ordered, resolved package cases in
its Core declaration table. Its source layout, function revision and emitted
bytes all belong to that same publication. -/
theorem published_indexed_package {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ p.req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    {cases : List Indexed.Source.PackageShape} (body : d.body = .package cases) :
    let scope := (⟨pkg.id, m.pureModule.module.path⟩ : Namespace.Scope)
    let index := p.req.checked.pureProgram.compiler.input.body.index
    (∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds s.sources checked.finiteSites
        ⟨pkg.id.source, scope.path, d.span, d.isPublic, .indexedHeader "package" d.name (FiniteSourceFiles.packageFields cases)⟩) ∧
    (∃ entry ∈ (VastitasKernel.MidIR.PackageLink.core p.req).declarations.packages,
      ((do return ⟨⟨scope, d.name⟩, ← cases.mapM (Indexed.Source.resolveShape index scope)⟩) :
        Indexed.Source.ResolveM Indexed.Core.NamedPackage).run' [] = .ok entry) ∧
    p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
    p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨⟨expected, layout, checked, collected, physical, scan, site⟩, member⟩ :=
    ResourceSource.physical_indexed_package p.req hp hm hd body
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  subst layout
  exact ⟨⟨expected, checked, collected, scan, site⟩, member,
    (VastitasKernel.MidIR.execute_identity _ _ p.artifact.linked.executed).2.symm.trans p.revision,
    p.revision, (corresponds valid p).1⟩

/-- A published primitive retains its elaborated binding even when reverse
compilation appends generated primitives. Both nominal lookups and the bytes
are from the same physical program and checked function revision. -/
theorem published_indexed_primitive {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ p.req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    {binding : Indexed.Source.Primitive} (body : d.body = .primitive binding) :
    let owner : Indexed.DeclId := ⟨⟨pkg.id, m.pureModule.module.path⟩, d.name⟩
    let resolved := p.req.checked.pureProgram.authority.headers.declarations.resolved
    (∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds s.sources checked.finiteSites
        ⟨pkg.id.source, owner.scope.path, d.span, d.isPublic, .indexedPrimitive d.name binding⟩) ∧
    Indexed.Source.lower p.req.input.pureProgram.source.headers = .ok resolved ∧
    (∃ value, resolved.declarations.primitive? owner = some value ∧
      (VastitasKernel.MidIR.PackageLink.core p.req).declarations.primitive? owner = some value) ∧
    p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
    p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨⟨expected, layout, checked, collected, physical, scan, site⟩, lowered, entry, member, owner⟩ :=
    ResourceSource.physical_indexed_primitive p.req hp hm hd body
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  subst layout
  obtain ⟨resolved, returned⟩ := IndexedReverseCore.elaborated_primitive p.req.checked.pureProgram member
  exact ⟨⟨expected, checked, collected, scan, site⟩, lowered,
    ⟨entry.binding, owner ▸ resolved, owner ▸ returned⟩,
    (VastitasKernel.MidIR.execute_identity _ _ p.artifact.linked.executed).2.symm.trans p.revision,
    p.revision, (corresponds valid p).1⟩

/-- Publication retains each indexed value under its physical source owner in
the elaborated table, Core and both MidIR phases, with the full LLVM bytes. -/
theorem published_indexed_value {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ p.req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    (indexed : d.body.category = 0) :
    let owner : Indexed.DeclId := ⟨⟨pkg.id, m.pureModule.module.path⟩, d.name⟩
    let resolved := p.req.checked.pureProgram.authority.headers.declarations.resolved
    (∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds s.sources checked.finiteSites
        ⟨pkg.id.source, owner.scope.path, d.span, d.isPublic, (FiniteSourceFiles.indexedSyntax d)⟩) ∧
    Indexed.Source.lower p.req.input.pureProgram.source.headers = .ok resolved ∧
    (∃ value, Indexed.lookup resolved.declarations.indexed owner = some value ∧
      Indexed.lookup (VastitasKernel.MidIR.PackageLink.core p.req).declarations.indexed owner = some value ∧
      Indexed.lookup p.artifact.linked.opt.env owner = some value ∧ Indexed.lookup p.artifact.linked.exe.env owner = some value) ∧
    p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
    p.text.toUTF8.data.toList = s.bytes := by
  obtain ⟨⟨expected, layout, checked, collected, physical, scan, site⟩, lowered, entry, member, owner⟩ :=
    ResourceSource.physical_indexed_value p.req hp hm hd indexed
  have same := Except.ok.inj (physical.symm.trans valid.physical)
  subst layout
  obtain ⟨resolved, returned⟩ := IndexedReverseCore.elaborated_indexed p.req.checked.pureProgram member
  have opt := p.artifact.linked.environment
  have exe := (VastitasKernel.MidIR.execute_identity _ _ p.artifact.linked.executed).1
  exact ⟨⟨expected, checked, collected, scan, site⟩, lowered,
    ⟨entry.declaration, owner ▸ resolved, owner ▸ returned,
      by rw [opt]; exact owner ▸ returned, by rw [exe, opt]; exact owner ▸ returned⟩,
    (VastitasKernel.MidIR.execute_identity _ _ p.artifact.linked.executed).2.symm.trans p.revision,
    p.revision, (corresponds valid p).1⟩

/-- A metric, evidence or frame in a published program has the same completed
value under its source owner in elaboration, Core and both MidIR environments. -/
theorem published_metric_or_frame {s : Subject} (valid : Valid s) {requireMain : Bool}
    (p : Publication s requireMain)
    {pkg : VastitasKernel.ResourceSource.Package} (hp : pkg ∈ p.req.input.packages)
    {m : VastitasKernel.ResourceSource.Module} (hm : m ∈ pkg.modules)
    {d : Indexed.Source.Declaration} (hd : d ∈ m.pureModule.declarations)
    (selected : FiniteSourceFiles.metricOrFrame d.body = true) :
    let owner : Indexed.DeclId := ⟨⟨pkg.id, m.pureModule.module.path⟩, d.name⟩
    let resolved := p.req.checked.pureProgram.authority.headers.declarations.resolved
    (∃ expected checked, EditSourceFiles.collect p.req.input = .ok expected ∧
      ExactModelSource.scanFiles s.sources p.req.input EditSourceFiles.relevant {edits := some expected} = .ok checked ∧
      FiniteSourceFiles.Corresponds s.sources checked.finiteSites
        ⟨pkg.id.source, owner.scope.path, d.span, d.isPublic, .indexedMetricOrFrame d⟩) ∧
    Indexed.Source.lower p.req.input.pureProgram.source.headers = .ok resolved ∧
    (∃ value, Indexed.lookup resolved.declarations.indexed owner = some value ∧
      Indexed.lookup (VastitasKernel.MidIR.PackageLink.core p.req).declarations.indexed owner = some value ∧
      Indexed.lookup p.artifact.linked.opt.env owner = some value ∧ Indexed.lookup p.artifact.linked.exe.env owner = some value) ∧
    p.artifact.linked.opt.revision = s.revision ∧ p.artifact.linked.exe.revision = s.revision ∧
    p.text.toUTF8.data.toList = s.bytes := by
  have shape := FiniteSourceFiles.metricOrFrame_syntax d selected
  simpa only [shape.1] using published_indexed_value valid p hp hm hd shape.2

end VastitasOracle.BoxedCertificate
