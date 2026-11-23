import VastitasKernel.ManifestMetadata
import VastitasKernel.PhysicalSources
import VastitasKernel.ResourceSource

set_option autoImplicit false

/-! Compare the aliases and explicit legacy geometry roles exported by each
file-backed package with its own physical manifest. -/
namespace VastitasKernel.ManifestBindings
open ResourceSource Indexed

abbrev Roles := List (List String × String)

private def settingRoles (setting : GeometrySetting TypePath) (sectionName : String) : Roles :=
  [("domain", setting.domain), ("marker", setting.marker), ("base_object", setting.baseObject),
   ("affine", setting.affine), ("base", setting.base), ("origin", setting.origin),
   ("identity", setting.identity), ("dimension", setting.dimension)].map fun (key, path) =>
      ([sectionName, key], path.name)

def roles (profile : GeometryProfile TypePath) : Roles :=
  [(["point"], profile.point.name), (["morphism"], profile.morphism.name),
   (["pointed"], profile.pointed.name), (["compose"], profile.compose.name), (["apply"], profile.apply.name)] ++
    settingRoles profile.scheme "scheme" ++ settingRoles profile.smooth "smooth"

def geometryMatches : Option (List (List String × ManifestMetadata.Written)) → Option (GeometryProfile TypePath) → Bool
  | none, none => true
  | some written, some profile => Finite.sameCounts (written.map fun (key, value) => (key, value.text)) (roles profile)
  | _, _ => false

def aliasesMatch (doc : ManifestMetadata.Document) (pkg : Package) : Bool :=
  Finite.sameCounts doc.paths.keys (pkg.dependencies.map (·.alias))

-- Shared lookup with the early package-identity check. Manifest labels are UTF-8.
def physicalFileIndex (layout : PhysicalSources.Layout) : Std.TreeMap String Nat := Id.run do
  let mut index := {}
  for file in layout.files, i in [:layout.files.size] do
    if let some path := String.fromUTF8? file.path then index := index.insert path i
  return index

def manifestFile? (layout : PhysicalSources.Layout) (index : Std.TreeMap String Nat)
    (owner : String) : Option PhysicalSources.File := do
  let file ← layout.files[← index.get? owner]?
  guard (file.path.data = owner.toUTF8.data)
  return file

def Corresponds (layout : PhysicalSources.Layout) (pkg : Package) : Prop :=
  ∃ file doc, manifestFile? layout (physicalFileIndex layout) pkg.id.source = some file ∧
    ManifestMetadata.readDocument? file.text = some doc ∧ aliasesMatch doc pkg = true ∧
    geometryMatches doc.geometry pkg.geometryCompat = true

private def mismatch (layout : PhysicalSources.Layout) (index : Std.TreeMap String Nat) (pkg : Package) : Bool :=
  match (manifestFile? layout index pkg.id.source).bind (fun file => ManifestMetadata.readDocument? file.text) with
  | none => true
  | some doc => !(aliasesMatch doc pkg && geometryMatches doc.geometry pkg.geometryCompat)

/-- Diagnostics pay for file-local line/column reconstruction only on failure. -/
private def valueSpan (file : PhysicalSources.File) (value : ManifestMetadata.Written) : Span := Id.run do
  let mut atByte := 0
  let mut line := 1
  let mut column := 1
  for ch in file.text do
    if atByte >= value.start then break
    atByte := atByte + ch.utf8Size
    if ch == '\n' then
      line := line + 1
      column := 1
    else column := column + 1
  return ⟨file.offset + value.start, file.offset + value.stop, line, column⟩

private def issue (layout : PhysicalSources.Layout) (index : Std.TreeMap String Nat) (pkg : Package) : Diagnostic := Id.run do
  let msg := s!"manifest {Lean.toJson pkg.id.source}"
  let error := fun (span : Span) (detail : String) => ({code := "E_MANIFEST_SOURCE", span, message := msg ++ ": " ++ detail} : Diagnostic)
  let some file := manifestFile? layout index pkg.id.source | return error {} "missing physical manifest"
  let first : Span := ⟨file.offset, file.offset, 1, 1⟩
  let some doc := ManifestMetadata.readDocument? file.text | return error first "invalid manifest fields"
  if !aliasesMatch doc pkg then
    let names := Std.HashSet.ofList (pkg.dependencies.map (·.alias))
    for (alias, dep) in doc.paths do
      unless names.contains alias do return error (valueSpan file dep.alias) s!"dependency alias {alias} is missing from the wire"
    return error first "a wire dependency alias is missing from the manifest"
  let expected := (pkg.geometryCompat.map roles).getD []
  for (key, value) in doc.geometry.getD [] do
    unless expected.lookup key == some value.text do
      return error (valueSpan file value) s!"geometry_compat.{String.intercalate "." key} differs from the wire export"
  return error first "geometry_compat export has missing fields or differs in presence"

def check (layout : PhysicalSources.Layout) (p : Program) : Except Diagnostic Unit := do
  if p.root == flatPackageId.source then return ()
  let index := physicalFileIndex layout
  if let some pkg := p.packages.find? (mismatch layout index) then throw (issue layout index pkg)

theorem check_sound {layout : PhysicalSources.Layout} {p : Program} (checked : check layout p = .ok ())
    (disk : p.root ≠ flatPackageId.source) {pkg : Package} (member : pkg ∈ p.packages) :
    Corresponds layout pkg := by
  simp [check, disk] at checked
  cases rejected : p.packages.find? (mismatch layout (physicalFileIndex layout)) with
  | some other => simp [rejected, throw] at checked
  | none =>
    have accepted := List.find?_eq_none.mp rejected pkg member
    unfold mismatch at accepted
    cases f : manifestFile? layout (physicalFileIndex layout) pkg.id.source with
    | none => simp [f] at accepted
    | some file =>
      cases d : ManifestMetadata.readDocument? file.text with
      | none => simp [f,d] at accepted
      | some doc =>
        have fields : aliasesMatch doc pkg = true ∧ geometryMatches doc.geometry pkg.geometryCompat = true := by
          simpa [f,d] using accepted
        exact ⟨file,doc,f,d,fields⟩

end VastitasKernel.ManifestBindings
