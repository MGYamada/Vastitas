import VastitasKernel.ResourceProtocol

set_option autoImplicit false

namespace VastitasOracle.CertificatePackages
open VastitasKernel ResourceSource

/-- The package owners and ordered dependency edges that qualify function IDs. -/
structure Graph where
  file : String
  root : String
  legacyGeometry : Bool
  packages : List (Namespace.PackageId × List (String × String))

def edges (ds : List Namespace.Dependency) := ds.map fun d => (d.alias,d.target)

def ofProgram (p : Program) : Graph :=
  ⟨p.file,p.root,p.legacyGeometry,p.packages.map fun pkg => (pkg.id,edges pkg.dependencies)⟩

section
open Lean PhysicalSources Namespace JsonDecode

/-- Protocol-10 representation of a non-entry flat library with a UTF-8 path. -/
def flatLibraryRow (offset : Nat) (path text : String) : Json :=
  Json.mkObj [("offset",toJson (Int.ofNat offset)),("path",.str path),("text",.str text)]

/-- Decode the fixed JSON fields once for every such library. Each application
checks its own path bytes, offsets and cumulative size at the actual cursor. -/
theorem flatLibraryStep (filename entryText path text : String) (count base offset used size : Nat)
    (files : Array File) (entry : Option Nat)
    (extent : text.utf8ByteSize = size)
    (notEntry : (offset == base) = false) (many : (count == 1) = false)
    (validPath : (path.isEmpty || path.toUTF8.data.contains 0) = false)
    (fits : (decide (size > 16 * 1024 * 1024) || decide (used + size > 64 * 1024 * 1024)) = false) :
    (Table.mk filename flatPackageId.source base entryText count {}).step
        ⟨files, offset, used, entry, {}⟩ (flatLibraryRow offset path text) =
    .ok ⟨files.push ⟨path.toUTF8, offset, text⟩, offset + size + 1, used + size, entry, {}⟩ := by
  subst size
  have keys : fields (flatLibraryRow offset path text) ["offset", "path", "text"] = .ok () := by rfl
  have off : (flatLibraryRow offset path text).getObjValAs? Nat "offset" = .ok offset := by rfl
  have label : field (flatLibraryRow offset path text) "path" = .ok (.str path) := by rfl
  have body : str (flatLibraryRow offset path text) "text" = .ok text := by rfl
  simp [Table.step, keys, off, label, body, pathBytes_string validPath, Json.getStr?, Except.toOption,
    notEntry, many, fits, bind, Except.bind, pure, Except.pure]

end

/-- Compose independently checked file rows in their original order. -/
theorem prepend_row {t : PhysicalSources.Table} {s next last : PhysicalSources.Cursor}
    {row : Lean.Json} {tail : List Lean.Json} (first : t.step s row = .ok next)
    (rest : tail.foldlM t.step next = .ok last) :
    (row :: tail).foldlM t.step s = .ok last := by
  simp [List.foldlM_cons, first, bind, Except.bind, rest]

theorem table_layout {wire : Lean.Json} {t : PhysicalSources.Table} {rows : Array Lean.Json}
    {last : PhysicalSources.Cursor} {result : PhysicalSources.Layout}
    (prepared : PhysicalSources.prepare wire = .ok (.inr (t,rows)))
    (scanned : rows.toList.foldlM t.step {missing := t.manifests} = .ok last)
    (complete : last.finish = .ok result) : PhysicalSources.layout wire = .ok result := by
  simp only [PhysicalSources.layout, prepared, bind, Except.bind, ← Array.foldlM_toList,
    scanned, complete]

private def readPackage (j : Lean.Json) : Except String (Namespace.PackageId × List (String × String)) := do
  let m ← Indexed.Wire.packageMetadata j
  return (m.id,edges m.dependencies)

/-- Use the same protocol, edition, geometry and package field decoders as the
public compiler. Reading this projection requires no function body reduction. -/
def read (wire : Lean.Json) : Except String Graph := do
  let h ← Wire.requestFields wire
  let packages ← h.packages.mapM readPackage
  return ⟨h.file,h.root,h.legacyGeometry,packages⟩

private theorem metadata_of_package {j : Lean.Json} {pkg : Package} (h : Wire.package j = .ok pkg) :
    readPackage j =
      (.ok (pkg.id,edges pkg.dependencies) : Except String _) := by
  unfold readPackage
  unfold Wire.package at h
  cases a : JsonDecode.array j "modules" <;> simp [a, bind, Except.bind] at h
  rename_i raw
  cases b : raw.mapM Wire.module <;> simp [b] at h
  cases c : Indexed.Wire.packageMetadata j <;> simp [c, bind, Except.bind, pure, Except.pure] at h ⊢
  cases h
  exact ⟨rfl,rfl⟩

private theorem metadata_of_packages {rows : List Lean.Json} {pkgs : List Package}
    (h : rows.mapM Wire.package = .ok pkgs) :
    rows.mapM readPackage =
      (.ok (pkgs.map fun pkg => (pkg.id,edges pkg.dependencies)) : Except String _) := by
  induction rows generalizing pkgs with
  | nil => cases h; rfl
  | cons j tail ih =>
    rw [List.mapM_cons] at h ⊢
    cases hp : Wire.package j <;> simp [hp, bind, Except.bind] at h
    cases ht : tail.mapM Wire.package <;> simp [ht, pure, Except.pure] at h
    cases h
    rw [metadata_of_package hp, ih ht]
    rfl

private theorem graph_of_fields {wire : Lean.Json} {p : Program} (h : Wire.decodeFields wire = .ok p) :
    read wire = .ok (ofProgram p) := by
  unfold Wire.decodeFields at h
  unfold read
  cases header : Wire.requestFields wire <;> simp [header, bind, Except.bind] at h ⊢
  rename_i fields
  cases hp : fields.packages.mapM Wire.package <;> simp [hp, pure, Except.pure] at h
  cases h
  rw [metadata_of_packages hp]
  rfl

/-- Every accepted wire has exactly the file, root, profile, package IDs and
ordered dependency targets read by the independently replayed stage proof. -/
theorem of_decoded {wire : Lean.Json} {p : Program} (h : Wire.program wire = .ok p) :
    read wire = .ok (ofProgram p) := by
  unfold Wire.program at h
  cases hf : Wire.decodeFields wire <;> simp [hf, bind, Except.bind] at h
  rename_i raw
  cases hr : Wire.reservedIdentities raw.root raw.packages <;> simp [hr] at h
  cases hn : Wire.operatorNames raw <;> simp [hn] at h
  rename_i names
  cases hs : Wire.exactSources wire {raw with operatorValues := names} <;>
    simp [hs, pure, Except.pure] at h
  cases h
  exact graph_of_fields (p := raw) hf

end VastitasOracle.CertificatePackages
