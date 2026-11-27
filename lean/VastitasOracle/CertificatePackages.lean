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

private theorem sizedRootFile (wire source : Json) (root text : String) (base size : Nat)
    (src : field wire "root_source" = .ok source)
    (keys : fields source ["offset", "text", "files"] = .ok ())
    (off : source.getObjValAs? Nat "offset" = .ok base) (body : str source "text" = .ok text)
    (owner : str wire "root" = .ok root)
    (protectedOffset : ((root == flatPackageId.source) && (base != 0)) = false)
    (extent : text.utf8ByteSize = size) (bound : size ≤ 16 * 1024 * 1024)
    (total : base + size ≤ 64 * 1024 * 1024 + 8191) :
    AssemblySource.rootFile wire = .ok ⟨base, text⟩ := by
  simp [AssemblySource.rootFile, src, owner, keys, off, body, protectedOffset, extent,
    Nat.not_lt_of_ge bound, Nat.not_lt_of_ge total, bind, Except.bind, pure, Except.pure]

def flatSingleSource (text : String) : Json :=
  Json.mkObj [("offset", toJson (0 : Int)), ("text", .str text)]

/-- Check the complete single-file layout using a separately proved UTF-8 extent. -/
theorem flatSingleLayout (wire : Json) (filename text : String) (size : Nat)
    (source : field wire "root_source" = .ok (flatSingleSource text))
    (file : str wire "file" = .ok filename)
    (root : str wire "root" = .ok flatPackageId.source)
    (valid : (filename.isEmpty || filename.toUTF8.data.contains 0) = false)
    (extent : text.utf8ByteSize = size) (bound : size ≤ 16 * 1024 * 1024) :
    PhysicalSources.layout wire = .ok ⟨#[⟨filename.toUTF8, 0, text⟩], 0⟩ := by
  have entry := sizedRootFile wire _ flatPackageId.source text 0 size source
    (by rfl) (by rfl) (by rfl) root (by decide) extent bound (by omega)
  have missing : ((flatSingleSource text).getObjVal? "files").isOk = false := by rfl
  cases raw : (flatSingleSource text).getObjVal? "files" with
  | error why =>
    simp [PhysicalSources.layout, PhysicalSources.prepare, source, entry, file, root,
      raw, pathBytes_string valid, bind, Except.bind, pure, Except.pure]
  | ok _ =>
    rw [raw] at missing
    contradiction

def tableSource (base : Nat) (text : String) (rows : Array Json) : Json :=
  Json.mkObj [("files", .arr rows), ("offset", toJson (Int.ofNat base)), ("text", .str text)]

def flatTableSource (text : String) (rows : Array Json) : Json := tableSource 0 text rows

/-- Decode the header of a flat table without reducing the entire entry text. -/
theorem flatTableHeader (wire : Json) (filename text : String) (rows : Array Json) (count size : Nat)
    (source : field wire "root_source" = .ok (flatTableSource text rows))
    (file : str wire "file" = .ok filename) (root : str wire "root" = .ok flatPackageId.source)
    (extent : text.utf8ByteSize = size) (bound : size ≤ 16 * 1024 * 1024)
    (len : rows.size = count) (positive : 0 < count) (limit : count ≤ 8192) :
    PhysicalSources.prepare wire =
      .ok (.inr (⟨filename, flatPackageId.source, 0, text, count, {}⟩, rows)) := by
  have entry := sizedRootFile wire _ flatPackageId.source text 0 size source
    (by rfl) (by rfl) (by rfl) root (by decide) extent bound (by omega)
  have files : (flatTableSource text rows).getObjVal? "files" = .ok (.arr rows) := by rfl
  have nonempty : rows ≠ #[] := by
    intro h
    simp [h] at len
    omega
  simp [PhysicalSources.prepare, source, entry, file, root, files, Json.getArr?, nonempty, limit, len,
    bind, Except.bind, pure, Except.pure]

def entryRow (base : Nat) (path : String) : Json :=
  Json.mkObj [("offset", toJson (Int.ofNat base)), ("path", .str path)]

def flatEntryRow (path : String) : Json := entryRow 0 path

/-- Consume the first row of a flat table at the protected entry offset. -/
theorem flatEntryStep (filename text : String) (count size : Nat)
    (extent : text.utf8ByteSize = size) (many : (count == 1) = false)
    (validPath : (filename.isEmpty || filename.toUTF8.data.contains 0) = false)
    (bound : size ≤ 16 * 1024 * 1024) :
    (Table.mk filename flatPackageId.source 0 text count {}).step {missing := {}} (flatEntryRow filename) =
      .ok ⟨#[⟨filename.toUTF8, 0, text⟩], size + 1, size, some 0, {}⟩ := by
  have keys : fields (flatEntryRow filename) ["offset", "path", "text"] = .ok () := by rfl
  have off : (flatEntryRow filename).getObjValAs? Nat "offset" = .ok 0 := by rfl
  have label : field (flatEntryRow filename) "path" = .ok (.str filename) := by rfl
  have missing : ((flatEntryRow filename).getObjVal? "text").isOk = false := by rfl
  have aggregate : size ≤ 64 * 1024 * 1024 := by omega
  simp [Table.step, keys, off, label, pathBytes_string validPath, missing, many, extent,
    Nat.not_lt_of_ge bound, Nat.not_lt_of_ge aggregate, Json.getStr?, Except.toOption,
    bind, Except.bind, pure, Except.pure]

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

/-- Canonical non-entry row for either protocol path encoding. -/
def fileRow (offset : Nat) (label : Json) (text : String) : Json :=
  Json.mkObj [("offset", toJson (Int.ofNat offset)), ("path", label), ("text", .str text)]

/-- Check the path, offset and manifest transition on the same row with empty contents.
The proved extent and bounds then restore the full text at the same cursor. -/
theorem nonEntryFileStep (t : Table) (s : Cursor) (label : Json) (path : ByteArray) (wireText text : String)
    (missing : ManifestSet) (size : Nat)
    (sameText : wireText = text)
    (other : (s.next == t.base) = false) (extent : text.utf8ByteSize = size)
    (fits : (decide (size > 16 * 1024 * 1024) || decide (s.byteCount + size > 64 * 1024 * 1024)) = false)
    (empty : t.step s (fileRow s.next label "") =
      .ok ⟨s.files.push ⟨path, s.next, ""⟩, s.next + 1, s.byteCount, s.entry, missing⟩) :
    t.step s (fileRow s.next label wireText) =
      .ok ⟨s.files.push ⟨path, s.next, text⟩, s.next + size + 1, s.byteCount + size, s.entry, missing⟩ := by
  subst wireText
  have keys (a : String) : fields (fileRow s.next label a) ["offset","path","text"] = .ok () := by rfl
  have off (a : String) : (fileRow s.next label a).getObjValAs? Nat "offset" = .ok s.next := by rfl
  have lab (a : String) : field (fileRow s.next label a) "path" = .ok label := by rfl
  have body (a : String) : str (fileRow s.next label a) "text" = .ok a := by rfl
  have usedFits : ¬67108864 < s.byteCount := by
    simp at fits
    omega
  simp [Table.step, keys, off, lab, body, other, extent, fits, usedFits, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at empty ⊢
  repeat' (split at empty <;> simp_all [Array.push_eq_push])
  all_goals grind

/-- Decode the packaged entry after its root manifest using its checked byte extent. -/
theorem packageEntryStep (root path text : String) (count base used size : Nat)
    (files : Array File) (previous : Option Nat) (owners missing : ManifestSet)
    (extent : text.utf8ByteSize = size)
    (pkg : (root == flatPackageId.source) = false)
    (ordinary : owners.contains path = false)
    (many : (count == 1) = false) (afterRoot : files.isEmpty = false)
    (validPath : (path.isEmpty || path.toUTF8.data.contains 0) = false)
    (fits : (decide (size > 16 * 1024 * 1024) || decide (used + size > 64 * 1024 * 1024)) = false) :
    (Table.mk root root base text count owners).step
      ⟨files, base, used, previous, missing⟩ (entryRow base path) =
    .ok ⟨files.push ⟨path.toUTF8, base, text⟩, base + size + 1, used + size, some files.size, missing⟩ := by
  have keys : fields (entryRow base path) ["offset", "path", "text"] = .ok () := by rfl
  have off : (entryRow base path).getObjValAs? Nat "offset" = .ok base := by rfl
  have label : field (entryRow base path) "path" = .ok (.str path) := by rfl
  have miss : ((entryRow base path).getObjVal? "text").isOk = false := by rfl
  simp [Table.step, keys, off, label, pathBytes_string validPath, miss, ordinary, many,
    afterRoot, pkg, extent, fits, Json.getStr?, Except.toOption, bind, Except.bind, pure, Except.pure]

/-- Keep the package graph and span checks bound to the exact length of this entry. -/
theorem packageTableHeader (wire : Json) (root text : String) (base size : Nat) (rows : Array Json)
    (manifests : ManifestSet)
    (src : field wire "root_source" = .ok (tableSource base text rows))
    (file : str wire "file" = .ok root)
    (owner : str wire "root" = .ok root) (pkg : (root == flatPackageId.source) = false)
    (extent : text.utf8ByteSize = size) (bound : size ≤ 16 * 1024 * 1024)
    (total : base + size ≤ 64 * 1024 * 1024 + 8191)
    (count : rows.isEmpty = false) (limit : rows.size ≤ 8192)
    (scanned : readManifests wire root base size = .ok manifests) :
    PhysicalSources.prepare wire = .ok (.inr (⟨root, root, base, text, rows.size, manifests⟩, rows)) := by
  have header := sizedRootFile wire (tableSource base text rows) root text base size src
    (by rfl) (by rfl) (by rfl) owner (by simp [pkg]) extent bound total
  have fr : (tableSource base text rows).getObjVal? "files" = .ok (.arr rows) := by rfl
  simp [PhysicalSources.prepare, src, header, file, owner, pkg, fr, Json.getArr?, count,
    Nat.not_lt_of_ge limit, extent, scanned, bind, Except.bind, pure, Except.pure]

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

/-- Declaration decoding uses only the fields returned by the protocol header decoder. -/
theorem candidate_of_header {a b : Lean.Json} (same : Wire.requestFields a = Wire.requestFields b) :
    Wire.sourceCandidate a = Wire.sourceCandidate b := by
  unfold Wire.sourceCandidate Wire.decodeFields
  rw [same]

/-- Compose a decoded row with its ordered tail without evaluating the row again. -/
theorem map_row {α β : Type} {readRow : α → Except String β} {row : α} {rows : List α}
    {value : β} {values : List β} (first : readRow row = .ok value)
    (rest : rows.mapM readRow = .ok values) :
    (row :: rows).mapM readRow = .ok (value :: values) := by
  simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure]

/-- Every decoded package occurs in the same position in the program as in the wire. -/
theorem fields_of_packages {j : Lean.Json} {file root : String} {legacy : Bool}
    {rows : List Lean.Json} {packages : List Package}
    (header : Wire.requestFields j = .ok ⟨file, root, legacy, rows⟩)
    (decoded : rows.mapM Wire.package = .ok packages) :
    Wire.decodeFields j = .ok {file, root, legacyGeometry := legacy, packages} := by
  simp [Wire.decodeFields, header, decoded, bind, Except.bind, pure, Except.pure]

/-- Compose identity and operator checks on the exact program recovered by the decoder. -/
theorem candidate_of_stages {j : Lean.Json} {raw : Program} (fields : Wire.decodeFields j = .ok raw)
    (ids : (Wire.reservedIdentities raw.root raw.packages).isOk = true)
    (operators : (Wire.operatorNames raw).isOk = true) :
    (Wire.sourceCandidate j).isOk = true := by
  cases hi : Wire.reservedIdentities raw.root raw.packages with
  | error e => simp [hi, Except.isOk, Except.toBool] at ids
  | ok _ =>
    cases hn : Wire.operatorNames raw with
    | error e => simp [hn, Except.isOk, Except.toBool] at operators
    | ok names => simp [Wire.sourceCandidate, fields, hi, hn, bind, Except.bind, pure, Except.pure,
        Except.isOk, Except.toBool]

private theorem graph_of_candidate {wire : Lean.Json} {p : Program} (h : Wire.sourceCandidate wire = .ok p) :
    read wire = .ok (ofProgram p) := by
  unfold Wire.sourceCandidate at h
  cases hf : Wire.decodeFields wire <;> simp [hf, bind, Except.bind] at h
  rename_i raw
  cases hr : Wire.reservedIdentities raw.root raw.packages <;> simp [hr] at h
  cases hn : Wire.operatorNames raw <;> simp [hn, pure, Except.pure] at h
  cases h
  exact graph_of_fields (p := raw) hf

/-- The recovered candidate has the independently supplied owner graph. The public decoder
returns that very candidate exactly when its physical source checks also succeed. -/
theorem replayed_candidate {wire : Lean.Json} {owners : Graph}
    (decoded : (Wire.sourceCandidate wire).isOk = true) (metadata : read wire = .ok owners) :
    ∃ p, Wire.sourceCandidate wire = .ok p ∧ ofProgram p = owners ∧
      (Wire.program wire = .ok p ↔ Wire.exactSources wire p = .ok ()) := by
  cases c : Wire.sourceCandidate wire with
  | error e => simp [c, Except.isOk, Except.toBool] at decoded
  | ok p =>
    refine ⟨p, rfl, Except.ok.inj ((graph_of_candidate c).symm.trans metadata), ?_⟩
    cases src : Wire.exactSources wire p <;> simp [Wire.program, c, src, bind, Except.bind, pure, Except.pure]

/-- Every accepted wire has exactly the file, root, profile, package IDs and
ordered dependency targets read by the independently replayed stage proof. -/
theorem of_decoded {wire : Lean.Json} {p : Program} (h : Wire.program wire = .ok p) :
    read wire = .ok (ofProgram p) := by
  cases c : Wire.sourceCandidate wire with
  | error e => simp [Wire.program, c, bind, Except.bind] at h
  | ok candidate =>
    cases src : Wire.exactSources wire candidate <;>
      simp [Wire.program, c, src, bind, Except.bind, pure, Except.pure] at h
    exact h ▸ graph_of_candidate c

end VastitasOracle.CertificatePackages
