import VastitasKernel.AssemblySource

set_option autoImplicit false

/-! Exact physical inputs to a protocol-10 compilation. The frontend supplies
the files it read. The checker reconstructs their disjoint locations using UTF-8
byte lengths. A repeated file at a different logical position has its own span. -/
namespace VastitasKernel.PhysicalSources
open Lean JsonDecode Namespace

structure File where
  path : ByteArray
  offset : Nat
  text : String

structure Layout where
  files : Array File
  entry : Nat

private def pathBytes (j : Json) : Except String ByteArray := do
  match j with
  | .str s =>
    if s.isEmpty || s.toUTF8.data.contains 0 then throw "invalid physical input path"
    return s.toUTF8
  | .arr xs =>
    let mut path := ByteArray.empty
    for x in xs do
      let n ← x.getNat?
      unless 0 < n && n ≤ 255 do throw "invalid physical input path byte"
      path := path.push n.toUInt8
    if (String.fromUTF8? path).isSome then throw "use a string for a UTF-8 physical input path"
    return path
  | _ => throw "expected a physical input path"

/-- Check byte lengths before comparing labels. Common directory prefixes are
expensive to normalize in independent kernel replay. Only equal-length,
distinct paths need a lexicographic comparison. -/
def comparePath (a b : String) : Ordering :=
  match compare a.utf8ByteSize b.utf8ByteSize with
  | .eq => if a == b then .eq else compare a.toUTF8.data b.toUTF8.data
  | order => order

private theorem comparePath_lex :
    comparePath = compareLex (compareOn String.utf8ByteSize) (compareOn fun s : String => s.toUTF8.data) := by
  funext a b
  unfold comparePath compareLex compareOn
  cases compare a.utf8ByteSize b.utf8ByteSize <;> simp [Ordering.then]
  intro same
  simp [same]

instance : Std.TransCmp comparePath := by rw [comparePath_lex]; infer_instance

instance : Std.LawfulEqCmp comparePath where
  eq_of_compare h := by
    rw [comparePath_lex, compareLex_eq_eq] at h
    exact String.toByteArray_inj.mp (ByteArray.ext (Std.LawfulEqOrd.eq_of_compare h.2))

abbrev ManifestSet := Std.TreeSet String comparePath

/-- Information shared by all file rows of one request. -/
structure Table where
  filename : String
  root : String
  base : Nat
  entryText : String
  count : Nat
  manifests : ManifestSet

structure Cursor where
  files : Array File := #[]
  next : Nat := 0
  byteCount : Nat := 0
  entry : Option Nat := none
  missing : ManifestSet

/-- Validate the request header and the root module spans once. -/
def prepare (json : Json) : Except String (Layout ⊕ (Table × Array Json)) := do
  let source ← field json "root_source"
  let header ← AssemblySource.rootFile json
  let base := header.offset
  let entryText := header.text
  let filename ← str json "file"
  let root ← str json "root"
  let flat := root == flatPackageId.source
  let manifest := !flat
  if manifest && filename != root then throw "physical package file must name the root manifest"
  let .ok raw := source.getObjVal? "files" | do
    unless base == 0 && !manifest do throw "missing physical inputs preceding the entry"
    return .inl ⟨#[⟨← pathBytes (.str filename), 0, entryText⟩], 0⟩
  let rows ← raw.getArr?
  if rows.isEmpty || rows.size > 8192 then throw "invalid physical input count"
  let mut manifests : ManifestSet := {}
  if manifest then
    for package in ← array json "packages" do
      let owner ← str package "source"
      manifests := manifests.insert owner
      if owner == root then
        for m in ← array package "modules" do
          if (← array m "path").isEmpty then
            let s ← decodeSpan m
            unless base ≤ s.start && s.start ≤ s.end && s.end ≤ base + entryText.utf8ByteSize do
              throw "root module is outside the physical entry"
  return .inr (⟨filename, root, base, entryText, rows.size, manifests⟩, rows)

/-- Consume one physical file. The incoming cursor fixes its cumulative byte
offset and the package manifests still missing from the prefix. -/
def Table.step (t : Table) (s : Cursor) (row : Json) : Except String Cursor := do
  fields row ["offset", "path", "text"]
  unless (← row.getObjValAs? Nat "offset") == s.next do throw "noncontiguous physical input offsets"
  let label ← field row "path"
  let path ← pathBytes label
  let name := label.getStr?.toOption
  let mut missing := s.missing
  if let some n := name then
    if t.manifests.contains n then
      if s.next == t.base then throw "a manifest cannot be the physical entry"
      unless missing.contains n do throw "duplicate physical package manifest"
      missing := missing.erase n
  if t.count == 1 && label.getStr?.isOk then throw "redundant single-file source table"
  let flat := t.root == flatPackageId.source
  if !flat && s.files.isEmpty && (name != some t.root || s.next == t.base) then
    throw "the first physical input must be the root manifest"
  let text ← if s.next == t.base then do
    if (row.getObjVal? "text").isOk then throw "duplicate physical entry text"
    if flat && name.any (· != t.filename) then throw "flat entry path differs from file"
    pure t.entryText
  else str row "text"
  let size := text.utf8ByteSize
  let total := s.byteCount + size
  if size > 16 * 1024 * 1024 || total > 64 * 1024 * 1024 then throw "physical source byte limit exceeded"
  let entry := if s.next == t.base then some s.files.size else s.entry
  return ⟨s.files.push ⟨path, s.next, text⟩, s.next + size + 1, total, entry, missing⟩

def Cursor.finish (s : Cursor) : Except String Layout := do
  let some i := s.entry | throw "physical inputs do not contain the entry offset"
  unless s.missing.isEmpty do throw "physical inputs omit a package manifest"
  return ⟨s.files,i⟩

def layout (json : Json) : Except String Layout := do
  match ← prepare json with
  | .inl single => return single
  | .inr (table, rows) =>
    let result ← rows.foldlM table.step {missing := table.manifests}
    result.finish

end VastitasKernel.PhysicalSources
