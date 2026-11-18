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

def layout (json : Json) : Except String Layout := do
  let source ← field json "root_source"
  let header ← AssemblySource.rootFile json
  let base := header.offset
  let entryText := header.text
  let filename ← str json "file"
  let root ← str json "root"
  let flat := root == flatPackageId.source
  let manifest := !flat && filename == root
  let fileLimit := 16 * 1024 * 1024
  let .ok raw := source.getObjVal? "files" | do
    unless base == 0 && !manifest do throw "missing physical inputs preceding the entry"
    return ⟨#[⟨← pathBytes (.str filename), 0, entryText⟩], 0⟩
  unless flat || manifest do throw "physical package file must name the root manifest"
  let rows ← raw.getArr?
  if rows.isEmpty || rows.size > 8192 then throw "invalid physical input count"
  let mut files := #[]
  let mut next := 0
  let mut byteCount := 0
  let mut entry := none
  let mut manifests : Std.TreeSet String := {}
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
  let mut missing := manifests
  for row in rows do
    fields row ["offset", "path", "text"]
    unless (← row.getObjValAs? Nat "offset") == next do throw "noncontiguous physical input offsets"
    let label ← field row "path"
    let path ← pathBytes label
    let name := label.getStr?.toOption
    if let some n := name then
      if manifests.contains n then
        if next == base then throw "a manifest cannot be the physical entry"
        unless missing.contains n do throw "duplicate physical package manifest"
        missing := missing.erase n
    if rows.size == 1 && label.getStr?.isOk then throw "redundant single-file source table"
    if manifest && files.isEmpty && (name != some root || next == base) then
      throw "the first physical input must be the root manifest"
    let text ← if next == base then do
      if (row.getObjVal? "text").isOk then throw "duplicate physical entry text"
      if flat && name.any (· != filename) then throw "flat entry path differs from file"
      pure entryText
    else str row "text"
    if next == base then entry := some files.size
    let size := text.utf8ByteSize
    byteCount := byteCount + size
    if size > fileLimit || byteCount > 64 * 1024 * 1024 then throw "physical source byte limit exceeded"
    files := files.push ⟨path, next, text⟩
    next := next + size + 1
  let some i := entry | throw "physical inputs do not contain the entry offset"
  unless missing.isEmpty do throw "physical inputs omit a package manifest"
  return ⟨files,i⟩

end VastitasKernel.PhysicalSources
