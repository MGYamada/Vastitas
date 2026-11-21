import VastitasKernel.ExactModelSource
import VastitasKernel.ResourceLiteralText

set_option autoImplicit false

/-! Match every static or runtime literal cell operation after storage checking,
including statements in uncalled functions and both arms of resource branches. -/
namespace VastitasKernel.ResourceCellSource
open AssemblyText ResourceSource SourceText

structure Cell where
  operation : String
  loan : String
  coordinates : Option (Nat × Nat)
  literal : Storage.Literal
  span : Span

private def cell? : Statement → Option Cell
  | .action (.fill loan v) s => some ⟨"fill", loan, none, v, s⟩
  | .action (.store loan r c v) s => some ⟨"store", loan, some (r,c), v, s⟩
  | .action (.expect loan r c v) s => some ⟨"expect", loan, some (r,c), v, s⟩
  | .runtime (.fill loan v) s => some ⟨"runtime_fill", loan, none, v, s⟩
  | .runtime (.expect loan r c v) s => some ⟨"runtime_expect", loan, some (r,c), v, s⟩
  | _ => none

structure Item where
  owner : ResourceOwner
  branches : List ResourceBranch
  index : Nat
  cell : Cell

private def collect (owner : ResourceOwner) (branches : List ResourceBranch) (index : Nat) :
    List Statement → Array Item → Array Item
  | [], found => found
  | first :: rest, found =>
    let found := match first with
      | .branch b yes no _ =>
        let found := collect owner (⟨index, .literal b, true⟩ :: branches) 0 yes found
        collect owner (⟨index, .literal b, false⟩ :: branches) 0 no found
      | .branchValue n yes no _ =>
        let found := collect owner (⟨index, .binding n, true⟩ :: branches) 0 yes found
        collect owner (⟨index, .binding n, false⟩ :: branches) 0 no found
      | stmt => match cell? stmt with
        | some cell => found.push ⟨owner, branches, index, cell⟩
        | none => found
    collect owner branches (index + 1) rest found

def items (p : Program) : List Item := Id.run do
  let mut found := #[]
  for pkg in p.packages do
    for m in pkg.modules do
      for fn in m.functions do
        found := collect ⟨pkg.id.source, m.pureModule.module.path, fn.name, fn.span.start, fn.isPublic⟩ [] 0 fn.body found
  return found.toList

private def diagnostic (span : Span) (message : String) : Diagnostic :=
  {code := "E_RESOURCE_SOURCE", span, message}

private abbrev Parser := ReaderT File (EStateM Diagnostic Cursor)

private def consume (readField : File → Cursor → Except String Cursor) : Parser Unit := do
  let f ← read
  let c ← get
  match readField f c with
  | .ok after => set after
  | .error msg => throw (diagnostic (((f.next c).toOption.map (·.span)).getD {}) msg)

private def token (t : ExactLexeme) : Parser Unit := consume fun f c => expectExact f c t

def replay (f : File) (before : Cursor) (cell : Cell) : Except Diagnostic Token := do
  let parser : Parser Unit := do
    token (.ident cell.operation)
    token (.punctuation '(')
    token (.ident cell.loan)
    token (.punctuation ',')
    if let some (r,c) := cell.coordinates then
      consume fun f p => ResourceLiteralText.expectNat f p r
      token (.punctuation ',')
      consume fun f p => ResourceLiteralText.expectNat f p c
      token (.punctuation ',')
    consume fun f p => ResourceLiteralText.check f p cell.literal
    token (.punctuation ')')
  match (parser f) before with
  | .error e _ => throw e
  | .ok () after =>
    let semi ← (f.next after).mapError (diagnostic cell.span)
    unless semi.kind matches .symbol ';' do throw (diagnostic semi.span "expected the end of the cell statement")
    return semi

abbrev Sites := Std.HashMap Nat CellSite

def Corresponds (layout : PhysicalSources.Layout) (sites : Sites) (i : Item) : Prop :=
  ∃ site file last, sites[i.cell.span.start]? = some site ∧ layout.files[site.fileIndex]? = some file ∧
    site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.cell.span ∧
    replay ⟨file.text, file.offset⟩ site.before i.cell = .ok last ∧ last.span.end = site.span.end

private def verify (layout : PhysicalSources.Layout) (sites : Sites) (i : Item) :
    Except Diagnostic (PLift (Corresponds layout sites i)) := do
  match hs : sites[i.cell.span.start]? with
  | none => throw (diagnostic i.cell.span "missing physical resource cell statement")
  | some site =>
    if pos : site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.cell.span then
      match hf : layout.files[site.fileIndex]? with
      | none => throw (diagnostic site.span "missing resource cell file")
      | some file =>
        match h : replay ⟨file.text, file.offset⟩ site.before i.cell with
        | .error e => throw e
        | .ok last =>
          if extent : last.span.end = site.span.end then
            return ⟨⟨site,file,last,hs,hf,pos.1,pos.2.1,pos.2.2.1,pos.2.2.2,h,extent⟩⟩
          else throw (diagnostic last.span "cell statement does not consume its physical extent")
    else throw (diagnostic site.span "resource cell belongs to a different function, branch or statement position")

private def checkAll (layout : PhysicalSources.Layout) (sites : Sites) : List Item → Except Diagnostic Unit
  | [] => .ok ()
  | i :: rest => do
    let _ ← verify layout sites i
    checkAll layout sites rest

private def inventoryError (sites : Sites) (cells : List Item) : Diagnostic := Id.run do
  let mut seen : Std.HashSet Nat := {}
  for i in cells do
    let start := i.cell.span.start
    if seen.contains start then return diagnostic i.cell.span "duplicate resource cell statement in request"
    unless sites.contains start do return diagnostic i.cell.span "resource cell statement has no physical site"
    seen := seen.insert start
  if let some (_, site) := sites.toList.find? (fun (start, _) => !seen.contains start) then
    return diagnostic site.span "physical resource cell statement omitted from request"
  return diagnostic {} "resource cell statement inventory differs from physical source"

def check (layout : PhysicalSources.Layout) (sites : Sites) (cells : List Item) : Except Diagnostic Unit :=
  if Finite.sameCounts sites.keys (cells.map (·.cell.span.start)) then checkAll layout sites cells
  else .error (inventoryError sites cells)

theorem check_sound {layout : PhysicalSources.Layout} {sites : Sites} {cells : List Item}
    (h : check layout sites cells = .ok ()) :
    Finite.sameCounts sites.keys (cells.map (·.cell.span.start)) = true ∧
    ∀ i ∈ cells, Corresponds layout sites i := by
  cases counts : Finite.sameCounts sites.keys (cells.map (·.cell.span.start)) <;>
    simp [check, counts] at h
  refine ⟨rfl, ?_⟩
  clear counts
  induction cells with
  | nil => simp
  | cons i rest ih =>
    cases v : verify layout sites i with
    | error e => simp [checkAll, v, bind, Except.bind] at h
    | ok evidence =>
      simp [checkAll, v, bind, Except.bind] at h
      exact List.forall_mem_cons.mpr ⟨evidence.down, ih h⟩

end VastitasKernel.ResourceCellSource
