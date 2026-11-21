import VastitasKernel.ExactModelSource

set_option autoImplicit false

/-! Inventory and replay of resource statements at their lexical owners and branch positions. -/
namespace VastitasKernel.ResourceStatementSource
open AssemblyText ResourceSource SourceText

structure Item (α : Type) where
  owner : ResourceOwner
  branches : List ResourceBranch
  index : Nat
  operation : α
  span : Span

private def collect {α : Type} (select : Statement → Option (α × Span)) (owner : ResourceOwner) (branches : List ResourceBranch) (index : Nat) :
    List Statement → Array (Item α) → Array (Item α)
  | [], found => found
  | first :: rest, found =>
    let found := match first with
      | .branch b yes no _ =>
        let found := collect select owner (⟨index, .literal b, true⟩ :: branches) 0 yes found
        collect select owner (⟨index, .literal b, false⟩ :: branches) 0 no found
      | .branchValue n yes no _ =>
        let found := collect select owner (⟨index, .binding n, true⟩ :: branches) 0 yes found
        collect select owner (⟨index, .binding n, false⟩ :: branches) 0 no found
      | stmt => match select stmt with
        | some (operation, span) => found.push ⟨owner, branches, index, operation, span⟩
        | none => found
    collect select owner branches (index + 1) rest found

def items {α : Type} (select : Statement → Option (α × Span)) (p : Program) : List (Item α) := Id.run do
  let mut found := #[]
  for pkg in p.packages do
    for m in pkg.modules do
      for fn in m.functions do
        found := collect select ⟨pkg.id.source, m.pureModule.module.path, fn.name, fn.span.start, fn.isPublic⟩ [] 0 fn.body found
  return found.toList

def diagnostic (span : Span) (message : String) : Diagnostic :=
  {code := "E_RESOURCE_SOURCE", span, message}

abbrev Parser := ReaderT File (EStateM Diagnostic Cursor)

def consume (readField : File → Cursor → Except String Cursor) : Parser Unit := do
  let f ← read
  let c ← get
  match readField f c with
  | .ok after => set after
  | .error msg => throw (diagnostic (((f.next c).toOption.map (·.span)).getD {}) msg)

def token (t : ExactLexeme) : Parser Unit := consume fun f c => expectExact f c t

def runStatement (p : Parser Unit) (f : File) (before : Cursor) (span : Span) : Except Diagnostic Token := do
  match (p f) before with
  | .error e _ => throw e
  | .ok () after =>
    let semi ← (f.next after).mapError (diagnostic span)
    unless semi.kind matches .symbol ';' do throw (diagnostic semi.span "expected the end of the resource statement")
    return semi

abbrev Sites := Std.HashMap Nat ResourceStatementSite

abbrev Replay (α : Type) := File → Cursor → α → Span → Except Diagnostic Token

variable {α : Type}

def Corresponds (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) (i : Item α) : Prop :=
  ∃ site file last, sites[i.span.start]? = some site ∧ layout.files[site.fileIndex]? = some file ∧
    site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.span ∧
    replay ⟨file.text, file.offset⟩ site.before i.operation i.span = .ok last ∧ last.span.end = site.span.end

private def verify (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) (i : Item α) :
    Except Diagnostic (PLift (Corresponds replay layout sites i)) := do
  match hs : sites[i.span.start]? with
  | none => throw (diagnostic i.span "missing physical resource statement")
  | some site =>
    if pos : site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.span then
      match hf : layout.files[site.fileIndex]? with
      | none => throw (diagnostic site.span "missing resource statement file")
      | some file =>
        match h : replay ⟨file.text, file.offset⟩ site.before i.operation i.span with
        | .error e => throw e
        | .ok last =>
          if extent : last.span.end = site.span.end then
            return ⟨⟨site,file,last,hs,hf,pos.1,pos.2.1,pos.2.2.1,pos.2.2.2,h,extent⟩⟩
          else throw (diagnostic last.span "resource statement does not consume its physical extent")
    else throw (diagnostic site.span "resource statement belongs to a different function, branch or statement position")

private def checkAll (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) : List (Item α) → Except Diagnostic Unit
  | [] => .ok ()
  | i :: rest => do
    let _ ← verify replay layout sites i
    checkAll replay layout sites rest

private def inventoryError (sites : Sites) (operations : List (Item α)) : Diagnostic := Id.run do
  let mut seen : Std.HashSet Nat := {}
  for i in operations do
    let start := i.span.start
    if seen.contains start then return diagnostic i.span "duplicate resource statement in request"
    unless sites.contains start do return diagnostic i.span "resource statement has no physical site"
    seen := seen.insert start
  if let some (_, site) := sites.toList.find? (fun (start, _) => !seen.contains start) then
    return diagnostic site.span "physical resource statement omitted from request"
  return diagnostic {} "resource statement inventory differs from physical source"

def check (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) (operations : List (Item α)) : Except Diagnostic Unit :=
  if Finite.sameCounts sites.keys (operations.map (·.span.start)) then checkAll replay layout sites operations
  else .error (inventoryError sites operations)

theorem check_sound {replay : Replay α} {layout : PhysicalSources.Layout} {sites : Sites} {operations : List (Item α)}
    (h : check replay layout sites operations = .ok ()) :
    Finite.sameCounts sites.keys (operations.map (·.span.start)) = true ∧
    ∀ i ∈ operations, Corresponds replay layout sites i := by
  cases counts : Finite.sameCounts sites.keys (operations.map (·.span.start)) <;>
    simp [check, counts] at h
  refine ⟨rfl, ?_⟩
  clear counts
  induction operations with
  | nil => simp
  | cons i rest ih =>
    cases v : verify replay layout sites i with
    | error e => simp [checkAll, v, bind, Except.bind] at h
    | ok evidence =>
      simp [checkAll, v, bind, Except.bind] at h
      exact List.forall_mem_cons.mpr ⟨evidence.down, ih h⟩

end VastitasKernel.ResourceStatementSource
