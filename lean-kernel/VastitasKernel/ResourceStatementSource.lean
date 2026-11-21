import VastitasKernel.ResourceLiteralText
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
    let found := match select first with
      | some (operation, span) => found.push ⟨owner, branches, index, operation, span⟩
      | none => found
    let found := match first with
      | .branch b yes no _ =>
        let found := collect select owner (⟨index, .literal b, true⟩ :: branches) 0 yes found
        collect select owner (⟨index, .literal b, false⟩ :: branches) 0 no found
      | .branchValue n yes no _ =>
        let found := collect select owner (⟨index, .binding n, true⟩ :: branches) 0 yes found
        collect select owner (⟨index, .binding n, false⟩ :: branches) 0 no found
      | _ => found
    collect select owner branches (index + 1) rest found

def itemsWithBoundaries {α : Type} (select : Statement → Option (α × Span))
    (boundaries : Function → List (Nat × α × Span)) (p : Program) : List (Item α) := Id.run do
  let mut found := #[]
  for pkg in p.packages do
    for m in pkg.modules do
      for fn in m.functions do
        let owner : ResourceOwner := ⟨pkg.id.source, m.pureModule.module.path, fn.name, fn.span.start, fn.isPublic⟩
        found := collect select owner [] 0 fn.body found
        for (index, op, span) in boundaries fn do
          found := found.push ⟨owner, [], index, op, span⟩
  return found.toList

def items {α : Type} (select : Statement → Option (α × Span)) (p : Program) : List (Item α) :=
  itemsWithBoundaries select (fun _ => []) p

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

def accessName : Storage.Access → String
  | .read => "read" | .write => "write" | .readWrite => "read_write"

def extent : RuntimeExtent → ExactLexeme
  | .literal n => .dimension n
  | .slot name => .ident name

def layoutFields (offset : Option Nat) (rows columns leading : ExactLexeme)
    (transposed : Bool) : List ExactLexeme :=
  [.ident (if offset.isSome then "layout" else "runtime_layout"), .punctuation '('] ++
  ((offset.toList.map ExactLexeme.dimension ++ [rows, columns, leading, .ident (toString transposed)]).intersperse
    (.punctuation ',')) ++ [.punctuation ')']

def pureTypeTokens : Indexed.Core.PureType → List ExactLexeme
  | .nat => [.ident "Nat"]
  | .int => [.ident "Int"]
  | .unit => [.ident "Unit"]
  | .bool => [.ident "Bool"]
  | .pair element =>
    [.ident "Pair", .punctuation '<', .ident (match element with | .nat => "Nat" | .int => "Int"), .punctuation '>']

def tokens (fields : List ExactLexeme) : Parser Unit := do
  for field in fields do
    match field with
    | .dimension n => consume fun f c => ResourceLiteralText.expectNat f c n
    | _ => token field

def peek : Parser Token := do
  let f ← read
  match f.next (← get) with
  | .ok t => return t
  | .error msg => throw (diagnostic {} msg)

def delimited {α : Type} (opening closing : Char) (xs : List α) (item : α → Parser Unit) :
    Parser Unit := do
  token (.punctuation opening)
  for (x, i) in xs.zipIdx do
    if i != 0 then token (.punctuation ',')
    item x
  token (.closeList closing (!xs.isEmpty))

def callFields (name : String) (arguments : List (List ExactLexeme)) : List ExactLexeme :=
  [.ident name, .punctuation '('] ++ (arguments.intersperse [.punctuation ',']).flatten ++ [.punctuation ')']

def nameFields (ns : List String) : List (List ExactLexeme) :=
  ns.map fun name => [.ident name]

def runTerminated (closing : Char) (p : Parser Unit) (f : File) (before : Cursor) (span : Span) :
    Except Diagnostic Token := do
  match (p f) before with
  | .error e _ => throw e
  | .ok () after =>
    let last ← (f.next after).mapError (diagnostic span)
    unless (match last.kind with | .symbol ch => ch == closing | _ => false) do
      throw (diagnostic last.span s!"expected '{closing}' at the end of the resource statement")
    return last

abbrev runStatement := runTerminated ';'

/-- The scope scan already traversed the body. Check that the parsed header
ends at exactly its opening brace and return its actual matching end token. -/
def runGroup (header : Parser Unit) (f : File) (site : ResourceStatementSite) : Except Diagnostic Token := do
  match (header f) site.before with
  | .error e _ => throw e
  | .ok () after =>
    let some (openingEnd, close) := site.group | throw (diagnostic site.span "expected a scoped resource declaration or branch")
    unless openingEnd == f.base + after.pos.byteIdx do
      throw (diagnostic site.span "resource header differs from its physical scope")
    return close

abbrev Sites := Std.HashMap Nat ResourceStatementSite

abbrev Replay (α : Type) := File → ResourceStatementSite → α → Span → Except Diagnostic Token

variable {α : Type}

def Corresponds (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) (i : Item α) : Prop :=
  ∃ site file last, sites[i.span.start]? = some site ∧ layout.files[site.fileIndex]? = some file ∧
    site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.span ∧
    replay ⟨file.text, file.offset⟩ site i.operation i.span = .ok last ∧ last.span.end = site.span.end

private def verify (replay : Replay α) (layout : PhysicalSources.Layout) (sites : Sites) (i : Item α) :
    Except Diagnostic (PLift (Corresponds replay layout sites i)) := do
  match hs : sites[i.span.start]? with
  | none => throw (diagnostic i.span "missing physical resource statement")
  | some site =>
    if pos : site.owner = i.owner ∧ site.branches = i.branches ∧ site.index = i.index ∧ site.span = i.span then
      match hf : layout.files[site.fileIndex]? with
      | none => throw (diagnostic site.span "missing resource statement file")
      | some file =>
        match h : replay ⟨file.text, file.offset⟩ site i.operation i.span with
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

theorem check_empty (replay : Replay α) (layout : PhysicalSources.Layout) :
    check replay layout {} [] = .ok () := by
  simp only [check, Std.HashMap.keys_empty, List.map_nil]
  rfl

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
