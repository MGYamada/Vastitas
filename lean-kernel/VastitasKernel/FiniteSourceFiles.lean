import VastitasKernel.ExactModelSource
import VastitasKernel.MethodBodyText

set_option autoImplicit false

/-! Replay the written module and import declarations, finite tables and named
functions after independent namespace and Core checking. Match each lexical
owner, visibility and node span in the original file. -/
namespace VastitasKernel.FiniteSourceFiles
open Indexed AssemblyText SourceText

structure Form where
  header : List ExactLexeme
  rows : List (Span × List ExactLexeme)
  closing : Char

private def ref (p : Source.Path) := ExactLexeme.reference p.path p.span
private def tag (t : Source.FiniteTag) := ExactLexeme.reference [t.name] t.span

private def tuple (items : List ExactLexeme) : List ExactLexeme :=
  .punctuation '(' :: listLexemes (items.map ([·])) ')'

private def application (name : String) (args : List Source.Path) : List ExactLexeme :=
  [.ident name, .punctuation '('] ++ (args.map ref).intersperse (.punctuation ',') ++ [.punctuation ')']

private def table (name : String) (inputs : List Source.Path) (output : Source.Path)
    (domain : List ExactLexeme) (rows : List Source.FiniteRow) : Form :=
  ⟨[.ident "table", .ident name] ++ tuple (inputs.map ref) ++ [.arrow, ref output] ++ domain ++ [.punctuation '{'],
   rows.map (fun r => (r.span, tuple (r.key.map tag) ++ [.rowArrow, tag r.value, .punctuation ';'])), '}'⟩

private def kleisliName : KleisliKind → String
  | .category => "finite_kleisli" | .triple => "finite_kleisli_triple"

def form (d : Source.Declaration) : Option Form :=
  let schema := fun rhs => Form.mk ([.ident "schema", .ident d.name, .punctuation '='] ++ rhs) [] ';'
  let instance_ := fun s rhs => Form.mk ([.ident "instance", .ident d.name, .punctuation ':', ref s,
    .punctuation '='] ++ rhs) [] ';'
  match d.body with
  | .finiteCarrier tags => some ⟨[.ident "finite", .ident d.name, .punctuation '{'] ++
      tags.flatMap (fun t => [tag t, .punctuation ';']), [], '}'⟩
  | .finiteTable axes out rows => some (table d.name axes out [] rows)
  | .composableTable axes out src dst rows =>
    some (table d.name axes out (.ident "where" :: application "composable" [src,dst]) rows)
  | .categorySchema => some (schema [.ident "finite_category"])
  | .functorSchema => some (schema [.ident "finite_functor"])
  | .isoSchema => some (schema [.ident "finite_iso"])
  | .natTransSchema => some (schema [.ident "finite_nat_trans"])
  | .monadSchema => some (schema [.ident "finite_monad"])
  | .kleisliSchema k s => some (schema (application (kleisliName k) [s]))
  | .finiteCategory s g => some (instance_ s (application "finite_graph" [g.objects,g.arrows,g.src,g.dst,g.ids,g.comp]))
  | .finiteOpposite s c => some (instance_ s [.ident "Opposite", .punctuation '<', ref c, .punctuation '>'])
  | .finiteFunctor s f => some (instance_ s (application "finite_functor" [f.source,f.target,f.objects,f.arrows]))
  | .finiteIso s i => some (instance_ s (application "finite_iso" [i.category,i.source,i.target,i.forward,i.inverse]))
  | .finiteNatTrans s t => some (instance_ s (application "finite_nat_trans" [t.source,t.target,t.components]))
  | .finiteMonad s m => some (instance_ s (application "finite_monad" [m.category,m.functor,m.unit,m.multiplication]))
  | .finiteKleisli k s m => some (instance_ s (application (kleisliName k) [m]))
  | _ => none

inductive DeclarationSyntax where
  | namespaceModule (name : String)
  | namespaceImport (declaration : Namespace.Import)
  | indexed (declaration : Form)
  | function (declaration : FunctionSource.Function)
  /-- Ordinary singleton and the top-level statement indices observed in main. -/
  | singleton (declaration : FunctionSource.Function) (shown : List Nat)

structure Item where
  packageSource : String
  modulePath : List String
  span : Span
  isPublic : Bool
  syntax_ : DeclarationSyntax

def declarations (program : ResourceSource.Program) : List Item :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    let item := fun span visibility syntax_ => Item.mk pkg.id.source m.pureModule.module.path span visibility syntax_
    let indexed := m.pureModule.declarations.filterMap fun d =>
      (form d).map fun shape => item d.span d.isPublic (.indexed shape)
    let imports := m.pureModule.module.imports.map fun i => item i.span i.isPublic (.namespaceImport i)
    let mod := m.pureModule.module
    let modules := mod.path.getLast?.toList.map fun name =>
      Item.mk pkg.id.source mod.path.dropLast mod.span mod.isPublic (.namespaceModule name)
    ((modules ++ imports) ++ indexed) ++ m.pureModule.functions.map fun f =>
      if f.finiteBinders.isEmpty then
        let shown := ((m.observations.lookup f.name).getD []).map (·.statement)
        item f.span f.isPublic (.singleton f shown)
      else item f.span f.isPublic (.function f)

private def errorAt (span : Span) (message : String) : Diagnostic := {code := "E_FINITE_SOURCE", span, message}

private def sourceError (kind : SiteKind) (span : Span) (message : String) : Diagnostic :=
  match kind with
  | .namespaceModule => {code := "E_MODULE_SOURCE", span, message}
  | .namespaceImport => {code := "E_IMPORT_SOURCE", span, message}
  | .singleton => {code := "E_FUNCTION_SOURCE", span, message}
  | .indexed | .finiteFunction => errorAt span message

def Item.kind (item : Item) : SiteKind :=
  match item.syntax_ with
  | .namespaceModule _ => .namespaceModule
  | .namespaceImport _ => .namespaceImport
  | .indexed _ => .indexed
  | .function _ => .finiteFunction
  | .singleton .. => .singleton

/-- The flat frontend admits main only in the entry file. The other physical
files under the same protected package identity are `--lib` inputs. -/
def Item.inFile (item : Item) (index entry : Nat) : Bool :=
  index == entry || item.packageSource != flatPackageId.source ||
    match item.syntax_ with
    | .singleton f _ | .function f => f.name != "main"
    | .indexed _ | .namespaceImport _ | .namespaceModule _ => true

private def readTokens (file : File) (before : Cursor) (tokens : List ExactLexeme)
    (report : Span → String → Diagnostic := errorAt) : Except Diagnostic Cursor :=
  tokens.foldlM (init := before) fun cursor token =>
    (expectExact file cursor token).mapError fun msg =>
      let span := (file.next cursor).toOption.map (·.span)
      let offset := file.base + cursor.pos.byteIdx
      report (span.getD ⟨offset, offset, cursor.line, cursor.column⟩) msg

private def replayIndexed (file : File) (first : Token) (shape : Form) (span : Span) : Except Diagnostic Unit := do
  unless first.kind matches .word "indexed" do throw (errorAt first.span "expected a finite indexed declaration")
  let mut after ← readTokens file first.after shape.header
  for (span, row) in shape.rows do
    let head ← (file.next after).mapError (errorAt first.span)
    after ← readTokens file after row
    unless sameSpan file head after span do throw (errorAt head.span "finite table row span differs from its source")
  after ← readTokens file after [.punctuation shape.closing]
  unless sameSpan file first after span do throw (errorAt first.span "finite declaration span differs from its source")

/-- The namespace frontend records the keyword span for an inline module
and the entire declaration span when it loads an external module. -/
private def replayModule (file : File) (first : Token) (name : String) (span : Span) : Except Diagnostic Unit := do
  let report := sourceError .namespaceModule
  unless first.kind matches .word "mod" do throw (report first.span "expected mod declaration")
  let after ← readTokens file first.after [.ident name] report
  let delimiter ← (file.next after).mapError (report span)
  let actual ← match delimiter.kind with
    | .symbol '{' => pure first.span
    | .symbol ';' => pure {first.span with «end» := delimiter.span.end}
    | _ => throw (report delimiter.span "expected module body or semicolon")
  unless actual == span do throw (report first.span "mod declaration span differs from its source")

private def replayImport (file : File) (first : Token) (entry : Namespace.Import) : Except Diagnostic Unit := do
  let report := sourceError .namespaceImport
  unless first.kind matches .word "use" do throw (report first.span "expected use declaration")
  let after ← readTokens file first.after (pathLexemes entry.path) report
  let delimiter ← (file.next after).mapError (report entry.span)
  let beforeSemi ← if delimiter.kind matches .word "as" then do
    let alias ← (file.next delimiter.after).mapError (report entry.span)
    if strictKeywords.contains entry.alias || Namespace.indexedSpelling entry.alias then
      throw ⟨"E_RESERVED", "reserved explicit import alias", alias.span, []⟩
    Namespace.sourceName entry.alias alias.span
    readTokens file delimiter.after [.ident entry.alias] report
  else do
    unless entry.path.getLast? == some entry.alias do throw (report delimiter.span "implicit import alias differs from its path")
    pure after
  let closed ← readTokens file beforeSemi [.punctuation ';'] report
  unless sameSpan file first closed entry.span do throw (report first.span "use declaration span differs from its source")

def replay (file : File) (before : Cursor) (item : Item) : Except Diagnostic Unit := do
  let first ← (file.next before).mapError (errorAt item.span)
  match item.syntax_ with
  | .namespaceModule name => replayModule file first name item.span
  | .namespaceImport entry => replayImport file first entry
  | .indexed shape => replayIndexed file first shape item.span
  | .function f => MethodBodyText.checkFunction file first f []
  | .singleton f shown => MethodBodyText.checkFunction file first f shown

abbrev Sites := Std.HashMap Nat FiniteSite

def Corresponds (layout : PhysicalSources.Layout) (sites : Sites) (item : Item) : Prop :=
  ∃ site file, sites[item.span.start]? = some site ∧ layout.files[site.fileIndex]? = some file ∧
    (site.packageSource, site.modulePath, site.isPublic) = (item.packageSource, item.modulePath, item.isPublic) ∧
    site.kind = item.kind ∧ item.inFile site.fileIndex layout.entry = true ∧
    replay ⟨file.text, file.offset⟩ site.before item = .ok ()

private def checkOne (layout : PhysicalSources.Layout) (sites : Sites) (item : Item) :
    Except Diagnostic Unit := do
  let some site := sites[item.span.start]? |
    throw (sourceError item.kind item.span "declaration missing from physical source")
  unless site.kind == item.kind do
    throw (sourceError site.kind site.span "declaration kind differs from the physical source")
  let some file := layout.files[site.fileIndex]? |
    throw (sourceError site.kind site.span "missing physical declaration file")
  unless (site.packageSource, site.modulePath, site.isPublic) = (item.packageSource, item.modulePath, item.isPublic) do
    throw (sourceError site.kind site.span "declaration owner or visibility differs from physical source")
  unless item.inFile site.fileIndex layout.entry do
    throw ⟨"E_LIBRARY", "a --lib file cannot provide main; define the entrypoint in the input file", item.span, []⟩
  replay ⟨file.text, file.offset⟩ site.before item

private theorem checkOne_sound {layout : PhysicalSources.Layout} {sites : Sites} {item : Item}
    (h : checkOne layout sites item = .ok ()) : Corresponds layout sites item := by
  cases hs : sites[item.span.start]? with
  | none => simp [checkOne, hs, throw] at h
  | some site =>
    by_cases kind : site.kind = item.kind
    · cases hf : layout.files[site.fileIndex]? with
      | none => simp [checkOne, hs, kind, hf, throw] at h
      | some file =>
        by_cases owner : (site.packageSource, site.modulePath, site.isPublic) =
            (item.packageSource, item.modulePath, item.isPublic)
        · cases located : item.inFile site.fileIndex layout.entry with
          | false => simp [checkOne, hs, kind, hf, owner, located, bind, Except.bind, throw] at h
          | true =>
            refine ⟨site, file, hs, hf, owner, kind, located, ?_⟩
            simpa [checkOne, hs, kind, hf, owner, located, bind, Except.bind, pure] using h
        · simp [checkOne, hs, kind, hf, owner, throw, bind, Except.bind] at h
    · simp [checkOne, hs, kind, throw, bind, Except.bind] at h

def checkAll (layout : PhysicalSources.Layout) (sites : Sites) : List Item → Except Diagnostic Unit
  | [] => .ok ()
  | first :: rest => do
    let _ ← checkOne layout sites first
    checkAll layout sites rest

theorem checkAll_sound {layout : PhysicalSources.Layout} {sites : Sites} {items : List Item}
    (h : checkAll layout sites items = .ok ()) : ∀ i ∈ items, Corresponds layout sites i := by
  induction items with
  | nil => simp
  | cons first rest ih =>
    cases e : checkOne layout sites first with
    | error err => simp [checkAll, e, bind, Except.bind] at h
    | ok proof =>
      simp [checkAll, e, bind, Except.bind] at h
      intro i member
      rcases List.mem_cons.mp member with rfl | later
      · exact checkOne_sound e
      · exact ih h _ later

private def inventoryError (sites : Sites) (items : List Item) : Diagnostic :=
  let expected : Std.HashSet Nat := .ofList (items.map (·.span.start))
  if let some (_, missing) := sites.toList.find? (fun (k,_) => !expected.contains k) then
    sourceError missing.kind missing.span "physical declaration omitted from the request"
  else
    match items.find? (fun item => !sites.contains item.span.start) with
    | some item => sourceError item.kind item.span "declaration inventory differs from physical source"
    | none => errorAt {} "duplicate physical declaration start"

def check (layout : PhysicalSources.Layout) (sites : Sites) (items : List Item) : Except Diagnostic Unit :=
  if Finite.sameCounts sites.keys (items.map (·.span.start)) then checkAll layout sites items
  else .error (inventoryError sites items)

/-- A single concrete declaration can be replayed by separately proving the
inventory, its physical owner and the syntax at that location. -/
theorem check_singleton {layout : PhysicalSources.Layout} {sites : Sites} {item : Item}
    {site : FiniteSite} {file : PhysicalSources.File}
    (keys : sites.keys = [item.span.start]) (lookup : sites[item.span.start]? = some site)
    (physical : layout.files[site.fileIndex]? = some file)
    (kind : site.kind = item.kind)
    (owner : (site.packageSource, site.modulePath, site.isPublic) = (item.packageSource, item.modulePath, item.isPublic))
    (location : item.inFile site.fileIndex layout.entry = true)
    (parsed : replay ⟨file.text, file.offset⟩ site.before item = .ok ()) :
    check layout sites [item] = .ok () := by
  have covered : Finite.sameCounts [item.span.start] [item.span.start] = true := by
    simp [Finite.sameCounts, Finite.countIndex]
  simp [check, keys, covered, checkAll, checkOne, lookup, physical, kind, owner, location, parsed, bind, Except.bind]

theorem check_sound {layout : PhysicalSources.Layout} {sites : Sites} {items : List Item}
    (h : check layout sites items = .ok ()) :
    Finite.sameCounts sites.keys (items.map (·.span.start)) = true ∧ ∀ i ∈ items, Corresponds layout sites i := by
  unfold check at h
  split at h
  · exact ⟨by assumption, checkAll_sound h⟩
  · contradiction

end VastitasKernel.FiniteSourceFiles
