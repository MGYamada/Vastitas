import VastitasKernel.ExactModelSource
import VastitasKernel.MethodBodyText

set_option autoImplicit false

/-! Replay finite declarations from the original file after the independent
table, endpoint and law checks. Match table rows and finite-indexed function
signatures and bodies at their original source spans. -/
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
  | indexed (declaration : Form)
  | function (declaration : FunctionSource.Function)

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
    indexed ++ m.pureModule.functions.filterMap fun f =>
      if f.finiteBinders.isEmpty then none else some (item f.span f.isPublic (.function f))

private def errorAt (span : Span) (message : String) : Diagnostic := {code := "E_FINITE_SOURCE", span, message}

private def readTokens (file : File) (before : Cursor) (tokens : List ExactLexeme) : Except Diagnostic Cursor :=
  tokens.foldlM (init := before) fun cursor token =>
    (expectExact file cursor token).mapError fun msg =>
      let span := (file.next cursor).toOption.map (·.span)
      let offset := file.base + cursor.pos.byteIdx
      errorAt (span.getD ⟨offset, offset, cursor.line, cursor.column⟩) msg

private def replayIndexed (file : File) (first : Token) (shape : Form) (span : Span) : Except Diagnostic Unit := do
  unless first.kind matches .word "indexed" do throw (errorAt first.span "expected a finite indexed declaration")
  let mut after ← readTokens file first.after shape.header
  for (span, row) in shape.rows do
    let head ← (file.next after).mapError (errorAt first.span)
    after ← readTokens file after row
    unless sameSpan file head after span do throw (errorAt head.span "finite table row span differs from its source")
  after ← readTokens file after [.punctuation shape.closing]
  unless sameSpan file first after span do throw (errorAt first.span "finite declaration span differs from its source")

def replay (file : File) (before : Cursor) (item : Item) : Except Diagnostic Unit := do
  let first ← (file.next before).mapError (errorAt item.span)
  match item.syntax_ with
  | .indexed shape => replayIndexed file first shape item.span
  | .function f => MethodBodyText.checkFiniteFunction file first f

abbrev Sites := Std.HashMap Nat FiniteSite

def Corresponds (layout : PhysicalSources.Layout) (sites : Sites) (item : Item) : Prop :=
  ∃ site file, sites[item.span.start]? = some site ∧ layout.files[site.fileIndex]? = some file ∧
    (site.packageSource, site.modulePath, site.isPublic) = (item.packageSource, item.modulePath, item.isPublic) ∧
    replay ⟨file.text, file.offset⟩ site.before item = .ok ()

private def checkOne (layout : PhysicalSources.Layout) (sites : Sites) (item : Item) :
    Except Diagnostic (PLift (Corresponds layout sites item)) := do
  match hs : sites[item.span.start]? with
  | none => throw (errorAt item.span "finite declaration missing from physical source")
  | some site =>
    match hf : layout.files[site.fileIndex]? with
    | none => throw (errorAt site.span "missing physical finite declaration file")
    | some file =>
      if h : (site.packageSource, site.modulePath, site.isPublic) = (item.packageSource, item.modulePath, item.isPublic) then
        match hr : replay ⟨file.text, file.offset⟩ site.before item with
        | .ok () => return ⟨⟨site,file,hs,hf,h,hr⟩⟩
        | .error err => throw err
      else throw (errorAt site.span "finite declaration owner or visibility differs from physical source")

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
      · exact proof.down
      · exact ih h _ later

private def inventoryError (sites : Sites) (items : List Item) : Diagnostic :=
  let expected : Std.HashSet Nat := .ofList (items.map (·.span.start))
  if let some (_, missing) := sites.toList.find? (fun (k,_) => !expected.contains k) then
    errorAt missing.span "physical finite declaration omitted from the request"
  else
    let span := (items.find? (fun item => !sites.contains item.span.start)).map (·.span)
    errorAt (span.getD {}) "finite declaration inventory differs from physical source"

def check (layout : PhysicalSources.Layout) (sites : Sites) (items : List Item) : Except Diagnostic Unit :=
  if Finite.sameCounts sites.keys (items.map (·.span.start)) then checkAll layout sites items
  else .error (inventoryError sites items)

theorem check_sound {layout : PhysicalSources.Layout} {sites : Sites} {items : List Item}
    (h : check layout sites items = .ok ()) :
    Finite.sameCounts sites.keys (items.map (·.span.start)) = true ∧ ∀ i ∈ items, Corresponds layout sites i := by
  unfold check at h
  split at h
  · exact ⟨by assumption, checkAll_sound h⟩
  · contradiction

end VastitasKernel.FiniteSourceFiles
