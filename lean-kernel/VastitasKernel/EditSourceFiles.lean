import VastitasKernel.FiniteSourceFiles
import VastitasKernel.MethodBodyText
import VastitasKernel.ResourceCellSource

set_option autoImplicit false

/-! Reconstruct the source declarations that supply edit authority. The
authority checker selects contributions and checks every body. This pass
binds the declarations, signatures and method bodies to their physical files. -/
namespace VastitasKernel.EditSourceFiles
open Indexed AssemblyText

private def resultTokens : Core.PureType → List ExactLexeme
  | .nat => [.ident "Nat"]
  | .int => [.ident "Int"]
  | .unit => [.ident "Unit"]
  | .bool => [.ident "Bool"]
  | .pair element =>
    [.ident "Pair", .punctuation '<', .ident (match element with | .nat => "Nat" | .int => "Int"), .punctuation '>']

private def method (m : DispatchSource.Method) : Except String EditMethod := do
  let params ← m.params.mapM fun p => do
    let .data (.named ty) := p.ty | throw "contributed fn requires a named selector"
    pure (p.name, ty.splitOn "::", p.span)
  let .mk _ _ body := m.body
  return ⟨⟨m.target.path, params, m.requirements, resultTokens m.result⟩, m.span, body⟩

private def header (kind name : String) (target : List String) : List ExactLexeme :=
  [.ident kind, .ident name, .punctuation ':'] ++ pathLexemes target

private def recipient (pkg : Namespace.RecipientPackage) (path : List String) : Except String (List ExactLexeme) := do
  let .name name := pkg | throw "physical edit recipient requires a manifest package name"
  return [.ident "to"] ++ pathLexemes (name :: path)

private def insert (table : EditDeclarations) (decl : EditDeclaration) : Except String EditDeclarations := do
  if table.headers.contains decl.span.start then throw "duplicate physical edit declaration"
  return {table with headers := table.headers.insert decl.span.start decl}

private def explicitDomain (g : Namespace.Generic) : Except String (List ExactLexeme) := do
  let params := g.params.map fun p => [.reference [p.name] p.span]
  let rows ← g.domain.mapM fun key => do
    let names ← key.mapM fun ty => do
      let .named name := ty | throw "expected a concrete family domain selector"
      pure [.ident name]
    pure ([.punctuation '('] ++ listLexemes names ')')
  return [.ident g.name, .punctuation '('] ++ listLexemes params ')' ++
    [.ident "domain", .punctuation '('] ++ listLexemes rows ')' ++ [.punctuation ';']

private def contract (c : RawAbstractMethod) : Except String FamilyDeclaration := do
  let params ← c.params.mapM fun p => do
    let .named name := p.ty | throw "contract requires a named selector"
    pure (p.name, name.splitOn "::", p.span)
  let result ← match c.returnType with
    | .named name => pure [.ident name]
    | .pair name => pure [.ident "Pair", .punctuation '<', .ident name, .punctuation '>']
    | _ => throw "unsupported family contract result"
  let domain := c.domain.map fun row => row.map fun p => (p.path, p.span)
  return .contract ⟨c.name.splitOn "::", params, c.requirements, result⟩ domain

private def addFamily (edits : EditDeclarations) (decl : ScopedDeclaration) : Except String EditDeclarations := do
  let start := decl.span.start
  if edits.families.contains start || edits.headers.contains start then throw "duplicate physical declaration start"
  return {edits with families := edits.families.insert start decl}

/-- Inference copies the first declaration's full span and its typed parameter
spans, including when that first declaration is a bodyless contract. -/
private abbrev FirstDeclarations := Std.HashMap String (Span × List (String × Span))

private def recordFirst (table : FirstDeclarations) (name : String) (span : Span) (params : List (String × Span)) :=
  if table[name]?.any (fun item => item.1.start ≤ span.start) then table else table.insert name (span, params)

/-- Edit revisions number defining methods in their declaring order. Without
edits, an unordered wire inventory still identifies each body by its source
span and must preserve order-independent finite dispatch. -/
private def checkEditOrder (program : ResourceSource.Program) : Except String Unit := do
  for pkg in program.packages do
    for m in pkg.modules do
      let mut previous : Std.HashMap (List String) Nat := {}
      for d in m.pureModule.methods do
        let target := d.target.path
        if previous[target]?.any (· ≥ d.span.start) then throw "method order differs from the source family"
        previous := previous.insert target d.span.start

def collect (program : ResourceSource.Program) : Except String EditDeclarations := do
  let mut table : EditDeclarations := {}
  for pkg in program.packages do
    for m in pkg.modules do
      let owner := m.pureModule.module
      let make := fun span visibility tokens => ExactHeader.mk pkg.id.source owner.path span visibility tokens
      for (kind, grants) in [("grant", owner.grants), ("delegation", owner.delegations)] do
        for g in grants do
          let rows := g.region.map fun key =>
            [.punctuation '('] ++ listLexemes (key.map fun name => pathLexemes (name.splitOn "::")) ')'
          let tokens := header kind g.name g.target ++ (← recipient g.granteePackage g.granteePath) ++
            (if g.delegable then [.ident "delegable"] else []) ++ [.punctuation '{', .ident "domain"] ++
            listLexemes rows ';' ++ [.punctuation '}']
          table ← insert table ⟨make g.span g.isPublic tokens, none⟩
      for t in owner.transfers do
        let tokens := header "transfer" t.name t.target ++ (← recipient t.granteePackage t.granteePath) ++ [.punctuation ';']
        table ← insert table ⟨make t.span t.isPublic tokens, none⟩
      for c in m.pureModule.contributions do
        let tokens := header "contribution" c.name c.target.path ++ [.punctuation '{']
        table ← insert table ⟨make c.span c.isPublic tokens, some (c.name, ← c.methods.mapM method)⟩
      let key := fun target => (pkg.id.source, owner.path, target)
      let mut locals : Std.HashMap String Namespace.Generic := {}
      for g in owner.generics do
        locals := locals.insert g.name g
        table := {table with targets := table.targets.insert (key [g.name])}
        unless g.inferDomain do
          table ← addFamily table ⟨pkg.id.source, owner.path, g.span, some g.isPublic, .header (← explicitDomain g)⟩
      for i in owner.imports do
        table := {table with targets := table.targets.insert (key [i.alias])}
      let visibility := fun name => locals[name]?.bind fun g =>
        if g.inferDomain || !g.isPublic then some g.isPublic else none
      let mut first : FirstDeclarations := {}
      for d in m.pureModule.methods do
        let target := d.target.path
        let name := String.intercalate "::" target
        first := recordFirst first name d.span (d.params.map fun p => (p.name, p.span))
        table ← addFamily table ⟨pkg.id.source, owner.path, d.span, visibility name, .method (← method d)⟩
        table := {table with targets := table.targets.insert (key target)}
      for c in owner.abstractMethods do
        first := recordFirst first c.name c.span (c.params.map fun p => (p.name, p.span))
        table ← addFamily table ⟨pkg.id.source, owner.path, c.span, visibility c.name, ← contract c⟩
      for g in owner.generics do
        if g.inferDomain then
          let origin := (g.span, g.params.map fun p => (p.name, p.span))
          unless first[g.name]? == some origin do throw "inferred family header differs from its first declaration"
  if !table.headers.isEmpty || ExactModelSource.hasAssembly program then checkEditOrder program
  return table

structure OwnedMethod where
  packageSource : String
  modulePath : List String
  contribution : Option String
  method : DispatchSource.Method

/-- Include all defining methods and each contribution
with its original declaring scope, whether or not the assembly applied it. -/
def sourceMethods (program : ResourceSource.Program) : List OwnedMethod :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    let owned := fun origin d => OwnedMethod.mk pkg.id.source m.pureModule.module.path origin d
    m.pureModule.methods.map (owned none) ++ m.pureModule.contributions.flatMap fun c =>
      c.methods.map (owned (some c.name))

def OwnedMethod.owner (item : OwnedMethod) : MethodOwner :=
  ⟨item.packageSource, item.modulePath, item.contribution, item.method.target.path⟩

def BodyCorresponds (layout : PhysicalSources.Layout) (checked : SourceChecks) (item : OwnedMethod) : Prop :=
  ∃ site file close, checked.bodies[item.method.span.start]? = some site ∧
    site.owner = item.owner ∧ site.declaration = item.method.span ∧
    layout.files[site.fileIndex]? = some file ∧
    MethodBodyText.check ⟨file.text, file.offset⟩ site.opening item.method.body = .ok close ∧
    close.span = site.closing

private def diagnostic (span : Span) (message : String) : Diagnostic :=
  {code := "E_ASSEMBLY", message, span}

private def replayBody (layout : PhysicalSources.Layout) (checked : SourceChecks) (item : OwnedMethod) :
    Except Diagnostic (PLift (BodyCorresponds layout checked item)) := do
  match hs : checked.bodies[item.method.span.start]? with
  | none => throw (diagnostic item.method.span "missing physical method body")
  | some site =>
    if owner : site.owner = item.owner ∧ site.declaration = item.method.span then
      match hf : layout.files[site.fileIndex]? with
      | none => throw (diagnostic site.opening "missing physical method file")
      | some file =>
        match replay : MethodBodyText.check ⟨file.text, file.offset⟩ site.opening item.method.body with
        | .error why => throw why
        | .ok close =>
          if extent : close.span = site.closing then
            return ⟨⟨site, file, close, hs, owner.1, owner.2, hf, replay, extent⟩⟩
          else throw (diagnostic close.span "method did not consume the full physical body")
    else throw (diagnostic site.declaration "method body belongs to another physical module")

def checkBodies (layout : PhysicalSources.Layout) (checked : SourceChecks) : List OwnedMethod → Except Diagnostic Unit
  | [] => .ok ()
  | first :: rest => do
    let _ ← replayBody layout checked first
    checkBodies layout checked rest

theorem checkBodies_sound {layout : PhysicalSources.Layout} {checked : SourceChecks} {items : List OwnedMethod}
    (accepted : checkBodies layout checked items = .ok ()) {item : OwnedMethod} (member : item ∈ items) :
    BodyCorresponds layout checked item := by
  induction items with
  | nil => contradiction
  | cons first rest ih =>
    cases h : replayBody layout checked first with
    | error err => simp [checkBodies, h, bind, Except.bind] at accepted
    | ok proof =>
      simp [checkBodies, h, bind, Except.bind] at accepted
      rcases List.mem_cons.mp member with rfl | later
      · exact proof.down
      · exact ih accepted later

/-- Stop at the second possible function keyword without allocating substrings.
The declaration scanner subsequently classifies the tokens in their scopes. -/
private def secondFnMarker (bytes : ByteArray) : Nat → Nat → Bool → Bool
  | 0, _, _ => false
  | left + 1, i, seen =>
    if bytes[i]? == some 'f'.toUInt8 && bytes[i + 1]? == some 'n'.toUInt8 then
      seen || secondFnMarker bytes left (i + 1) true
    else secondFnMarker bytes left (i + 1) seen

def relevant (source : String) : Bool :=
  -- A single file with just one nullary definition and no contract, selector,
  -- qualification or requirement cannot introduce dispatch on its own.
  (source.contains "fn" && (source.contains ":" || source.contains ";" ||
    source.contains "requires" || secondFnMarker source.toUTF8 (source.utf8ByteSize - 1) 0 false)) ||
  ["grant", "delegation", "transfer", "contribution", "assembl", "generic", "method"].any fun word => source.contains word

def check (json : Lean.Json) (program : ResourceSource.Program) : Except Diagnostic Unit := do
  let expected ← (collect program).mapError (diagnostic {})
  let layout ← (PhysicalSources.layout json).mapError (diagnostic {})
  let checked ← (ExactModelSource.scanFiles layout program relevant {edits := some expected}).mapError (diagnostic {})
  unless checked.edits.any (·.isEmpty) do
    throw (diagnostic {} "edit declaration has no matching physical source")
  ResourceCellSource.check layout checked.cells (ResourceCellSource.items program)
  checkBodies layout checked (sourceMethods program)
  FiniteSourceFiles.check layout checked.finiteSites (FiniteSourceFiles.declarations program)

theorem all_evidence {json : Lean.Json} {program : ResourceSource.Program}
    (accepted : check json program = .ok ()) :
    ∃ expected layout checked, collect program = .ok expected ∧ PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout program relevant {edits := some expected} = .ok checked ∧
      checked.edits.any (·.isEmpty) = true ∧
      ResourceCellSource.check layout checked.cells (ResourceCellSource.items program) = .ok () ∧
      checkBodies layout checked (sourceMethods program) = .ok () ∧
      FiniteSourceFiles.check layout checked.finiteSites (FiniteSourceFiles.declarations program) = .ok () := by
  cases h : collect program <;> simp [check, Except.mapError, bind, Except.bind, h] at accepted
  rename_i expected
  cases l : PhysicalSources.layout json <;> simp [l] at accepted
  rename_i layout
  cases s : ExactModelSource.scanFiles layout program relevant {edits := some expected} <;>
    simp [s] at accepted
  rename_i checked
  cases e : checked.edits.any (·.isEmpty) <;> simp [e, throw] at accepted
  cases cells : ResourceCellSource.check layout checked.cells (ResourceCellSource.items program) <;> simp [cells] at accepted
  cases b : checkBodies layout checked (sourceMethods program) <;> simp [b] at accepted
  exact ⟨expected, layout, checked, rfl, rfl, s, e, cells, b, accepted⟩

theorem check_evidence {json : Lean.Json} {program : ResourceSource.Program}
    (accepted : check json program = .ok ()) :
    ∃ expected layout checked, collect program = .ok expected ∧ PhysicalSources.layout json = .ok layout ∧
      ExactModelSource.scanFiles layout program relevant {edits := some expected} = .ok checked ∧
      checked.edits.any (·.isEmpty) = true ∧ checkBodies layout checked (sourceMethods program) = .ok () ∧
      FiniteSourceFiles.check layout checked.finiteSites (FiniteSourceFiles.declarations program) = .ok () := by
  obtain ⟨expected, layout, checked, inputs, files, scan, edits, _, bodies, finite⟩ := all_evidence accepted
  exact ⟨expected, layout, checked, inputs, files, scan, edits, bodies, finite⟩

end VastitasKernel.EditSourceFiles
