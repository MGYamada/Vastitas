import VastitasKernel.ExactModelSource
import VastitasKernel.MethodBodyText

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
  return ⟨m.target.path, params, m.requirements, resultTokens m.result, m.span, body⟩

private def header (kind name : String) (target : List String) : List ExactLexeme :=
  [.ident kind, .ident name, .punctuation ':'] ++ pathLexemes target

private def recipient (pkg : Namespace.RecipientPackage) (path : List String) : Except String (List ExactLexeme) := do
  let .name name := pkg | throw "physical edit recipient requires a manifest package name"
  return [.ident "to"] ++ pathLexemes (name :: path)

private def insert (table : EditDeclarations) (decl : EditDeclaration) : Except String EditDeclarations := do
  if table.headers.contains decl.span.start then throw "duplicate physical edit declaration"
  return {table with headers := table.headers.insert decl.span.start decl}

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
  -- An edit can select a defining body or leave it as a fallback. Retain
  -- ordinary family methods even when the caller never invokes the family.
  if !table.headers.isEmpty || ExactModelSource.hasAssembly program then
    for pkg in program.packages do
      for m in pkg.modules do
        let owner := m.pureModule.module
        let key := fun target => (pkg.id.source, owner.path, target)
        for g in owner.generics do
          table := {table with targets := table.targets.insert (key [g.name])}
        for i in owner.imports do
          table := {table with targets := table.targets.insert (key [i.alias])}
        let mut previous : Std.HashMap (List String) Nat := {}
        for decl in m.pureModule.methods do
          let start := decl.span.start
          if table.headers.contains start || table.methods.contains start then throw "duplicate physical method start"
          if previous[decl.target.path]?.any (· ≥ start) then throw "method order differs from the source family"
          previous := previous.insert decl.target.path start
          let expected ← method decl
          table := {table with
            targets := table.targets.insert (key decl.target.path)
            methods := table.methods.insert start (pkg.id.source, owner.path, expected)}
  return table

structure OwnedMethod where
  packageSource : String
  modulePath : List String
  contribution : Option String
  method : DispatchSource.Method

def hasEdits (program : ResourceSource.Program) : Bool :=
  program.packages.any fun pkg => pkg.modules.any fun m =>
    let owner := m.pureModule.module
    !owner.grants.isEmpty || !owner.delegations.isEmpty || !owner.transfers.isEmpty ||
      !m.pureModule.contributions.isEmpty || owner.assembly.any fun a => !a.events.isEmpty

/-- Include all defining methods in an edited program and each contribution
with its original declaring scope, whether or not the assembly applied it. -/
def sourceMethods (program : ResourceSource.Program) : List OwnedMethod :=
  let edited := hasEdits program
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    let owned := fun origin d => OwnedMethod.mk pkg.id.source m.pureModule.module.path origin d
    (if edited then m.pureModule.methods.map (owned none) else []) ++ m.pureModule.contributions.flatMap fun c =>
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

def relevant (source : String) : Bool :=
  ["grant", "delegation", "transfer", "contribution", "assembl", "generic", "method"].any fun word => source.contains word

def check (json : Lean.Json) (program : ResourceSource.Program) : Except Diagnostic Unit := do
  let expected ← (collect program).mapError (diagnostic {})
  let layout ← (PhysicalSources.layout json).mapError (diagnostic {})
  let checked ← (ExactModelSource.scanFiles layout program relevant {edits := some expected}).mapError (diagnostic {})
  unless checked.edits.any (·.isEmpty) do
    throw (diagnostic {} "edit declaration has no matching physical source")
  checkBodies layout checked (sourceMethods program)

end VastitasKernel.EditSourceFiles
