import VastitasKernel.ExactModelSource

set_option autoImplicit false

/-! Reconstruct the source declarations that supply edit authority. The
authority checker selects contributions and checks every body. This pass
binds the declarations, signatures and body extents to their physical files. -/
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
  if table.contains decl.span.start then throw "duplicate physical edit declaration"
  return table.insert decl.span.start decl

def collect (program : ResourceSource.Program) : Except String EditDeclarations := do
  let mut table := {}
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
        table ← insert table ⟨make c.span c.isPublic tokens, some (← c.methods.mapM method)⟩
  return table

def relevant (source : String) : Bool :=
  ["grant", "delegation", "transfer", "contribution", "assembl", "generic", "method"].any fun word => source.contains word

def check (json : Lean.Json) (program : ResourceSource.Program) : Except String Unit := do
  let expected ← collect program
  let layout ← PhysicalSources.layout json
  let checked ← ExactModelSource.scanFiles layout program relevant {edits := some expected}
  unless checked.edits.any (·.isEmpty) do throw "edit declaration has no matching physical source"

end VastitasKernel.EditSourceFiles
