import VastitasKernel.PhysicalSources
import VastitasKernel.ResourceSource

set_option autoImplicit false

/-! Agreement of the closed mathematical declarations and resource realization
calls with their physical edition-2026 files and lexical owners. -/
namespace VastitasKernel.ExactModelSource
open Indexed AssemblyText

private def ref (p : Source.Path) : ExactLexeme := .reference p.path p.span

private def lexemes (name : String) : ExactConstruction Source.Path → List ExactLexeme
  | .cauchyQQ => [.ident "carrier", .ident name, .punctuation '=', .ident "cauchy_qq"]
  | .complexPairs real =>
    [.ident "carrier", .ident name, .punctuation '=', .ident "complex_pairs", .punctuation '(', ref real, .punctuation ')']
  | .realMeadow carrier =>
    [.ident "meadow", .ident name, .punctuation '=', .ident "real_meadow", .punctuation '(', ref carrier, .punctuation ')']
  | .complexMeadow carrier real =>
    [.ident "meadow", .ident name, .punctuation '=', .ident "complex_meadow", .punctuation '(', ref carrier,
      .punctuation ',', ref real, .punctuation ')']
  | .identity subject =>
    [.ident "morphism", .ident name, .punctuation '=', .ident "identity", .punctuation '(', ref subject, .punctuation ')']
  | .affine model n coordinates =>
    [.ident "affine", .ident name, .punctuation '=', .ident "Affine", .punctuation '(', ref model,
      .punctuation ',', .dimension n, .punctuation ')', .punctuation '['] ++
      (coordinates.map ExactLexeme.ident).intersperse (.punctuation ',') ++ [.closeList ']' (!coordinates.isEmpty)]

private def precision (r : ResourceSource.FloatRepresentation) : List ExactLexeme :=
  let (width, carrier) := match r with
    | .real32 => ("F32", "RR") | .complex32 => ("F32", "CC")
    | .real64 => ("F64", "RR") | .complex64 => ("F64", "CC")
  [.separator, .punctuation '<', .ident width, .punctuation '<', .ident carrier,
    .punctuation '>', .punctuation '>']

private def collectCalls (owner : ResourceOwner) (branches : List ResourceBranch) (index : Nat) :
    List ResourceSource.Statement → SourceChecks → Except String SourceChecks
  | [], checks => pure checks
  | first :: tail, checks => do
    let checks ← match first with
      | .realization callee rep args result into span => do
        if checks.calls.contains span.start then throw "duplicate physical realization statement"
        let binding := if into then [] else [.ident "let", .ident result, .punctuation '=']
        let destination := if into then [.arrow, .ident result] else []
        let lexemes := binding ++ [ref callee] ++ (rep.map precision).getD [] ++ [.punctuation '('] ++
          (args.map ref).intersperse (.punctuation ',') ++ [.closeList ')' (!args.isEmpty)] ++ destination
        pure {checks with calls := checks.calls.insert span.start ⟨owner, branches, index, span, lexemes⟩}
      | .branch b yes no _ => do
        let checks ← collectCalls owner (⟨index, .literal b, true⟩ :: branches) 0 yes checks
        collectCalls owner (⟨index, .literal b, false⟩ :: branches) 0 no checks
      | .branchValue name yes no _ => do
        let checks ← collectCalls owner (⟨index, .binding name, true⟩ :: branches) 0 yes checks
        collectCalls owner (⟨index, .binding name, false⟩ :: branches) 0 no checks
      | _ => pure checks
    collectCalls owner branches (index + 1) tail checks

def check (layout : PhysicalSources.Layout) (program : ResourceSource.Program) : Except String Unit := do
  let mut checks : SourceChecks := {}
  let flat := program.root == flatPackageId.source
  let mut manifests : Std.TreeSet String := {}
  for pkg in program.packages do
    if !flat then manifests := manifests.insert pkg.id.source
    for m in pkg.modules do
      for decl in m.pureModule.declarations do
        if let .exactGeometry c := decl.body then
          if let .affine _ _ coords := c then
            unless coords.all SpectralDeclarations.isIdentifier do throw "invalid exact affine coordinate identifier"
          if checks.headers.contains decl.span.start then throw "duplicate physical exact declaration"
          let header := ExactHeader.mk pkg.id.source m.pureModule.module.path decl.span decl.isPublic (lexemes decl.name c)
          checks := {checks with headers := checks.headers.insert decl.span.start header}
      for fn in m.functions do
        checks ← collectCalls ⟨pkg.id.source, m.pureModule.module.path, fn.name, fn.span.start, fn.isPublic⟩ [] 0 fn.body checks
  if checks.isEmpty then
    -- Discover omitted declarations and calls even if the wire has none.
    for file in layout.files do
      unless (String.fromUTF8? file.path).any manifests.contains do
        if mayHaveExactHeaders file.text then
          let _ ← checkExactHeaders file.text file.offset "" [] {}
    return ()
  -- The loader reads each package manifest, its dependencies, then its root.
  -- External modules are visited depth first in the order of their physical
  -- declarations. The same physical path can occur at different offsets.
  let mut pending : List (String × List (List String)) :=
    if flat then [(flatPackageId.source,[[]])] else []
  for file in layout.files do
    if let some name := (String.fromUTF8? file.path).filter manifests.contains then
      pending := (name,[[]]) :: pending
    else
      let (pkg, path :: rest) :: ancestors := pending | throw "source file lacks a declaring module"
      let (external, left) ← checkExactHeaders file.text file.offset pkg path checks
      checks := left
      let next := external.toList ++ rest
      pending := if next.isEmpty then ancestors else (pkg,next) :: ancestors
  unless pending.isEmpty do throw "missing declared external module in physical inputs"
  unless checks.headers.isEmpty do throw "exact declaration has no matching physical source"
  unless checks.calls.isEmpty do throw "realization has no matching physical source"

end VastitasKernel.ExactModelSource
