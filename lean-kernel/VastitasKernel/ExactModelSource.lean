import VastitasKernel.PhysicalSources
import VastitasKernel.ResourceSource

set_option autoImplicit false

/-! Agreement of the closed mathematical declarations with the physical
edition-2026 files. Both the original offsets and all qualified references
participate; user-supplied field or ring proofs have no wire representation. -/
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
      (coordinates.map ExactLexeme.ident).intersperse (.punctuation ',') ++ [.closeCoordinates (!coordinates.isEmpty)]

def check (layout : PhysicalSources.Layout) (program : ResourceSource.Program) : Except String Unit := do
  let mut headers : Std.HashMap Nat ExactHeader := {}
  let flat := program.root == flatPackageId.source
  let mut manifests : Std.TreeSet String := {}
  for pkg in program.packages do
    if !flat then manifests := manifests.insert pkg.id.source
    for m in pkg.modules do
      for decl in m.pureModule.declarations do
        if let .exactGeometry c := decl.body then
          if let .affine _ _ coords := c then
            unless coords.all SpectralDeclarations.isIdentifier do throw "invalid exact affine coordinate identifier"
          if headers.contains decl.span.start then throw "duplicate physical exact declaration"
          headers := headers.insert decl.span.start ⟨pkg.id.source, m.pureModule.module.path, decl.span, decl.isPublic, lexemes decl.name c⟩
  if headers.isEmpty then
    -- An omitted mathematical declaration must still be discovered in its
    -- physical text. Other files need no module traversal in this common case.
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
      let (external, left) ← checkExactHeaders file.text file.offset pkg path headers
      headers := left
      let next := external.toList ++ rest
      pending := if next.isEmpty then ancestors else (pkg,next) :: ancestors
  unless pending.isEmpty do throw "missing declared external module in physical inputs"
  unless headers.isEmpty do throw "exact declaration has no matching physical source"

end VastitasKernel.ExactModelSource
