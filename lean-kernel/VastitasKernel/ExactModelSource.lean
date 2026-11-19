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
  let mut manifests : Std.TreeSet String := {}
  for pkg in program.packages do
    if program.root != flatPackageId.source then manifests := manifests.insert pkg.id.source
    for m in pkg.modules do
      for decl in m.pureModule.declarations do
        if let .exactGeometry c := decl.body then
          if let .affine _ _ coords := c then
            unless coords.all SpectralDeclarations.isIdentifier do throw "invalid exact affine coordinate identifier"
          if headers.contains decl.span.start then throw "duplicate physical exact declaration"
          headers := headers.insert decl.span.start ⟨decl.span, decl.isPublic, lexemes decl.name c⟩
  for file in layout.files do
    unless (String.fromUTF8? file.path).any manifests.contains do
      headers ← checkExactHeaders file.text file.offset headers
  unless headers.isEmpty do throw "exact declaration has no matching physical source"

end VastitasKernel.ExactModelSource
