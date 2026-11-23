import VastitasKernel.PhysicalSources
import VastitasKernel.ResourceSource

set_option autoImplicit false

/-! Agreement of the closed mathematical declarations and resource realization
calls with their physical edition-2026 files and lexical owners. -/
namespace VastitasKernel.ExactModelSource
open Indexed AssemblyText

private def ref (p : Source.Path) : ExactLexeme := .reference p.path p.span

def keyword : ExactConstruction Source.Path → String
  | .cauchyQQ | .complexPairs .. => "carrier"
  | .realMeadow .. | .complexMeadow .. => "meadow"
  | .affine .. => "affine"
  | .identity .. => "morphism"

/-- The exact-model owner scan and the complete declaration inventory compare
the same constructor, operand paths, chart dimension and coordinate order. -/
def fields : ExactConstruction Source.Path → List ExactLexeme
  | .cauchyQQ => [.punctuation '=', .ident "cauchy_qq"]
  | .complexPairs real =>
    [.punctuation '=', .ident "complex_pairs", .punctuation '(', ref real, .punctuation ')']
  | .realMeadow carrier =>
    [.punctuation '=', .ident "real_meadow", .punctuation '(', ref carrier, .punctuation ')']
  | .complexMeadow carrier real =>
    [.punctuation '=', .ident "complex_meadow", .punctuation '(', ref carrier,
      .punctuation ',', ref real, .punctuation ')']
  | .identity subject =>
    [.punctuation '=', .ident "identity", .punctuation '(', ref subject, .punctuation ')']
  | .affine model n coordinates =>
    [.punctuation '=', .ident "Affine", .punctuation '(', ref model,
      .punctuation ',', .dimension n, .punctuation ')', .punctuation '['] ++
      (coordinates.map ExactLexeme.ident).intersperse (.punctuation ',') ++ [.closeList ']' (!coordinates.isEmpty)]

private def lexemes (name : String) (construction : ExactConstruction Source.Path) : List ExactLexeme :=
  .ident (keyword construction) :: .ident name :: fields construction

def storageRepresentation (r : Storage.Scalar) : List ExactLexeme :=
  let (width, carrier) := match r with
    | .f32 => ("F32", "RR") | .complexF32 => ("F32", "CC")
    | .f64 => ("F64", "RR") | .complexF64 => ("F64", "CC")
  [.ident width, .punctuation '<', .ident carrier, .punctuation '>']

private def precision (r : ResourceSource.FloatRepresentation) : List ExactLexeme :=
  [.separator, .punctuation '<'] ++ storageRepresentation r.scalar ++ [.punctuation '>']

private def collectCalls (owner : ResourceOwner) (branches : List ResourceBranch) (index : Nat) :
    List ResourceSource.Statement → SourceChecks → Except String SourceChecks
  | [], checks => pure checks
  | first :: tail, checks => do
    let checks ← match first with
      | .affineRealization callee site result => do
        if checks.calls.contains site.span.start then throw "duplicate physical realization statement"
        let tokens := [.ident "let", .ident result, .punctuation '=', ref callee, .punctuation '('] ++
          storageRepresentation site.representation.scalar ++ [.punctuation ',', .dimension site.dimension, .closeList ')' true]
        pure {checks with calls := checks.calls.insert site.span.start ⟨owner, branches, index, site.span, tokens⟩}
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

def hasAssembly (program : ResourceSource.Program) : Bool :=
  program.packages.any fun pkg =>
    pkg.modules.any fun m => m.pureModule.module.assembly.any fun a => !a.events.isEmpty

/-- Associate each scanned file with the package and module which declared it.
An empty expected table still discovers omitted declarations in physical files. -/
def scanFiles (layout : PhysicalSources.Layout) (program : ResourceSource.Program)
    (relevant : String → Bool) (initial : SourceChecks) : Except String SourceChecks := do
  let mut checks := initial
  let flat := program.root == flatPackageId.source
  let manifests : Std.TreeSet String := if flat then {} else .ofList (program.packages.map (·.id.source))
  let hasAssembly := checks.edits.isSome && hasAssembly program
  if flat && (hasAssembly || checks.edits.any (fun t => !t.headers.isEmpty)) then
    throw "edit declarations require a package manifest"
  if checks.edits.isNone && checks.isEmpty then
    -- Discover omitted declarations and calls even if the wire has none.
    for file in layout.files do
      unless (String.fromUTF8? file.path).any manifests.contains do
        if relevant file.text then
          let _ ← checkExactHeaders file.text file.offset "" [] checks
    return checks
  -- The loader reads each package manifest, its dependencies, then its root.
  -- External modules are visited depth first in the order of their physical
  -- declarations. The same physical path can occur at different offsets.
  if flat then
    -- The entry and every --lib file contribute to the same protected root
    -- module. The byte layout assigns a separate range to each occurrence.
    for file in layout.files, i in [:layout.files.size] do
      let (external, left) ← checkExactHeaders file.text file.offset program.root []
        {checks with flat := true, fileIndex := i, allowAssembly := false}
      unless external.isEmpty do throw "external modules require a package manifest"
      checks := left
    return checks
  let mut pending : List (String × List (List String)) := []
  for file in layout.files, i in [:layout.files.size] do
    if let some name := (String.fromUTF8? file.path).filter manifests.contains then
      pending := (name,[[]]) :: pending
    else
      let (pkg, path :: rest) :: ancestors := pending | throw "source file lacks a declaring module"
      let entry := pkg == program.root && path.isEmpty
      if checks.edits.isSome && entry != (i == layout.entry) then throw "assembly entry differs from the physical root module"
      let (external, left) ← checkExactHeaders file.text file.offset pkg path {checks with allowAssembly := entry, fileIndex := i}
      checks := left
      let next := external.toList ++ rest
      pending := if next.isEmpty then ancestors else (pkg,next) :: ancestors
  unless pending.isEmpty do throw "missing declared external module in physical inputs"
  return checks

def check (layout : PhysicalSources.Layout) (program : ResourceSource.Program) : Except String Unit := do
  let mut checks : SourceChecks := {}
  for pkg in program.packages do
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
  checks ← scanFiles layout program mayHaveExactHeaders checks
  unless checks.headers.isEmpty do throw "exact declaration has no matching physical source"
  unless checks.calls.isEmpty do throw "realization has no matching physical source"

end VastitasKernel.ExactModelSource
