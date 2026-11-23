import VastitasKernel.ResourceStatementSource

set_option autoImplicit false

/-! Replay the port types of a resource function at its physical declaration. -/
namespace VastitasKernel.ResourceHeaderSource
open AssemblyText ResourceSource ResourceStatementSource SourceText

structure Signature where
  name : String
  parameters : List Parameter
  results : List (String × Storage.Functions.ResultType String)
  valueType : Indexed.Core.PureType

private def applied (name : String) (args : List (List ExactLexeme)) : Parser Unit :=
  tokens ([.ident name, .punctuation '<'] ++ (args.intersperse [.punctuation ',']).flatten ++ [.punctuation '>'])

private def portAccess : Storage.Access → String
  | .read => "Read" | .write => "Write" | .readWrite => "ReadWrite"

private def owned (ty : Storage.Functions.OwnedType) : Parser Unit := do
  applied "Owned" [ExactModelSource.storageRepresentation ty.scalar, [.dimension ty.elements]]
  if !ty.initialized.isEmpty || ((← peek).kind matches .word "initialized") then
    token (.ident "initialized")
    delimited '[' ']' ty.initialized fun l =>
      tokens (layoutFields (some l.offset) (.dimension l.rows) (.dimension l.columns) (.dimension l.leading) l.transposed)

private def initializes (present : Bool) : Parser Unit := do
  if present then token (.ident "initializes")

private def parameterType : Parameter → Parser Unit
  | .value _ ty _ => tokens (pureTypeTokens ty)
  | .owned _ ty _ => owned ty
  | .borrowed _ scalar rows cols access init _ => do
    applied (portAccess access) [ExactModelSource.storageRepresentation scalar, [.dimension rows], [.dimension cols]]
    initializes init
  | .space _ impl dim _ => applied "Space" [[.reference impl.path impl.span], [.dimension dim]]
  | .runtimeSpace _ impl dim _ => applied "RuntimeSpace" [[.reference impl.path impl.span], [extent dim]]
  | .basis _ space _ => applied "Basis" [[.ident space]]
  | .runtimeBasis _ space _ => applied "RuntimeBasis" [[.ident space]]
  | .runtimeMap _ src dst access init _ => do
    applied "RuntimeMap" [[.ident src], [.ident dst], [.ident (accessName access)]]
    initializes init
  | .involution _ space _ => applied "Involution" [[.ident space]]
  | .dualSpace _ parent _ => applied "DualSpace" [[.ident parent]]
  | .conjugateSpace _ parent inv _ => applied "ConjugateSpace" [[.ident parent], [.ident inv]]
  | .derivedBasis _ parent space _ => applied "DerivedBasis" [[.ident parent], [.ident space]]
  | .metric _ basis inv orthonormal _ =>
    applied (if orthonormal then "OrthonormalMetric" else "Metric") [[.ident basis], [.ident inv]]
  | .ownedMap _ src dst _ => applied "OwnedMap" [[.ident src], [.ident dst]]
  | .ownedMapTo _ src dim _ => applied "OwnedMapTo" [[.ident src], [.dimension dim]]
  | .map _ src dst access init _ => do
    applied (portAccess access ++ "Map") [[.ident src], [.ident dst]]
    initializes init
  | .vector _ basis access init _ => do
    applied (portAccess access ++ "Vector") [[.ident basis]]
    initializes init

private def parameter (p : Parameter) : Parser Unit := do
  let head ← peek
  tokens [.ident p.name, .punctuation ':']
  parameterType p
  unless sameSpan (← read) head (← get) p.span do
    throw (diagnostic head.span "resource parameter span differs from its declaration")

private def result (port : String × Storage.Functions.ResultType String) : Parser Unit := do
  tokens [.ident port.1, .punctuation ':']
  match port.2 with
  | .owned ty => owned ty
  | .ownedMap src dst => applied "OwnedMap" [[.ident src], [.ident dst]]
  | .ownedMapTo src dim => applied "OwnedMapTo" [[.ident src], [.dimension dim]]

def header (s : Signature) : Parser Unit := do
  tokens [.ident "resource", .ident "fn", .ident s.name]
  delimited '(' ')' s.parameters parameter
  if !s.results.isEmpty || ((← peek).kind matches .word "returns") then
    token (.ident "returns")
    delimited '(' ')' s.results result
  token .arrow
  tokens (pureTypeTokens s.valueType)
  token (.punctuation '{')

end VastitasKernel.ResourceHeaderSource
