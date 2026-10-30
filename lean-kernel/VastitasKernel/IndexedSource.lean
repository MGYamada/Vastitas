import VastitasKernel.Namespace
import VastitasKernel.IndexedCore
import VastitasKernel.IndexedGeometryProfile

/-! Unresolved declaration input for the forthcoming source/protocol-7 path.
Owners are reconstructed from enclosing packages/modules, never supplied on a
declaration or reference. This internal AST is not yet a public wire protocol. -/
namespace VastitasKernel.Indexed.Source

abbrev Path := TypePath

inductive Representation where
  | affineDescriptor
  | scalarBase (setting : GeometricSetting) (coefficient : CoefficientKind)
  | linearDescriptor (base : Path) (coefficient : CoefficientKind)
  deriving Repr, Inhabited

inductive Parameter where
  | domain | marker | natural
  | object (domain : Path)
  deriving Repr, Inhabited

structure Family where
  parameters : List Parameter
  constraints : List Indexed.Constraint
  representation : FamilyRepresentation
  deriving Repr, Inhabited

structure ObjectType where
  domain : Path
  marker : Path
  deriving Repr, Inhabited

inductive BoundIndex where
  | witness
  | global (declaration : Path)
  | domain (declaration : Path)
  | marker (declaration : Path)
  | natural (value : Nat)
  deriving Repr, Inhabited

structure BoundApplication where
  family : Path
  indices : List BoundIndex
  deriving Repr, Inhabited

structure PackageShape where
  witnessType : ObjectType
  fields : List BoundApplication
  deriving Repr, Inhabited

inductive Primitive where
  | descriptor (implementation : Path)
  | global (declaration : Path)
  | origin (domain : ObjectType) (pointFamily baseObject : Path)
  | identity (domain : ObjectType) (mapFamily : Path)
  | dimension (domain : ObjectType)
  | compose (mapFamily : Path)
  | apply (mapFamily pointFamily : Path)
  deriving Repr, Inhabited

inductive Body where
  | marker
  | implementation (marker : Path) (representation : Representation)
      (capabilities : List Capability)
  | classification (parents domain : List Path)
  | global (implementation : Path)
  | family (contract : Family)
  | package (cases : List PackageShape)
  | primitive (binding : Primitive)
  deriving Repr, Inhabited

structure Declaration where
  name : String
  body : Body
  isPublic : Bool
  span : Span
  deriving Repr, Inhabited

inductive TypeArgument where
  | name (path : Path)
  | natural (value : Nat)
  deriving Repr, Inhabited

inductive DataType where
  | pure (type : Core.PureType)
  | object (type : Source.ObjectType)
  | application (family : Path) (arguments : List TypeArgument)
  | legacy (type : RawType)
  | inferredPackage -- only produced by the old pack syntax; never a signature
  deriving Repr, Inhabited

/- The initial internal body adapter handles data functions. Fn lifting and
finite dispatch/edit composition must be added before public protocol 7. -/
structure Param where
  name : String
  type : Source.DataType
  span : Span := {}
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | call (callee : Path) (arguments : List Expr) (span : Span)
    | unary (operator : String) (operand : Expr) (span : Span)
    | binary (operator : String) (left right : Expr) (span : Span)
    | branch (condition : Expr) (yes no : Block) (span : Span)
    | block (body : Block) (span : Span)
    | pack (type : Source.DataType) (witness : Expr) (fields : List Expr) (span : Span)
    deriving Repr, Inhabited
  inductive Stmt where
    | letE (name : String) (annotation : Option Source.DataType) (value : Expr) (span : Span)
    | unpack (value : Expr) (witness : String) (fields : List String) (span : Span)
    deriving Repr, Inhabited
  inductive Block where
    | mk (statements : List Stmt) (result : Expr) (span : Span)
    deriving Repr, Inhabited
end

def Expr.span : Expr → Span
  | .integer _ span | .boolean _ span | .unit span | .variable _ span
  | .call _ _ span | .unary _ _ span | .binary _ _ _ span | .branch _ _ _ span
  | .block _ span | .pack _ _ _ span => span

structure Function where
  name : String
  params : List Param
  result : Source.DataType
  body : Block
  isPublic : Bool
  span : Span
  deriving Repr, Inhabited

/-- Namespace-only header: the existing resolver consumes name/visibility/span,
not this placeholder body. No old surface checker may accept source bodies
through this projection; the body adapter must check the actual Function. -/
def Function.namespaceHeader (f : Function) : Namespace.Function := {
  name := f.name, params := [], result := .data (.named "Int"),
  body := .mk [] (.unit f.span) f.span, isPublic := f.isPublic, span := f.span }

structure Module where
  module : Namespace.Module
  declarations : List Declaration
  functions : List Function := []
  deriving Repr, Inhabited

structure Package where
  id : Namespace.PackageId
  dependencies : List Namespace.Dependency
  modules : List Module
  geometryCompat : Option (GeometryProfile Path) := none
  deriving Repr, Inhabited

structure Program where
  file : String
  root : String
  packages : List Package
  extended : Bool := false
  editable : Bool := false
  authority : Bool := false
  deriving Repr, Inhabited

def Program.toNamespace (p : Program) : Namespace.Program := {
  file := p.file, root := p.root, extended := p.extended, editable := p.editable,
  authority := p.authority, packages := p.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies,
    modules := pkg.modules.map fun m =>
      { m.module with functions := m.module.functions ++ m.functions.map Function.namespaceHeader } } }

def Program.functions (p : Program) : List (Namespace.Owner × Function) :=
  p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.functions.map fun f => (⟨⟨pkg.id, m.module.path⟩, f.name⟩, f)

/-- The input has no field for a declaration owner. Even an unused declaration
in a dependency receives the enclosing package's full canonical identity. -/
def Program.owned (p : Program) : List (Namespace.Owner × Declaration) :=
  p.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.declarations.map fun declaration =>
      (⟨⟨pkg.id, m.module.path⟩, declaration.name⟩, declaration)

def Program.targets (p : Program) : List Namespace.Target :=
  p.toNamespace.declarations ++ p.owned.map fun (owner, declaration) =>
    ⟨owner, .indexedDeclaration, declaration.isPublic⟩

/-- The original namespace resolver sees one shared namespace. These indexes
are rebuilt from the input, not received as frontend lookup certificates. -/
def Program.indexed (p : Program) : Namespace.Indexed := {
  toProgram := p.toNamespace, declarations := p.targets,
  byOwner := Namespace.ownerIndex p.targets, byScope := Namespace.scopeIndex p.targets }

def Body.category : Body → Nat
  | .package _ => 1
  | .primitive _ => 2
  | _ => 0

/-- Match the three ordered tables in Core.Declarations without sorting IDs or
discarding duplicates. The namespace audit rejects cross-category collisions. -/
def Program.declarationIds (p : Program) : List DeclId :=
  [0, 1, 2].flatMap fun category =>
    (p.owned.filter fun (_, declaration) => declaration.body.category == category).map Prod.fst

structure Reference where
  scope : Namespace.Scope
  path : Path
  target : Namespace.Target
  deriving Repr, Inhabited

structure Resolved where
  declarations : Core.Declarations
  references : List Reference
  geometry : Option (GeometryProfile DeclId) := none
  deriving Repr, Inhabited

end VastitasKernel.Indexed.Source
