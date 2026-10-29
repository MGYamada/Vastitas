import VastitasKernel.Namespace
import VastitasKernel.IndexedCore

/-! Unresolved declaration input for the forthcoming source/protocol-7 path.
Owners are reconstructed from enclosing packages/modules, never supplied on a
declaration or reference. This is not yet a public protocol or term elaborator. -/
namespace VastitasKernel.Indexed.Source

abbrev Path := TypePath

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

structure Module where
  module : Namespace.Module
  declarations : List Declaration
  deriving Repr, Inhabited

structure Package where
  id : Namespace.PackageId
  dependencies : List Namespace.Dependency
  modules : List Module
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
    modules := pkg.modules.map (·.module) } }

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
  deriving Repr, Inhabited

end VastitasKernel.Indexed.Source
