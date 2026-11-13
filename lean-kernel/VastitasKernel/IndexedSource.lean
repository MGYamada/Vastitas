import VastitasKernel.Namespace
import VastitasKernel.IndexedCore
import VastitasKernel.IndexedGeometryProfile

/-! Unresolved declaration input used by the public protocol-7 path.
Owners are reconstructed from enclosing packages/modules, never supplied on a
declaration or reference. `Indexed.Wire.check` composes declaration, body,
function, dispatch and authority checks; this AST alone is not an acceptance
entry point. Protocol 8 also uses this declaration foundation. -/
namespace VastitasKernel.Indexed.Source

abbrev Path := TypePath

inductive Representation where
  | affineDescriptor
  | scalarBase (setting : GeometricSetting) (coefficient : CoefficientKind)
  | linearDescriptor (base : Path) (coefficient : CoefficientKind)
  | presentedAffine (field : AlgebraDeclarations.ExactField)
  | smoothAffine
  deriving Repr, Inhabited

/-- Unexpanded polynomial syntax. Sums and products are n-ary, so long
polynomials stay shallow. The kernel bounds degree, exponents and digits
before expanding. Rust parses and never evaluates. -/
inductive PolyExpr where
  | natural (value : Nat)
  | fraction (numerator : Int) (denominator : Nat)
  | coordinate (name : String)
  | neg (operand : PolyExpr)
  | sum (terms : List PolyExpr)
  | product (factors : List PolyExpr)
  | pow (base : PolyExpr) (exponent : Nat)
  deriving Repr, Inhabited

inductive Parameter where
  | domain | marker | natural
  | object (domain : Path)
  /-- A frame of the family `family` (Stage 4, protocol 9). -/
  | frame (family : Path)
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

/-- One decoded field of a primitive's wire form. The kinds are exactly what
the indexed declaration decoder (protocols 7 to 9) accepts for a primitive
field. -/
inductive WireArgument where
  | path (path : Path)
  | objectType (type : ObjectType)
  /-- A coordinate name, resolved to its index after elaboration. -/
  | coordinate (name : String)
  /-- A polynomial in coordinates, checked after elaboration. -/
  | polynomial (expression : PolyExpr)
  | pullbackMode (mode : SmoothRuntime.PullbackMode)
  deriving Repr, Inhabited

/-- The kind of a wire field, as a family declares it. -/
inductive WireKind where
  | path | objectType | coordinate | polynomial | pullbackMode
  deriving Repr, Inhabited, DecidableEq, BEq

def WireArgument.kind : WireArgument → WireKind
  | .path _ => .path
  | .objectType _ => .objectType
  | .coordinate _ => .coordinate
  | .polynomial _ => .polynomial
  | .pullbackMode _ => .pullbackMode

/-- The table spelling of a kind, for the generated Rust table. -/
def WireKind.wire : WireKind → String
  | .path => "path"
  | .objectType => "object_type"
  | .coordinate => "coordinate"
  | .polynomial => "polynomial"
  | .pullbackMode => "pullback_mode"

/-- A primitive's wire form: the `op` and its fields, named and in wire order.
The families of `IndexedPrimitiveFamilies` say which ops exist and which fields
each takes; the decoder admits exactly those, and `resolvePrimitive` builds
the binding through the op's family. The arguments the stage passes
elaborate (a coordinate name, a monomial) are read back from here by op and
field name. -/
structure Primitive where
  op : String
  arguments : List (String × WireArgument)
  deriving Repr, Inhabited

/-- The field `name` of the `op` form, if this is that form and has it. -/
def Primitive.argument? (p : Primitive) (op name : String) : Option WireArgument :=
  if p.op == op then (p.arguments.find? (·.1 == name)).map (·.2) else none

def Primitive.coordinate? (p : Primitive) (op name : String) : Option String :=
  match p.argument? op name with
  | some (.coordinate coordinate) => some coordinate
  | _ => none

def Primitive.polynomial? (p : Primitive) (op name : String) : Option PolyExpr :=
  match p.argument? op name with
  | some (.polynomial expression) => some expression
  | _ => none

/-- The Gram matrix of a metric declaration, before elaboration. -/
inductive MetricGram where
  /-- The identity matrix of the object's dimension. -/
  | euclidean
  /-- Rows of constant polynomial expressions in the object's coordinates. -/
  | rows (entries : List (List PolyExpr))
  deriving Repr, Inhabited

/-- The kind of evidence a declaration asks the kernel to compute. -/
inductive EvidenceKind where
  | nondegenerate
  | riemannian
  deriving Repr, Inhabited, DecidableEq

/-- A scale monomial before resolution (Stage 4): a constant coefficient
times a product of powers of scales. -/
structure ScaleMonomial where
  coefficient : PolyExpr
  factors : List (Path × Int)
  deriving Repr, Inhabited

/-- The Gram matrix of a physical metric before resolution (Stage 4). -/
inductive PhysicalGram where
  /-- The identity matrix of the object's dimension. -/
  | euclidean
  /-- Rows of scale monomials. -/
  | gram (rows : List (List ScaleMonomial))
  /-- One scale per coordinate, by coordinate name. -/
  | normalized (scales : List (String × Path))
  deriving Repr, Inhabited

/-- How a declared morphism `X → Y` over `S` is given (Stage 2). -/
inductive MorphismDefinition where
  /-- The images of `Y`'s coordinates, as polynomials in `X`'s coordinates. -/
  | pullback (images : List (String × PolyExpr))
  | identity
  | structureMap
  /-- The projections of a fiber product onto its factors. -/
  | first
  | second
  /-- `D(φ^#(f)) → D(f)` for a declared morphism `φ : Y → X` and `D(f) ⊂ X`:
  the action of `φ` on the structure sheaf over a principal open. -/
  | restrict (morphism : Path)
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
  /-- `spec[generators] relations(…) over base by(name ↦ image, …)` -/
  | affine (implementation : Path) (generators : List String) (relations : List PolyExpr)
      (base : Option Path) (bindings : List (String × PolyExpr))
  /-- `morphism name : family<X, Y, S> = definition` -/
  | morphism (family : Path) (indices : List Path) (definition : MorphismDefinition)
  /-- `fiber(left, right) [via(b ↦ p, …) inverse(b' ↦ p, …)]` over `left`'s base. -/
  | affineFiber (implementation : Path) (left right : Path)
      (via : Option (List (String × PolyExpr) × List (String × PolyExpr)))
  /-- `localize(object, element) inverse u`: the principal open `D(element)`. -/
  | affineLocalization (implementation : Path) (object : Path) (element : PolyExpr) (inverse : String)
  /-- `iso name = forward f inverse g`: two declared morphisms, mutually inverse. -/
  | iso (forward backward : Path)
  /-- `cartesian name = square(first, second) through fiber inverse h`. -/
  | cartesian (first second fiber inverse : Path)
  /-- `Affine(dimension)[coordinates]`: a smooth object (Stage 3). The kernel
  checks the dimension against the coordinates; only the coordinates are kept. -/
  | smoothAffine (implementation : Path) (dimension : Nat) (coordinates : List String)
  /-- `metric name : family<object> = gram`: a metric (Stage 3). The kernel
  evaluates the Gram matrix in the object's coordinates. -/
  | metric (family : Path) (indices : List Path) (gram : MetricGram)
  /-- `evidence name = kind(metric)`: the kernel computes the certificate. -/
  | evidence (metric : Path) (kind : EvidenceKind)
  /-- `frame name : family<object> = columns(…)` (Stage 4): the columns of
  `P` as polynomial expressions in the object's coordinates, or `none` for
  `coordinates`, the coordinate frame, and the declared inverse `Q`, as
  columns. -/
  | frame (family : Path) (indices : List Path) (columns : Option (List (List PolyExpr)))
      (inverse : Option (List (List PolyExpr)))
  /-- `base_dimension name` (Stage 4). -/
  | baseDimension
  /-- `quantity name = dimension` (Stage 4): base dimensions with integer
  exponents. -/
  | quantity (dimension : List (Path × Int))
  /-- `reading name : family<object> = (coordinate: quantity, …)` (Stage 4). -/
  | reading (family : Path) (indices : List Path) (quantities : List (String × Path))
  /-- `scale name = magnitude of quantity` (Stage 4): a constant polynomial
  expression. -/
  | scale (quantity : Path) (magnitude : PolyExpr)
  /-- `physical name : family<object> = interpret(metric, reading = reading, entries)`
  (Stage 4), with the dimension of its terms when declared. -/
  | physicalMetric (family : Path) (indices : List Path) (metric reading : Path)
      (value : Option (List (Path × Int))) (entries : PhysicalGram)
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

/- The narrower internal body adapter handles data functions. Public protocol 7
adds Fn lifting and finite dispatch/edit composition through FunctionSource,
DispatchSource and AuthoritySource before accepting the returned Core. -/
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
  byOwner := Namespace.ownerIndex p.targets, byScope := Namespace.scopeIndex p.targets,
  byPackage := Namespace.packageIndex p.toNamespace.packages,
  indexedPlaces := p.owned.map fun (owner, declaration) => (owner, declaration.span) }

def Body.category : Body → Nat
  | .package _ => 1
  | .primitive _ | .morphism .. | .iso .. | .cartesian .. => 2
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
