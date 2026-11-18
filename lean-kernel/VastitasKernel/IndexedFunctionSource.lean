import VastitasKernel.IndexedSource
import VastitasKernel.Surface

/-! Source syntax before Fn erasure. Data types reuse the indexed
annotation AST. Fn signatures retain source paths until their writing scope is known;
the public decoder (`IndexedBodyProtocol`) constructs this AST, then
`ResourceSource.Wire.check` composes its compiler with dispatch and authority
validation. This AST is not an
independent wire acceptance entry point. -/
namespace VastitasKernel.Indexed.FunctionSource

abbrev SignatureSyntax := Surface.TypeExpr Source.DataType
abbrev Signature := Surface.TypeExpr Core.DataType

def callableSourceData : Source.DataType → Bool
  | .pure .nat | .pure .int | .pure .bool | .pure .unit | .finiteHom .. => true
  | _ => false

def callableCoreData : Core.DataType → Bool
  | .pure .nat | .pure .int | .pure .bool | .pure .unit | .finite (.hom ..) => true
  | _ => false

inductive FnType where
  | data (type : Source.DataType)
  | function (signature : SignatureSyntax)
  deriving Repr, Inhabited

/-- A function-valued type contains an actual Fn shape, not an arbitrary data
annotation disguised by the outer constructor. -/
def FnType.Valid : FnType → Bool
  | .data _ => true
  | .function s => s.isFunction && s.allData callableSourceData && s.withinDepth Limits.typeNesting

def FnType.callable : FnType → Option SignatureSyntax
  | .data ty => if callableSourceData ty then some (.data ty) else none
  | .function signature => if (FnType.function signature).Valid then some signature else none

structure Param where
  name : String
  type : FnType
  span : Span := {}
  deriving Repr, Inhabited

/-- Static model and object parameters. The schema declaration determines
whether an unqualified model binder names a category or a Monad. -/
inductive StaticBinder where
  | category (name : String) (schema : Source.Path) (span : Span)
  | object (name category : String) (span : Span)
  | monadObject (name monad : String) (span : Span)
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | functionValue (path : Source.Path) (span : Span)
    | call (callee : Source.Path) (arguments : List Expr) (span : Span)
    | finiteCall (callee : Source.Path) (indices : List Source.Path) (arguments : List Expr) (span : Span)
    | finiteLookup (table : Source.Path) (arguments : List Expr) (span : Span)
    | invoke (callee : Expr) (arguments : List Expr) (span : Span)
    | lambda (params : List Param) (result : FnType) (body : Block) (span : Span)
    | lifted (id : Nat) (span : Span) -- backend-only, rejected in source
    | unary (operator : String) (operand : Expr) (span : Span)
    | binary (operator : String) (left right : Expr) (span : Span)
    | branch (condition : Expr) (yes no : Block) (span : Span)
    | block (body : Block) (span : Span)
    | pack (type : Source.DataType) (witness : Expr) (fields : List Expr) (span : Span)
    deriving Repr, Inhabited
  inductive Stmt where
    | letE (name : String) (annotation : Option FnType) (value : Expr) (span : Span)
    | unpack (value : Expr) (witness : String) (fields : List String) (span : Span)
    deriving Repr, Inhabited
  inductive Block where
    | mk (statements : List Stmt) (result : Expr) (span : Span)
    deriving Repr, Inhabited
end

def Expr.span : Expr → Span
  | .integer _ span | .boolean _ span | .unit span | .variable _ span
  | .finiteCall _ _ _ span | .finiteLookup _ _ span | .functionValue _ span | .call _ _ span
  | .invoke _ _ span | .lambda _ _ _ span
  | .lifted _ span | .unary _ _ span | .binary _ _ _ span | .branch _ _ _ span
  | .block _ span | .pack _ _ _ span => span

structure Function where
  name : String
  params : List Param
  result : FnType
  body : Block
  isPublic : Bool := false
  span : Span := {}
  finiteBinders : List StaticBinder := []
  deriving Repr, Inhabited

def Function.callable (function : Function) : Option SignatureSyntax := do
  guard function.finiteBinders.isEmpty
  let parameters ← function.params.mapM (fun param => param.type.callable)
  let result ← function.result.callable
  return .function parameters result

def Function.higher (function : Function) : Bool :=
  function.params.any (fun param => match param.type with | .function _ => true | _ => false) ||
    match function.result with | .function _ => true | _ => false

/-- Only names, visibility and spans are consumed by namespace resolution.
The intentionally ill-typed placeholder cannot replace actual body checking. -/
def Function.namespaceHeader (function : Function) : Source.Function := {
  name := function.name, params := [], result := .pure .int,
  body := .mk [] (.unit function.span) function.span,
  isPublic := function.isPublic, span := function.span }

structure Module where
  module : Namespace.Module
  declarations : List Source.Declaration
  functions : List Function
  deriving Repr, Inhabited

structure Package where
  id : Namespace.PackageId
  dependencies : List Namespace.Dependency
  modules : List Module
  geometryCompat : Option (GeometryProfile Source.Path) := none
  deriving Repr, Inhabited

structure Program where
  file : String
  root : String
  packages : List Package
  extended : Bool := false
  editable : Bool := false
  authority : Bool := false
  deriving Repr, Inhabited

def Program.headers (program : Program) : Source.Program := {
  file := program.file, root := program.root,
  extended := program.extended, editable := program.editable, authority := program.authority,
  packages := program.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies, geometryCompat := pkg.geometryCompat,
    modules := pkg.modules.map fun m => {
      module := { m.module with
        hasFiniteCompose := m.functions.any (fun f => f.name == "compose" && !f.finiteBinders.isEmpty) },
      declarations := m.declarations,
      -- A finite callable forwarding method shares the represented method's
      -- namespace entry. Every method remains in finiteFunctions for checking.
      functions := m.functions.filterMap fun f =>
        if !f.finiteBinders.isEmpty && f.higher then none else some f.namespaceHeader } } }

private def Program.namedFunctions (program : Program) : List (DeclId × Function) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.functions.map fun function => (⟨⟨pkg.id, m.module.path⟩, function.name⟩, function)

/-- Ordinary functions are lifted into executable definitions immediately.
Finite templates stay in the same namespace and are instantiated after type inference. -/
def Program.functions (program : Program) : List (DeclId × Function) :=
  program.namedFunctions.filter fun (_, f) => f.finiteBinders.isEmpty

def Program.finiteFunctions (program : Program) : List (DeclId × Function) :=
  program.namedFunctions.filter fun (_, f) => !f.finiteBinders.isEmpty

end VastitasKernel.Indexed.FunctionSource
