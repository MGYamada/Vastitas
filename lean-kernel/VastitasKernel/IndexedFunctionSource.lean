import VastitasKernel.IndexedSource
import VastitasKernel.Surface

/-! Internal source syntax before Fn erasure. Data types reuse the indexed
annotation AST. Fn signatures retain the existing scalar/recursive-Fn boundary;
this syntax is not a public wire protocol. -/
namespace VastitasKernel.Indexed.FunctionSource

inductive FnType where
  | data (type : Source.DataType)
  | function (signature : Surface.TypeExpr)
  deriving Repr, Inhabited

/-- A function-valued type contains an actual Fn shape, not an arbitrary data
annotation disguised by the outer constructor. -/
def FnType.Valid : FnType → Bool
  | .data _ => true
  | .function signature => signature.isFunction && signature.callableData && signature.withinDepth Limits.typeNesting

def FnType.callable : FnType → Option Surface.TypeExpr
  | .data (.pure .nat) => some (.data (.named "Nat"))
  | .data (.pure .int) => some (.data (.named "Int"))
  | .data (.pure .bool) => some (.data (.named "Bool"))
  | .data (.pure .unit) => some (.data (.named "Unit"))
  | .function signature => if (FnType.function signature).Valid then some signature else none
  | _ => none

structure Param where
  name : String
  type : FnType
  span : Span := {}
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | functionValue (path : Source.Path) (span : Span)
    | call (callee : Source.Path) (arguments : List Expr) (span : Span)
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
  | .functionValue _ span | .call _ _ span | .invoke _ _ span | .lambda _ _ _ span
  | .lifted _ span | .unary _ _ span | .binary _ _ _ span | .branch _ _ _ span
  | .block _ span | .pack _ _ _ span => span

structure Function where
  name : String
  params : List Param
  result : FnType
  body : Block
  isPublic : Bool := false
  span : Span := {}
  deriving Repr, Inhabited

def Function.callable (function : Function) : Option Surface.TypeExpr := do
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
    id := pkg.id, dependencies := pkg.dependencies,
    modules := pkg.modules.map fun m => {
      module := m.module, declarations := m.declarations,
      functions := m.functions.map Function.namespaceHeader } } }

def Program.functions (program : Program) : List (DeclId × Function) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.functions.map fun function => (⟨⟨pkg.id, m.module.path⟩, function.name⟩, function)

end VastitasKernel.Indexed.FunctionSource
