import VastitasKernel.IndexedFunctionCheck
import VastitasKernel.DispatchChecker

/-! Internal finite scalar dispatch over the declaration-driven source AST.
Method selectors retain the existing scalar/abstract-selector syntax; indexed
values may occur inside bodies, never as dispatch keys or method results. -/
namespace VastitasKernel.Indexed.DispatchSource
open FunctionSource

def pureType (type : Core.PureType) : RawType :=
  match type with
  | .nat => .named "Nat"
  | .int => .named "Int"
  | .bool => .named "Bool"
  | .unit => .named "Unit"
  | .pair .nat => .pair "Nat"
  | .pair .int => .pair "Int"

structure Method where
  target : Source.Path
  params : List Surface.Param
  result : Core.PureType
  requirements : List String
  body : FunctionSource.Block
  span : Span := {}
  deriving Repr, Inhabited

/-- Only declarations/selectors are projected into the existing namespace and
finite-family machinery. This placeholder is never a checked method body. -/
def Method.header (method : Method) : Surface.Method := {
  name := String.intercalate "::" method.target.path
  params := method.params
  result := .data (pureType method.result)
  requirements := method.requirements
  body := .mk [] (.unit method.span) method.span
  span := method.span }

structure Module where
  module : Namespace.Module
  declarations : List Source.Declaration
  functions : List FunctionSource.Function := []
  methods : List Method := []
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

def Program.source (program : Program) : FunctionSource.Program := {
  file := program.file, root := program.root, extended := program.extended,
  editable := program.editable, authority := program.authority,
  packages := program.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies,
    modules := pkg.modules.map fun m => {
      module := { m.module with methods := m.module.methods ++ m.methods.map Method.header },
      declarations := m.declarations, functions := m.functions } } }

/-- Original order and enclosing scope are retained before selector expansion.
No supplied method ID, winner, or source-body correspondence is trusted. -/
def Program.methods (program : Program) : List (Namespace.Scope × Method) :=
  program.packages.flatMap fun pkg => pkg.modules.flatMap fun m =>
    m.methods.map (⟨pkg.id, m.module.path⟩, ·)

def Program.lambdaScopes (program : Program) : List (Namespace.Scope × FunctionSource.LambdaScope) :=
  program.source.lambdaScopes ++ program.methods.flatMap fun (scope, method) =>
    (FunctionSource.blockScopes (method.params.map (·.name)) method.body).map (scope, ·)

def Program.scopesSafe (program : Program) : Bool :=
  let index := program.source.headers.indexed
  program.lambdaScopes.all fun (scope, lambda) => decide (FunctionSource.ScopeSafe index scope lambda)

/-- Until authority composition is installed, reject every old body/edit
envelope explicitly. Abstract selector declarations are checked below. -/
def supported (program : Program) : Namespace.Result Unit := do
  if program.editable || program.authority || program.packages.any (fun pkg => pkg.modules.any fun m =>
      !m.module.functions.isEmpty || !m.module.methods.isEmpty ||
      !m.module.grants.isEmpty || !m.module.delegations.isEmpty || !m.module.transfers.isEmpty ||
      !m.module.contributions.isEmpty || m.module.assembly.isSome) then
    Namespace.problem {} "E_STAGE" "indexed dispatch adapter does not yet compose old bodies or edit authority"

end VastitasKernel.Indexed.DispatchSource
