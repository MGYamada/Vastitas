import VastitasKernel.IndexedDispatchCheck
import VastitasKernel.IndexedFunctionRegression

namespace VastitasKernel.Indexed.DispatchSource.Regression
open FunctionSource

private def path (name : String) : Source.Path := ⟨name.splitOn "::", {}⟩
private def int : FnType := .data (.pure .int)
private def num (n : Nat) : Expr := .integer (toString n) {}
private def var (name : String) : Expr := .variable name {}
private def call (name : String) (args : List Expr := []) : Expr := .call (path name) args {}
private def block (value : Expr) (statements : List Stmt := []) : Block := .mk statements value {}
private def main (value : Expr) (statements : List Stmt := []) : FunctionSource.Function :=
  ⟨"main", [], int, block value statements, true, {}⟩
private def generic : Namespace.Generic := {
  name := "adjust", params := [{ name := "value", span := {} }], domain := [[.named "Int"]],
  isPublic := true, span := {} }
private def method (selector : String) (body : Block) : Method := {
  target := path "adjust", params := [⟨"x", .data (.named selector), {}⟩], result := .int,
  requirements := [], body }
private def broad : Method := method "Number" (block (num 3))
private def narrow : Method := method "Int" (block (call "twice" [
  .lambda [⟨"n", int, {}⟩] int (block (.binary "+" (var "n")
    (call "int" [call "geo::dimension" [call "geo::Affine" [num 2]]]) {})) {}, var "x"]))

private def program (methods : List Method) (entry : FunctionSource.Function := main (call "adjust" [num 38])) : Program :=
  let source := FunctionSource.Regression.higherFixture
  { file := source.file, root := source.root, packages := source.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies, modules := pkg.modules.map fun m => {
      module := { m.module with generics := if pkg.id.source == source.root then [generic] else [] },
      declarations := m.declarations,
      functions := if pkg.id.source == source.root then m.functions.filter (·.name != "main") ++ [entry] else m.functions,
      methods := if pkg.id.source == source.root then methods else [] } } }

private def accepts (name : String) (p : Program) : IO Unit :=
  match checkProgram p true with
  | .ok _ => pure ()
  | .error d => throw (IO.userError s!"indexed dispatch {name}: {d.code}: {d.message}")
private def rejects (name code : String) (p : Program) : IO Unit :=
  match checkProgram p true with
  | .ok _ => throw (IO.userError s!"indexed dispatch {name}: unexpectedly accepted")
  | .error d => unless d.code == code do
      throw (IO.userError s!"indexed dispatch {name}: expected {code}, got {d.code}: {d.message}")
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed dispatch regression failed: {name}")

def dispatchFixture : Program := program [broad, narrow]
#eval accepts "indexed method and higher-order callback" dispatchFixture
#eval accepts "method order invariance" (program [narrow, broad])
#eval rejects "applicable nonwinner body" "E_TYPE" (program [{ broad with body := block (.boolean false {}) }, narrow])
#eval rejects "out-of-domain applicable body" "E_TYPE" (program
  [{ broad with body := block (.binary "+" (var "x") (num 1) {}) }, narrow])
#eval rejects "generic is not a Fn value" "E_TYPE" (program [broad, narrow]
  (main (.invoke (.functionValue (path "adjust") {}) [num 1] {})))
#eval rejects "Pair is not a dispatch key" "E_TYPE" (program [broad, narrow]
  (main (call "adjust" [call "pair" [num 1, num 2]])))
#eval rejects "indexed object is not a dispatch key" "E_TYPE" (program [broad, narrow]
  (main (call "adjust" [call "geo::Affine" [num 2]])))
#eval rejects "Fn is not a dispatch key" "E_TYPE" (program [broad, narrow]
  (main (call "adjust" [var "add1"])))
#eval rejects "call outside domain" "E_DISPATCH_DOMAIN" (program [broad, narrow]
  (main (call "adjust" [var "n"]) [.letE "n" (some (.data (.pure .nat))) (num 3) {}]))
#eval rejects "generic arity before selection" "E_ARITY" (program [broad, narrow] (main (call "adjust" [])))
#eval rejects "Fn selector is not erased to Unit" "E_TYPE" (program
  [{ broad with params := [⟨"x", .function (.cons (.data (.named "Int")) .nil) (.data (.named "Int")), {}⟩] }])
#eval rejects "method lambda capture" "E_CAPTURE" (program [broad,
  { narrow with body := block (.invoke (.lambda [⟨"n", int, {}⟩] int (block (var "x")) {}) [num 1] {}) }])
#eval rejects "method lambda shadow" "E_SHADOW" (program [broad,
  { narrow with body := block (.invoke (.lambda [⟨"x", int, {}⟩] int (block (var "x")) {}) [num 1] {}) }])
#eval rejects "generic method recursion" "E_RECURSION" (program [broad,
  { narrow with body := block (call "adjust" [var "x"]) }])
#eval rejects "applicable coverage absent even without call" "E_DISPATCH_COVERAGE" (program [] (main (num 0)))
#eval rejects "duplicate methods" "E_DUPLICATE" (program [broad, broad])
#eval rejects "unsupported authority envelope" "E_STAGE" { dispatchFixture with editable := true, authority := true }

private def rootModule (p : Program) (change : Module → Module) : Program :=
  { p with packages := p.packages.map fun pkg => { pkg with modules := pkg.modules.map fun m =>
    if pkg.id.source == p.root && m.module.path.isEmpty then change m else m } }
private def contract (result : RawType := .named "Int") : RawAbstractMethod := {
  name := "adjust", params := [⟨"x", .named "Number", {}⟩], returnType := result,
  domain := [[path "Number"]], requirements := [], span := {} }
def contractFixture : Program := rootModule { dispatchFixture with extended := true } fun m =>
  { m with module := { m.module with generics := [{ generic with domain := [] }], abstractMethods := [contract] } }
#eval accepts "abstract contract expands callable domain" contractFixture
#eval rejects "exact contract result" "E_CONTRACT_RESULT" (rootModule contractFixture fun m =>
  { m with module := { m.module with abstractMethods := [contract (.named "Nat")] } })
#eval rejects "old method body cannot be silently omitted" "E_STAGE" (rootModule dispatchFixture fun m =>
  { m with module := { m.module with methods := [broad.header] } })

private def libraryModule (p : Program) (change : Module → Module) : Program :=
  { p with packages := p.packages.map fun pkg => { pkg with modules := pkg.modules.map fun m =>
    if pkg.id.source != p.root && m.module.path.isEmpty then change m else m } }
#eval rejects "foreign generic owner" "E_OWNER" (libraryModule
  (program [{ broad with target := path "geo::foreign" }]) fun m =>
    { m with module := { m.module with generics := [{ generic with name := "foreign" }] } })
#eval rejects "foreign scalar membership owner" "E_OWNER" (libraryModule
  (rootModule { dispatchFixture with extended := true } fun m =>
    { m with module := { m.module with subtypes := [⟨"Int", path "geo::Foreign", {}⟩] } }) fun m =>
      { m with module := { m.module with abstractTypes := [⟨⟨"Foreign", [path "Number"], {}⟩, true⟩] } })

private def nominal (name : String) : Namespace.AbstractType := ⟨⟨name, [path "Number"], {}⟩, true⟩
def nominalFixture : Program := rootModule { program [method "Arithmetic" (block (num 17))] with extended := true } fun m =>
  { m with module := { m.module with
    abstractTypes := [nominal "Arithmetic"],
    subtypes := [⟨"Nat", path "Arithmetic", {}⟩, ⟨"Int", path "Arithmetic", {}⟩] } }
#eval accepts "nominal selector and exact scalar membership" nominalFixture
#eval rejects "equal inhabitants are not selector subtyping" "E_DISPATCH_AMBIGUOUS" (rootModule
  { program [method "First" (block (num 1)), method "Second" (block (num 2))] with extended := true } fun m =>
    { m with module := { m.module with abstractTypes := [nominal "First", nominal "Second"], subtypes :=
      [⟨"Nat", path "First", {}⟩, ⟨"Int", path "First", {}⟩,
       ⟨"Nat", path "Second", {}⟩, ⟨"Int", path "Second", {}⟩] } })
#eval accepts "Lean-established capability filters keys" (program
  [{ (method "Any" (block (num 5))) with requirements := ["HasOrder"] }])
#eval rejects "nominal/capability product order" "E_DISPATCH_AMBIGUOUS" (program
  [{ (method "Any" (block (num 5))) with requirements := ["HasOrder"] }, narrow])
#eval rejects "unknown capability" "E_CAPABILITY" (program [{ broad with requirements := ["Imaginary"] }])
#eval accepts "package order does not change canonical selection" { dispatchFixture with packages := dispatchFixture.packages.reverse }

private def pairMethod : Method := { (method "Number" (block (call "pair" [num 1, num 2]))) with result := .pair .int }
def pairFixture : Program := program [pairMethod] (main (call "pair_first" [call "adjust" [num 8]]))
#eval accepts "Pair method result stays outside keys" pairFixture
#eval rejects "method duplicate binder" "E_SHADOW" (program [{ broad with params := [⟨"adjust", .data (.named "Number"), {}⟩] }])

private def twoArgumentAmbiguity : Program := rootModule
  (program [
    { broad with params := [⟨"x", .data (.named "Int"), {}⟩, ⟨"y", .data (.named "Number"), {}⟩] },
    { broad with params := [⟨"x", .data (.named "Number"), {}⟩, ⟨"y", .data (.named "Int"), {}⟩] }]
    (main (num 0))) fun m =>
      { m with module := { m.module with generics := [{ generic with
        params := [⟨"left", {}⟩, ⟨"right", {}⟩], domain := [] }] } }
#eval rejects "ambiguity outside empty callable domain" "E_DISPATCH_AMBIGUOUS" twoArgumentAmbiguity

#eval check "all applicable pairs become audited source bodies" (match checkProgram dispatchFixture true with
  | .error _ => false
  | .ok checked => checked.dispatch.instances.length == 3 &&
      checked.dispatch.instances.all fun entry => checked.audit.lowered.origins.any fun key =>
        checked.compiler.input.dispatch.definitions[(entry.method, entry.key)]? == some key.definition)
#eval check "forged selected method rejected" (match checkProgram dispatchFixture true with
  | .error _ => false
  | .ok checked => match checked.executable.lowered.dispatchCalls.head? with
    | none => false
    | some call => !Compiler.validPass checked.compiler.input false { checked.executable.lowered with
        dispatchCalls := [{ call with method := 999 }] })
#eval check "forged source method/key table rejected" (match checkProgram dispatchFixture true with
  | .error _ => false
  | .ok checked => !instancesValid checked.dispatch { checked.compiler with input :=
      { checked.compiler.input with dispatch := { checked.compiler.input.dispatch with definitions := {} } } })
#eval check "omitted nonwinner expansion rejected" (match checkProgram dispatchFixture true with
  | .error _ => false
  | .ok checked => !expansionValid checked.dispatch.families checked.dispatch.instances.tail)

private def independentMethod : Method := { broad with
  body := block (.invoke (.lambda [⟨"n", int, {}⟩] int (block (num 3)) {}) [num 0] {}) }
#eval check "method lambda identity shared across scalar keys" (match checkProgram (program [independentMethod]) true with
  | .error _ => false
  | .ok checked => checked.dispatch.instances.length == 2 &&
      (checked.lifted.definitions.toList.filter (·.isLambda)).length == 1)
#eval check "different source lambdas do not share identity by span or body" (match checkProgram
  (program [independentMethod, { independentMethod with params := narrow.params }]) true with
  | .error _ => false
  | .ok checked => (checked.lifted.definitions.toList.filter (·.isLambda)).length == 2)

end VastitasKernel.Indexed.DispatchSource.Regression
