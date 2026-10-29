import VastitasKernel.IndexedFunctionCheck
import VastitasKernel.IndexedSourceBodyRegression

namespace VastitasKernel.Indexed.FunctionSource.Regression
open Compiler

private def path (name : String) : Source.Path := ⟨name.splitOn "::", {}⟩
private def int : FnType := .data (.pure .int)
private def nat : FnType := .data (.pure .nat)
private def intFn : Surface.TypeExpr := .function (.cons (.data (.named "Int")) .nil) (.data (.named "Int"))
private def fnInt : FnType := .function intFn
private def var (name : String) : Expr := .variable name {}
private def num (value : Nat) : Expr := .integer (toString value) {}
private def call (name : String) (arguments : List Expr := []) : Expr := .call (path name) arguments {}
private def invoke (callee : Expr) (arguments : List Expr) : Expr := .invoke callee arguments {}
private def block (result : Expr) (statements : List Stmt := []) : Block := .mk statements result {}
private def fn (name : String) (params : List Param) (result : FnType) (body : Block) : Function :=
  ⟨name, params, result, body, true, {}⟩
private def main (value : Expr) (statements : List Stmt := []) : Function := fn "main" [] int (block value statements)
private def bind (name : String) (value : Expr) (type : Option FnType := none) : Stmt := .letE name type value {}
private def lambda (body : Expr) : Expr := .lambda [⟨"x", int, {}⟩] int (block body) {}
private def add1 : Function := fn "add1" [⟨"x", int, {}⟩] int (block (.binary "+" (var "x") (num 1) {}))
private def add2 : Function := fn "add2" [⟨"x", int, {}⟩] int (block (.binary "+" (var "x") (num 2) {}))
private def twice : Function := fn "twice" [⟨"f", fnInt, {}⟩, ⟨"n", int, {}⟩] int
  (block (call "f" [call "f" [var "n"]]))

private def program (functions : List Function) : Program :=
  let p := Source.Regression.declarationFixture
  { file := p.file, root := p.root, packages := p.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies,
    modules := pkg.modules.map fun m => ⟨m.module, m.declarations,
      if pkg.id.source == p.root && m.module.path.isEmpty then functions else []⟩ } }

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed Fn regression failed: {name}")
private def accepts (name : String) (p : Program) (requireMain := true) : IO Unit :=
  match Compiler.checkProgram p requireMain with
  | .error diagnostic => throw (IO.userError s!"indexed Fn {name}: {diagnostic.code}: {diagnostic.message}")
  | .ok _ => pure ()
private def rejects (name code : String) (p : Program) (requireMain := true) : IO Unit :=
  match Compiler.checkProgram p requireMain with
  | .error diagnostic => unless diagnostic.code == code do
      throw (IO.userError s!"indexed Fn {name}: expected {code}, got {diagnostic.code}: {diagnostic.message}")
  | .ok _ => throw (IO.userError s!"indexed Fn {name}: unexpectedly accepted")

/-- Named higher-order targets and a lambda are specialized into the common Core. -/
def higherFixture : Program := program [add1, twice, main
  (.binary "+" (call "twice" [var "add1", num 20])
    (invoke (lambda (.binary "*" (var "x") (num 2) {})) [num 10]) {})]

#eval accepts "named and lambda targets" higherFixture
#eval accepts "empty library" (program []) false
#eval rejects "required main" "E_MAIN" (program [])
#eval accepts "recursive Fn result" (program [add1, twice,
  fn "choose" [⟨"f", fnInt, {}⟩] fnInt (block (var "f")),
  main (invoke (call "choose" [var "add1"]) [num 41])])
#eval accepts "Fn result keeps scalar argument computations" (program [add1,
  fn "choose" [⟨"n", int, {}⟩] fnInt (block (var "add1")), main (invoke (call "choose" [num 2]) [num 3])])
#eval accepts "same-target branch" (program [add1, main
  (invoke (.branch (.boolean false {}) (block (var "add1")) (block (var "add1")) {}) [num 5])])
#eval rejects "different targets even for constant branch" "E_STATIC_CALL" (program [add1, add2, main
  (invoke (.branch (.boolean true {}) (block (var "add1")) (block (var "add2")) {}) [num 5])])
#eval accepts "signature probe joins do not constrain unused Fn parameters" (program [main (num 0),
  fn "pick" [⟨"f", fnInt, {}⟩, ⟨"g", fnInt, {}⟩] fnInt
    (block (.branch (.boolean true {}) (block (var "f")) (block (var "g")) {}))])
#eval rejects "probe join does not authorize executable divergent targets" "E_STATIC_CALL" (program [add1, add2,
  fn "pick" [⟨"f", fnInt, {}⟩, ⟨"g", fnInt, {}⟩] fnInt
    (block (.branch (.boolean true {}) (block (var "f")) (block (var "g")) {})),
  main (invoke (call "pick" [var "add1", var "add2"]) [num 5])])
#eval rejects "unused higher-order body" "E_TYPE" (program [main (num 0),
  fn "bad" [⟨"f", fnInt, {}⟩] int (block (.boolean true {}))])
#eval rejects "unused higher-order invocation" "E_TYPE" (program [main (num 0),
  fn "bad" [⟨"f", fnInt, {}⟩] int (block (call "f" [.boolean true {}]))])
#eval rejects "direct recursion" "E_RECURSION" (program [main (call "main")])
#eval rejects "higher-order recursion" "E_RECURSION" (program [add1, main (call "recur" [var "add1", num 1]),
  fn "recur" [⟨"f", fnInt, {}⟩, ⟨"n", int, {}⟩] int (block (call "recur" [var "f", var "n"]))])
#eval rejects "partial application" "E_ARITY" (program [add1, twice, main (call "twice" [var "add1"])])
#eval rejects "data called" "E_TYPE" (program [main (call "x") [bind "x" (num 1)]])
#eval rejects "Fn used as data" "E_TYPE" (program [add1, main (.binary "+" (var "add1") (num 2) {})])
#eval rejects "Fn/data annotation mismatch" "E_TYPE" (program [add1, main (num 0) [bind "f" (var "add1") (some int)]])
#eval rejects "data/Fn annotation mismatch" "E_TYPE" (program [main (num 0) [bind "f" (num 1) (some fnInt)]])
#eval rejects "malformed Fn constructor" "E_TYPE" (program [main (num 0), fn "bad"
  [⟨"f", .function (.data (.named "Int")), {}⟩] int (block (num 0))])
#eval rejects "source Fn main argument cannot be erased" "E_MAIN" (program [add1,
  fn "main" [⟨"f", fnInt, {}⟩] int (block (num 0)), fn "caller" [] int (block (call "main" [var "add1"]))])
#eval rejects "Fn main return" "E_MAIN" (program [add1, fn "main" [] fnInt (block (var "add1"))])
#eval rejects "outer scalar capture" "E_CAPTURE" (program [main (num 0)
  [bind "outer" (num 2), bind "f" (lambda (.binary "+" (var "x") (var "outer") {}))]])
#eval rejects "outer Fn capture" "E_CAPTURE" (program [add1, main (num 0)
  [bind "outer" (var "add1"), bind "f" (lambda (call "outer" [var "x"]))]])
#eval rejects "lambda parameter shadow" "E_SHADOW" (program [main (num 0)
  [bind "x" (num 2), bind "f" (lambda (var "x"))]])
#eval rejects "lambda local shadow" "E_SHADOW" (program [main (num 0)
  [bind "outer" (num 2), bind "f" (.lambda [⟨"x", int, {}⟩] int
    (block (var "x") [bind "outer" (num 3)]) {})]])
#eval rejects "nested lambda capture" "E_CAPTURE" (program [main (num 0)
  [bind "f" (.lambda [⟨"x", int, {}⟩] fnInt (block (.lambda [⟨"y", int, {}⟩] int (block (var "x")) {})) {})]])
#eval rejects "unknown in inactive lambda branch" "E_NAME" (program [main (num 0)
  [bind "f" (lambda (.branch (.boolean true {}) (block (var "x")) (block (var "absent")) {}))]])
#eval rejects "forged lifted reference" "E_RESERVED" (program [main (num 0) [bind "f" (.lifted 0 {})]])
#eval rejects "Pair in Fn signature" "E_TYPE" (program [main (num 0),
  fn "bad" [⟨"f", fnInt, {}⟩, ⟨"p", .data (.pure (.pair .int)), {}⟩] int (block (num 0))])
#eval rejects "indexed Fn signature" "E_TYPE" (program [main (num 0),
  fn "bad" [⟨"f", fnInt, {}⟩, ⟨"X", .data (.object ⟨path "geo::Scheme", path "geo::QQ"⟩), {}⟩] int (block (num 0))])
#eval rejects "Pair lambda result" "E_TYPE" (program [main (num 0) [bind "f"
  (.lambda [⟨"x", int, {}⟩] (.data (.pure (.pair .int))) (block (call "pair" [var "x", var "x"])) {})]])
#eval rejects "capture through an indexed annotation" "E_CAPTURE" (program [main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "f" (.lambda [⟨"x", int, {}⟩] int
    (block (var "x") [bind "p" (call "geo::origin" [var "X"])
      (some (.data (.application (path "geo::Point") [.name (path "X"), .name (path "geo::Base")])) )]) {})]])

/-- A scalar lambda may create and inspect indexed objects locally. -/
def indexedLambdaFixture : Program := program [twice, main (call "twice" [
  .lambda [⟨"n", int, {}⟩] int (block (.binary "+" (var "n")
    (call "int" [call "geo::dimension" [var "X"]]) {}) [bind "X" (call "geo::Affine" [num 4])]) {}, num 2])]
#eval accepts "indexed operations within independent lambda" indexedLambdaFixture
#eval accepts "Pair local within scalar lambda" (program [main (invoke (lambda (call "pair_first" [call "pair" [var "x", var "x"]])) [num 7])])
#eval rejects "index scope escape inside lambda" "E_ESCAPE" (program [main (num 0) [bind "f"
  (.lambda [⟨"x", int, {}⟩] int (block (var "x") [bind "p" (.block
    (block (call "geo::origin" [var "X"]) [bind "X" (call "geo::Affine" [num 2])]) {})]) {})]])

mutual
  private def dataExpr : Source.Expr → Expr
    | .integer value span => .integer value span
    | .boolean value span => .boolean value span
    | .unit span => .unit span
    | .variable name span => .variable name span
    | .call callee arguments span => .call callee (arguments.map dataExpr) span
    | .unary op value span => .unary op (dataExpr value) span
    | .binary op left right span => .binary op (dataExpr left) (dataExpr right) span
    | .branch condition yes no span => .branch (dataExpr condition) (dataBlock yes) (dataBlock no) span
    | .block body span => .block (dataBlock body) span
    | .pack type witness fields span => .pack type (dataExpr witness) (fields.map dataExpr) span
  private def dataBlock : Source.Block → Block
    | .mk statements result span => .mk (statements.map dataStatement) (dataExpr result) span
  private def dataStatement : Source.Stmt → Stmt
    | .letE name type value span => .letE name (type.map FnType.data) (dataExpr value) span
    | .unpack value witness fields span => .unpack (dataExpr value) witness fields span
end

def dataProgram (program : Source.Program) : Program := {
  file := program.file, root := program.root, extended := program.extended, editable := program.editable, authority := program.authority,
  packages := program.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies,
    modules := pkg.modules.map fun m => {
      module := m.module, declarations := m.declarations,
      functions := m.functions.map fun f => {
        name := f.name, params := f.params.map (fun p => ⟨p.name, .data p.type, p.span⟩), result := .data f.result,
        body := dataBlock f.body, isPublic := f.isPublic, span := f.span } } } }

#eval accepts "data package bodies through Fn path" (dataProgram Source.BodyRegression.packageFixture)
#eval accepts "data multiple fields through Fn path" (dataProgram Source.BodyRegression.multipleFixture)
#eval accepts "data scalars through Fn path" (dataProgram Source.BodyRegression.scalarFixture)
#eval check "accepted executable generates native code" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => (Core.Codegen.generate checked.executable.core).isOk)

private def library (p : Program) (functions : List Function) : Program :=
  { p with packages := [p.packages[0]!, { p.packages[1]! with modules :=
    [{ p.packages[1]!.modules[0]! with functions }] }] }
private def secret : Function := { add1 with name := "secret", isPublic := false }
private def reveal : Function := fn "reveal" [] fnInt (block (var "secret"))
/-- Private functions can be intentionally returned as Fn values. Their bodies
still resolve in the defining module, while direct private paths are rejected. -/
def privateTargetFixture : Program := library (program [main (invoke (call "geo::reveal") [num 8])]) [secret, reveal]
#eval accepts "returned private target" privateTargetFixture
#eval rejects "direct private Fn reference" "E_VISIBILITY"
  (library (program [main (invoke (.functionValue (path "geo::secret") {}) [num 8])]) [secret, reveal])
#eval rejects "direct private call" "E_VISIBILITY" (library (program [main (call "geo::secret" [num 8])]) [secret])
#eval accepts "dependent alias package Fn lookup" (library (program [main (invoke (call "other::reveal") [num 8])]) [secret, reveal])
#eval rejects "unreachable library Fn body" "E_TYPE" (library (program [main (num 0)])
  [fn "bad" [⟨"f", fnInt, {}⟩] int (block (call "f" [.boolean false {}]))])
#eval rejects "Fn signature scalar mismatch" "E_TYPE" (program [twice, main (call "twice" [var "natural", num 1]),
  fn "natural" [⟨"n", nat, {}⟩] nat (block (var "n"))])
#eval accepts "pure scalar branch remains symmetric" (program [main (call "int" [.branch (.boolean false {})
  (block (num 1)) (block (var "n")) {}]) [bind "n" (num 2) (some nat)]])
#eval rejects "invalid old dispatch envelope" "E_STAGE" { higherFixture with extended := true }
#eval check "executable pass never contains signature probes" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => checked.executable.lowered.staticUses.all fun use => match use.target.name with | .concrete _ => true | .probe _ => false)
#eval check "forged static signature and probe rejected" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => match checked.executable.lowered.staticUses.head? with
    | none => false
    | some use =>
        !validPass checked.prepared.input false { checked.executable.lowered with staticUses :=
          [{ use with expected := .data (.named "Int") }] } &&
        !validPass checked.prepared.input false { checked.executable.lowered with staticUses :=
          [{ use with target := { use.target with name := .probe 0 } }] })
#eval check "forged emitted call target rejected" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => match checked.executable.lowered.emittedCalls.head? with
    | none => false
    | some call => !validPass checked.prepared.input false { checked.executable.lowered with emittedCalls :=
        [{ call with id := checked.executable.lowered.origins.size }] })
#eval check "missing audit coverage rejected" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => !coversDefinitions checked.prepared.input { checked.audit.lowered with origins := #[] })
#eval check "tampered lifted owner rejected" (match Compiler.checkProgram higherFixture true with
  | .error _ => false
  | .ok checked => !validDefinitions higherFixture { checked.lifted with
      definitions := checked.lifted.definitions.modify 0 (fun definition =>
        { definition with owner := { definition.owner with name := "forged" } }) })

private def manyLambdas (count : Nat) : Program := program (main (num 0) :: (List.range count).map fun id =>
  fn s!"lambdaUser{id}" [] int (block (invoke (lambda (var "x")) [num 0])))
#eval accepts "specialization limit inclusive" (manyLambdas Limits.specializations)
#eval rejects "specialization limit exceeded" "E_LIMIT" (manyLambdas (Limits.specializations + 1))

/-- Dependency traversal has its own worklist budget, separate from each
function's body budget. All functions are real source definitions. -/
private def longChain (count : Nat) : Program := program (main (call "chain0") ::
  (List.range count).map fun id => fn s!"chain{id}" [] int (block
    (if id + 1 < count then call s!"chain{id + 1}" else num 7)))
#eval accepts "long ordinary dependency chain" (longChain 4200)

end VastitasKernel.Indexed.FunctionSource.Regression
