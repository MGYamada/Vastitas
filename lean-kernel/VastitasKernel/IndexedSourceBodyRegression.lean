import VastitasKernel.IndexedSourceProgram
import VastitasKernel.IndexedSourceRegression
import VastitasKernel.IndexedCodegen

namespace VastitasKernel.Indexed.Source.BodyRegression
open Bodies

private def path (name : String) : Path := ⟨name.splitOn "::", {}⟩
private def arg (name : String) : TypeArgument := .name (path name)
private def int : Source.DataType := .pure .int
private def nat : Source.DataType := .pure .nat
private def object : Source.DataType := .object ⟨path "geo::Scheme", path "geo::QQ"⟩
private def point (name : String) : Source.DataType := .application (path "Point") [arg name, arg "geo::Base"]
private def packed : Source.DataType := .application (path "geo::Pointed") [arg "geo::Scheme", arg "geo::QQ"]
private def var (name : String) : Source.Expr := .variable name {}
private def num (value : Nat) : Source.Expr := .integer (toString value) {}
private def call (name : String) (arguments : List Source.Expr := []) : Source.Expr := .call (path name) arguments {}
private def block (result : Source.Expr) (statements : List Source.Stmt := []) : Source.Block := .mk statements result {}
private def fn (name : String) (params : List Source.Param) (result : Source.DataType) (body : Source.Block) : Source.Function :=
  ⟨name, params, result, body, true, {}⟩
private def bind (name : String) (value : Source.Expr) (annotation : Option Source.DataType := none) : Source.Stmt :=
  .letE name annotation value {}
private def program (functions : List Source.Function) : Source.Program :=
  let p := Regression.declarationFixture
  { p with packages := [{ p.packages[0]! with modules := [{ p.packages[0]!.modules[0]! with functions }] }, p.packages[1]!] }
private def main (body : Source.Expr) (statements : List Source.Stmt := []) : Source.Function := fn "main" [] int (block body statements)
private def make : Source.Function := fn "make" [⟨"n", nat, {}⟩] packed
  (block (.pack packed (var "X") [var "p"] {})
    [bind "X" (call "geo::Affine" [var "n"]), bind "p" (call "geo::origin" [var "X"])])
private def unwrap : Source.Function := fn "unwrap" [⟨"boxed", packed, {}⟩] int
  (block (call "int" [call "geo::dimension" [var "X"]]) [.unpack (var "boxed") "X" ["p"] {}])

/-- Actual unresolved source bodies, deliberately ordered before their callees. -/
def packageFixture : Source.Program := program [main (call "unwrap" [call "make" [num 2]]), unwrap, make]

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed source body regression failed: {name}")
private def accepts (p : Source.Program) (requireMain := true) : Bool := (Bodies.checkProgram p requireMain).isOk
private def rejects (code : String) (p : Source.Program) : Bool :=
  match Bodies.checkProgram p true with | .error error => error.code == code | .ok _ => false

#eval check "unresolved package bodies and forward calls" (accepts packageFixture)
#eval check "actual source bodies reach native codegen" (match Bodies.checkProgram packageFixture true with
  | .ok checked => (Core.Codegen.generate checked.core).isOk
  | .error _ => false)
#eval check "source ordering does not select a different function" (accepts (program [make, unwrap, main (call "unwrap" [call "make" [num 2]])]))
#eval check "empty library accepted but entrypoint required for build" (accepts (program []) false && !accepts (program []))
#eval check "entrypoint result" (rejects "E_MAIN" (program [fn "main" [] nat (block (num 0))]))
#eval check "unreachable body checked" (rejects "E_TYPE" (program [main (num 0), fn "bad" [] int (block (.boolean true {}))]))
#eval check "unsupported old body cannot be silently ignored" (rejects "E_STAGE" {
  packageFixture with packages := packageFixture.packages.map fun p =>
    { p with modules := p.modules.map fun m => { m with module := { m.module with functions := [make.namespaceHeader] } } } })
#eval check "unsupported abstract/edit envelopes rejected" (rejects "E_STAGE" { packageFixture with extended := true } &&
  rejects "E_STAGE" { packageFixture with extended := true, editable := true, authority := true })
#eval check "scalar equality cannot equate objects" (rejects "E_OPERATOR" (program [main
  (.block (block (num 0) [bind "equal" (.binary "==" (var "X") (var "X") {})]) {})
  [bind "X" (call "geo::Affine" [num 2])]]))
#eval check "scope escape through block" (rejects "E_ESCAPE" (program [main (num 0)
  [bind "p" (.block (block (call "geo::origin" [var "X"]) [bind "X" (call "geo::Affine" [num 2])]) {})]]))
#eval check "unknown call" (rejects "E_NAME" (program [main (call "absent")]))
#eval check "primitive cannot be selected by output type" (rejects "E_TYPE" (program [main (call "geo::Affine" [num 2])]))
#eval check "unknown variable in unused branch" (rejects "E_NAME" (program [main
  (.branch (.boolean true {}) (block (num 0)) (block (var "absent")) {})]))
#eval check "ordinary value cannot be called" (rejects "E_TYPE" (program [main (call "n") [bind "n" (num 3)]]))
#eval check "index family is not callable" (rejects "E_TYPE" (program [main (call "Point")]))
#eval check "source name collisions" (rejects "E_DUPLICATE" (program [main (num 0), main (num 1)]))
#eval check "parameter shadowing" (rejects "E_DUPLICATE" (program [main (num 0), fn "bad" [⟨"x", int, {}⟩] int
  (block (var "x") [bind "x" (num 2)])]))
#eval check "import cannot be shadowed" (rejects "E_SHADOW" (program [main (num 0) [bind "geo" (num 0)]]))
#eval check "forward parameter index rejected" (rejects "E_NAME" (program [main (num 0), fn "bad"
  [⟨"p", point "X", {}⟩, ⟨"X", object, {}⟩] int (block (num 0))]))
#eval check "dependent function call" (accepts (program [
  fn "keep" [⟨"X", object, {}⟩, ⟨"p", point "X", {}⟩] (point "X") (block (var "p")),
  main (call "int" [call "geo::dimension" [var "X"]]) [bind "X" (call "geo::Affine" [num 13]),
    bind "p" (call "keep" [var "X", call "geo::origin" [var "X"]])]]))
#eval check "equal dimensions do not identify call endpoints" (rejects "E_TYPE" (program [
  fn "keep" [⟨"X", object, {}⟩, ⟨"p", point "X", {}⟩] (point "X") (block (var "p")),
  main (num 0) [bind "X" (call "geo::Affine" [num 2]), bind "Y" (call "geo::Affine" [num 2]),
    bind "p" (call "keep" [var "X", call "geo::origin" [var "Y"]])]]))
#eval check "wrong package field count" (rejects "E_ENDPOINT" (program [main (num 0),
  fn "bad" [] packed (block (.pack packed (var "X") [] {}) [bind "X" (call "geo::Affine" [num 2])])]))
#eval check "package witness association" (rejects "E_ENDPOINT" (program [main (num 0),
  fn "bad" [] packed (block (.pack packed (var "X") [call "geo::origin" [var "Y"]] {})
    [bind "X" (call "geo::Affine" [num 2]), bind "Y" (call "geo::Affine" [num 2])])]))
#eval check "unpack field count" (rejects "E_ARITY" (program [make, main (num 0) [.unpack (call "make" [num 2]) "X" [] {}]]))
#eval check "unpack names must be distinct" (rejects "E_DUPLICATE" (program [make,
  main (num 0) [.unpack (call "make" [num 2]) "X" ["X"] {}]]))
#eval check "opening a package twice does not identify witnesses" (rejects "E_TYPE" (program [make,
  fn "keep" [⟨"X", object, {}⟩, ⟨"p", point "X", {}⟩] (point "X") (block (var "p")),
  main (num 0) [bind "boxed" (call "make" [num 2]), .unpack (var "boxed") "X" ["p"] {},
    .unpack (var "boxed") "Y" ["q"] {}, bind "bad" (call "keep" [var "X", var "q"])]]))
#eval check "direct and mutual recursion rejected" (rejects "E_RECURSION" (program [main (call "main")]) &&
  rejects "E_RECURSION" (program [main (call "bounce"), fn "bounce" [] int (block (call "main"))]))
#eval check "unreachable recursion rejected" (rejects "E_RECURSION" (program [main (num 0), fn "cycle" [] int (block (call "cycle"))]))
#eval check "literal inference is symmetric" (accepts (program [main (call "int" [.binary "+" (num 1) (var "n") {}])
  [bind "n" (num 2) (some nat)]]))
#eval check "Pair operands are inferred independently" (rejects "E_TYPE" (program [main (num 0)
  [bind "n" (num 2) (some nat), bind "p" (call "pair" [var "n", num 1])]]))
#eval check "explicit conversion only" (rejects "E_TYPE" (program [main (var "n") [bind "n" (num 2) (some nat)]]))
#eval check "malformed numeral" (rejects "E_LITERAL" (program [main (.integer "-1" {})]))

/-- Every scalar operation here originates in the unresolved source body. -/
def scalarFixture : Source.Program := program [main
  (.binary "+" (call "pair_first" [var "p"])
    (call "int" [.binary "-" (var "n") (num 9) {}]) {})
  [bind "n" (num 2) (some nat), bind "p" (call "pair"
    [.integer "999999999999999999999999999999999999999997" {}, num 0])]]

#eval check "source scalar and Pair native generation" (match Bodies.checkProgram scalarFixture true with
  | .ok checked => (Core.Codegen.generate checked.core).isOk
  | .error _ => false)

private def withLibrary (p : Source.Program) (change : Source.Module → Source.Module) : Source.Program :=
  { p with packages := [p.packages[0]!, { p.packages[1]! with modules := [change p.packages[1]!.modules[0]!] }] }
private def secret (isPublic : Bool) : Source.Function := { fn "secret" [] int (block (num 17)) with isPublic }
#eval check "private function cannot be called across packages" (rejects "E_VISIBILITY"
  (withLibrary (program [main (call "geo::secret")]) fun m => { m with functions := [secret false] }))
#eval check "dependency function resolved by canonical owner" (accepts
  (withLibrary (program [main (call "other::secret")]) fun m => { m with functions := [secret true] }))
#eval check "unreachable dependency function still checked" (rejects "E_NAME"
  (withLibrary (program [main (num 0)]) fun m => { m with functions := [fn "bad" [] int (block (var "absent"))] }))
#eval check "public function re-export" (accepts (withLibrary (program [main (call "geo::exported")]) fun m =>
  { m with functions := [secret true], module := { m.module with imports := [⟨["secret"], "exported", true, {}⟩] } }))
#eval check "private function re-export rejected" (rejects "E_VISIBILITY"
  (withLibrary (program [main (call "geo::exported")]) fun m =>
    { m with functions := [secret false], module := { m.module with imports := [⟨["secret"], "exported", true, {}⟩] } }))

private def keep : Source.Function := fn "keep" [⟨"X", object, {}⟩, ⟨"p", point "X", {}⟩] (point "X") (block (var "p"))
private def sameBranch (a b : String) : Source.Expr := .branch (.boolean true {}) (block (var a)) (block (var b)) {}
#eval check "branch of same object preserves identity" (accepts (program [keep, main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "p" (call "geo::origin" [var "X"]),
    bind "Y" (sameBranch "X" "X") (some object), bind "q" (call "keep" [var "Y", var "p"])]]))
#eval check "constant condition does not identify different objects" (rejects "E_TYPE" (program [keep, main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "Y" (call "geo::Affine" [num 2]),
    bind "Z" (sameBranch "X" "Y") (some object), bind "q" (call "keep" [var "Z", call "geo::origin" [var "X"]])]]))
#eval check "branch expected abstract object type" (accepts (program [main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "Y" (var "X") (some object),
    bind "Z" (sameBranch "X" "Y") (some object)]]))
private def identityObject : Source.Function := fn "identityObject" [⟨"X", object, {}⟩] object (block (var "X"))
#eval check "object-return calls introduce fresh nominal identities" (rejects "E_TYPE" (program [keep, identityObject, main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "Y" (call "identityObject" [var "X"]),
    bind "Z" (call "identityObject" [var "X"]), bind "q" (call "keep" [var "Y", call "geo::origin" [var "Z"]])]]))
#eval check "aliases preserve the exact object identity" (accepts (program [keep, main (num 0)
  [bind "X" (call "geo::Affine" [num 2]), bind "Y" (var "X"), bind "q" (call "keep" [var "Y", call "geo::origin" [var "X"]])]]))
private def token (witness : String) : Source.DataType := .application (path "geo::Token")
  [arg "geo::Scheme", arg "geo::QQ", .natural 3, arg witness]
#eval check "non-geometric dependent family uses the same body checker" (accepts (program [
  fn "keepToken" [⟨"X", object, {}⟩, ⟨"value", token "X", {}⟩] (token "X") (block (var "value")),
  fn "passToken" [⟨"Y", object, {}⟩, ⟨"value", token "Y", {}⟩] (token "Y")
    (block (call "keepToken" [var "Y", var "value"]))]) false)
#eval check "empty-runtime token index cannot escape unpack" (rejects "E_ESCAPE" (program [main (num 0),
  fn "escape" [⟨"boxed", .application (path "geo::Sealed") [arg "geo::Scheme", arg "geo::QQ"], {}⟩] int
    (block (num 0) [bind "bad" (.block (block (var "value") [.unpack (var "boxed") "X" ["value"] {}]) {})])]))

private def multiple (p : Source.Program) : Source.Program := withLibrary p fun m =>
  { m with declarations := m.declarations.map fun d => if d.name == "Pointed" then
    { d with body := .package [⟨⟨path "Scheme", path "QQ"⟩,
      [⟨path "Point", [.witness, .global (path "Base")]⟩, ⟨path "Morphism", [.witness, .witness]⟩]⟩] } else d }
private def makeMultiple : Source.Function := fn "make" [⟨"n", nat, {}⟩] packed
  (block (.pack packed (var "X") [call "geo::origin" [var "X"], call "geo::id" [var "X"]] {})
    [bind "X" (call "geo::Affine" [var "n"])])
private def repackMultiple : Source.Function := fn "repack" [⟨"boxed", packed, {}⟩] packed
  (block (.pack packed (var "X") [call "geo::apply" [var "m", var "p"], var "m"] {})
    [.unpack (var "boxed") "X" ["p", "m"] {}])
/-- Both differently represented fields originate in unresolved source bodies. -/
def multipleFixture : Source.Program := multiple (program [makeMultiple, repackMultiple, main
  (call "int" [call "geo::dimension" [var "X"]])
  [.unpack (call "repack" [call "make" [num 3]]) "X" ["p", "m"] {}, bind "q" (call "geo::apply" [var "m", var "p"])]] )
#eval check "multiple ordered fields and repacking" (accepts multipleFixture)
#eval check "swapped heterogeneous fields rejected" (rejects "E_ENDPOINT" (multiple (program [main (num 0),
  fn "bad" [] packed (block (.pack packed (var "X") [call "geo::id" [var "X"], call "geo::origin" [var "X"]] {})
    [bind "X" (call "geo::Affine" [num 3])])])) )

#eval check "source coverage rejects omissions and substituted owners" (match Bodies.checkProgram packageFixture true with
  | .error _ => false
  | .ok checked =>
      let module := checked.lowered.module
      let first := module.functions[0]!
      !validFunctionOrigins packageFixture { module with functions := module.functions.tail } &&
      !validFunctionOrigins packageFixture { module with functions :=
        { first with definition := { first.definition with name := "forged" } } :: module.functions.tail })
#eval check "duplicate body substitution fails independent Core uniqueness" (match Bodies.checkProgram packageFixture true with
  | .error _ => false
  | .ok checked =>
      let module := checked.lowered.module
      let repeated := { module with functions := List.replicate module.functions.length module.functions[0]! }
      validFunctionOrigins packageFixture repeated && !(Core.Typing.checkModule repeated false).isOk)
#eval check "forged call provenance rejected" (match Bodies.checkProgram packageFixture true with
  | .error _ => false
  | .ok checked => match checked.lowered.calls.head? with
    | none => false
    | some reference =>
        let forged := { reference with id := packageFixture.functions.length }
        !validCalls packageFixture.indexed { checked.lowered with calls := [forged] } &&
        !validCalls packageFixture.indexed { checked.lowered with calls := [{ reference with path := path "absent" }] })
#eval check "shared dependency is ordered once" (accepts (program [main (.binary "+" (call "leaf") (call "leaf") {}),
  fn "leaf" [] int (block (num 1))]))
#eval check "nested unary and Bool operators" (accepts (program [main
  (.branch (.unary "!" (.binary "&&" (.boolean true {}) (.boolean false {}) {}) {})
    (block (.unary "-" (num 3) {})) (block (num 0)) {})]))

end VastitasKernel.Indexed.Source.BodyRegression
