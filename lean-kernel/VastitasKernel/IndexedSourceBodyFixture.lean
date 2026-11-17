import VastitasKernel.IndexedSourceRegression

/-! Data-function source programs of the executable regressions and the
standalone native fixtures (`scripts/check_indexed_codegen.lean`). Neither
`Main` nor a compiler module imports this module. The programs are unresolved
source bodies over `Source.Regression.declarationFixture`; the helpers that
build them are shared with `IndexedSourceBodyRegression`. -/
namespace VastitasKernel.Indexed.Source.BodyFixture

def path (name : String) : Path := ⟨name.splitOn "::", {}⟩
def arg (name : String) : TypeArgument := .name (path name)
def int : Source.DataType := .pure .int
def nat : Source.DataType := .pure .nat
def object : Source.DataType := .object ⟨path "geo::Scheme", path "geo::QQ"⟩
def point (name : String) : Source.DataType := .application (path "Point") [arg name, arg "geo::Base"]
def packed : Source.DataType := .application (path "geo::Pointed") [arg "geo::Scheme", arg "geo::QQ"]
def var (name : String) : Source.Expr := .variable name {}
def num (value : Nat) : Source.Expr := .integer (toString value) {}
def call (name : String) (arguments : List Source.Expr := []) : Source.Expr := .call (path name) arguments {}
def block (result : Source.Expr) (statements : List Source.Stmt := []) : Source.Block := .mk statements result {}
def fn (name : String) (params : List Source.Param) (result : Source.DataType) (body : Source.Block) : Source.Function :=
  ⟨name, params, result, body, true, {}⟩
def bind (name : String) (value : Source.Expr) (annotation : Option Source.DataType := none) : Source.Stmt :=
  .letE name annotation value {}
/-- The functions in the root module of the declaration fixture. -/
def program (functions : List Source.Function) : Source.Program :=
  let p := Regression.declarationFixture
  { p with packages := [{ p.packages[0]! with modules := [{ p.packages[0]!.modules[0]! with functions }] }, p.packages[1]!] }
def main (body : Source.Expr) (statements : List Source.Stmt := []) : Source.Function := fn "main" [] int (block body statements)
def make : Source.Function := fn "make" [⟨"n", nat, {}⟩] packed
  (block (.pack packed (var "X") [var "p"] {})
    [bind "X" (call "geo::Affine" [var "n"]), bind "p" (call "geo::origin" [var "X"])])
def unwrap : Source.Function := fn "unwrap" [⟨"boxed", packed, {}⟩] int
  (block (call "int" [call "geo::dimension" [var "X"]]) [.unpack (var "boxed") "X" ["p"] {}])

/-- Actual unresolved source bodies, deliberately ordered before their callees. -/
def packageFixture : Source.Program := program [main (call "unwrap" [call "make" [num 2]]), unwrap, make]

/-- Every scalar operation here originates in the unresolved source body. -/
def scalarFixture : Source.Program := program [main
  (.binary "+" (call "pair_first" [var "p"])
    (call "int" [.binary "-" (var "n") (num 9) {}]) {})
  [bind "n" (num 2) (some nat), bind "p" (call "pair"
    [.integer "999999999999999999999999999999999999999997" {}, num 0])]]

/-- The program with the library module changed by `change`. -/
def withLibrary (p : Source.Program) (change : Source.Module → Source.Module) : Source.Program :=
  { p with packages := [p.packages[0]!, { p.packages[1]! with modules := [change p.packages[1]!.modules[0]!] }] }

/-- The program whose package `Pointed` has two differently represented fields. -/
def multiple (p : Source.Program) : Source.Program := withLibrary p fun m =>
  { m with declarations := m.declarations.map fun d => if d.name == "Pointed" then
    { d with body := .package [⟨⟨path "Scheme", path "QQ"⟩,
      [⟨path "Point", [.witness, .global (path "Base")]⟩, ⟨path "Morphism", [.witness, .witness]⟩]⟩] } else d }
def makeMultiple : Source.Function := fn "make" [⟨"n", nat, {}⟩] packed
  (block (.pack packed (var "X") [call "geo::origin" [var "X"], call "geo::id" [var "X"]] {})
    [bind "X" (call "geo::Affine" [var "n"])])
def repackMultiple : Source.Function := fn "repack" [⟨"boxed", packed, {}⟩] packed
  (block (.pack packed (var "X") [call "geo::apply" [var "m", var "p"], var "m"] {})
    [.unpack (var "boxed") "X" ["p", "m"] {}])
/-- Both differently represented fields originate in unresolved source bodies. -/
def multipleFixture : Source.Program := multiple (program [makeMultiple, repackMultiple, main
  (call "int" [call "geo::dimension" [var "X"]])
  [.unpack (call "repack" [call "make" [num 3]]) "X" ["p", "m"] {}, bind "q" (call "geo::apply" [var "m", var "p"])]] )

end VastitasKernel.Indexed.Source.BodyFixture
