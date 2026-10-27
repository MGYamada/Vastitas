import VastitasKernel.SurfaceProtocol
import VastitasKernel.FunctionChecker
import VastitasKernel.Semantics
import Lean.Elab.Term

/-! Fixed frontend fixture for the stdlib's numerical contracts. Rust CI checks
this exact JSON against the canonical .vast sources. This is not a proof of
the Rust parser or a general source-level operational correspondence theorem. -/
namespace VastitasKernel.PromotionFixture

open Lean Elab Term in
/-- Reify the actual decoder's fixed input as a transparent kernel term.
JSON parsing is run during elaboration, not assumed as a semantic axiom. -/
elab "stdlib_fixture% " path:str : term => do
  let file := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let source ← IO.FS.readFile (file.parent.getD "." / path.getString)
  let .ok json := Lean.Json.parse source | throwError "invalid stdlib JSON fixture"
  let .ok program := decodeSurfaceModule json | throwError "invalid stdlib surface fixture"
  -- Derived Repr prints Span.end without escaping this Lean keyword.
  let printed := (reprStr program).replace " end :=" " «end» :="
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term printed with
    | .ok stx => pure stx
    | .error message => throwError "cannot reify stdlib fixture: {message}\n{printed.take 500}"
  elabTerm stx (some (mkConst ``Surface.Program))

def raw : Surface.Program := stdlib_fixture% "../../tests/fixtures/promotion.json"

#eval show IO Unit from do
  let source := include_str "../../tests/fixtures/promotion.json"
  let .ok json := Lean.Json.parse source | throw (IO.userError "invalid fixture JSON")
  let .ok decoded := decodeSurfaceModule json | throw (IO.userError "invalid fixture IR")
  unless reprStr decoded == reprStr raw do
    throw (IO.userError "stdlib reification changed the decoded input")
def acceptance : Except Diagnostic CertifiedModule := checkSurfaceProgram raw

open Lean Elab Term in
/-- Reflect the exact output of the actual checker, not a handwritten model.
The kernel subsequently checks proofs about this ordinary CheckedModule term.
Concrete frontend/decoder/checker agreement is also checked below at build time;
general public-checker soundness remains the oracle's acceptance theorem. -/
elab "stdlib_checked% " path:str : term => do
  let file := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let source ← IO.FS.readFile (file.parent.getD "." / path.getString)
  let .ok json := Lean.Json.parse source | throwError "invalid stdlib JSON fixture"
  let .ok program := decodeSurfaceModule json | throwError "invalid stdlib surface fixture"
  let .ok certified := checkSurfaceProgram program | throwError "stdlib fixture was rejected"
  let printed := (reprStr certified.val).replace " end :=" " «end» :="
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `term printed with
    | .ok stx => pure stx
    | .error message => throwError "cannot reify checked stdlib: {message}"
  elabTerm stx (some (mkConst ``CheckedModule))

def checked : CheckedModule := stdlib_checked% "../../tests/fixtures/promotion.json"

#eval show IO Unit from do
  let .ok certified := acceptance | throw (IO.userError "stdlib fixture rejected")
  unless reprStr certified.val == reprStr checked do
    throw (IO.userError "checked stdlib reification differs from actual acceptance")

def function (name : String) : CheckedFunction :=
  (checked.functions.find? (·.name == name)).getD default

end VastitasKernel.PromotionFixture
