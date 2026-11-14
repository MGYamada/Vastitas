import VastitasKernel.ResourceProtocol
import VastitasKernel.IndexedSemantics
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Compiled reverse Core on the Stage 3 acceptance example (#623).

`tests/fixtures/reverse-example.wire.json` is the wire of
`examples/packages/smooth-differential`, with the checkout root written as
`/vastitas`; `tests/reverse_core.rs` keeps it current. The public protocol-9
checker accepts it. The Core evaluator then runs `main` on the executable
Core, whose reverse passes call the runtime reverse pass, and on the compiled
Core, which `emit` lowers. Both evaluate to 42, so each of the 25
observations agrees. This is an executable regression, not a proof. -/
namespace VastitasAlgebraTest.ReverseExampleRegression

open VastitasKernel VastitasKernel.Indexed.Core

private def json : Lean.Json :=
  (Lean.Json.parse (include_str "../../tests/fixtures/reverse-example.wire.json")).toOption.getD .null

private def check := RegressionSupport.check "reverse example regression failed"

/-- The value of `main` in a module. -/
private def mainValue (module : Module) : Option Semantics.Value := do
  let id ← module.main
  Semantics.eval module 1024 (fun _ => none) (.call id [] [] ⟨.pure .int, none⟩)

#eval do
  let .ok accepted := ResourceSource.Wire.check json true
    | throw (IO.userError "reverse example regression failed: the checker rejects the acceptance example")
  let checked := accepted.checked.pureProgram
  let source := checked.executable.core.module
  let compiled := checked.compiled.core.module
  check "the acceptance example compiles 22 reverse sites" (checked.compiled.entries.length == 22)
  check "four sites keep an opaque step" ((checked.compiled.entries.filter fun (entry : Reverse.Entry) =>
    entry.site.steps.any (·.kind == Reverse.StepKind.opaque)).length == 4)
  check "main evaluates to 42 on the executable Core, through the runtime reverse pass"
    (mainValue source == some (Semantics.Value.integer 42))
  check "main evaluates to 42 on the compiled Core" (mainValue compiled == some (Semantics.Value.integer 42))
  check "the compiled module validates against the executable Core"
    (Reverse.validate source checked.compiled.entries compiled)

end VastitasAlgebraTest.ReverseExampleRegression
