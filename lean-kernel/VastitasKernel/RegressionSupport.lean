set_option autoImplicit false

/-! Helpers of the executable regressions (`*Regression.lean` and the test
libraries). Neither `Main` nor a compiler module imports this module, so the
executable and its build identity do not depend on it. -/
namespace VastitasKernel.RegressionSupport

/-- Fail the `#eval` of a regression unless `ok` holds. The error reads
`<suite>: <label>`, where each regression passes its own `suite` text. -/
def check (suite label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"{suite}: {label}")

end VastitasKernel.RegressionSupport
