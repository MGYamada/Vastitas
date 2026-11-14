import VastitasKernel.Core
import VastitasKernel.Checker
import VastitasKernel.FunctionChecker
import VastitasKernel.Runtime
import VastitasKernel.Graph

/-! Root module of the `VastitasKernel` library target; no module imports it.
It imports the old Core and Surface checker modules (`Core`, `Checker`,
`FunctionChecker`), their runtime model `Runtime` and the internal `Graph`
fragment. `Main`'s import closure contains neither `Runtime` nor `Graph`. CI
builds this root together with the executable and test-library roots, so that
the axiom audit finds every kernel module built. -/
