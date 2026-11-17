import VastitasKernel.Core
import VastitasKernel.Checker
import VastitasKernel.Runtime
import VastitasKernel.Graph

/-! Root module of the `VastitasKernel` library target. No module imports it,
and CI builds it explicitly. It imports the old Core checker (`Core`,
`Checker`), its runtime model `Runtime` and the internal `Graph` fragment.
`Main`'s import closure contains none of `Checker`, `Runtime` and `Graph`. -/
