import VastitasKernel.Core
import VastitasKernel.Checker
import VastitasKernel.Runtime
import VastitasKernel.Graph
import VastitasKernel.ComplexDivision

/-! Root module of the `VastitasKernel` library target. No module imports it,
and CI builds it explicitly. It imports the old Core checker (`Core`,
`Checker`), its runtime model `Runtime`, the internal `Graph` fragment and
`ComplexDivision`, which proves signed-zero results for the scalar reference
graph of #855. `Main` imports none of `Checker`, `Runtime`, `Graph` and
`ComplexDivision`, directly or transitively. -/
