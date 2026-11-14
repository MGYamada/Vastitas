import VastitasKernel.Core
import VastitasKernel.Checker
import VastitasKernel.FunctionChecker
import VastitasKernel.SurfacePrograms
import VastitasKernel.Runtime
import VastitasKernel.Graph

/-! Root module of the `VastitasKernel` library target. No module imports it,
and CI builds it explicitly. It imports the old Core and Surface checker
modules (`Core`, `Checker`, `FunctionChecker`), the namespace, edit and
authority checkers over them (`SurfacePrograms`), their runtime model `Runtime`
and the internal `Graph` fragment. `Main`'s import closure contains none of
`Checker`, `FunctionChecker`, `SurfacePrograms`, `Runtime` and `Graph`. -/
