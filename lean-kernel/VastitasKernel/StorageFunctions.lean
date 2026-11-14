import VastitasKernel.StorageFunctionSyntax
import VastitasKernel.StorageFunctionReceipts
import VastitasKernel.StorageFunctionContext
import VastitasKernel.StorageFunctionOperations
import VastitasKernel.StorageFunctionNumerical
import VastitasKernel.StorageFunctionCalls
import VastitasKernel.StorageFunctionExpansion
import VastitasKernel.StorageFunctionChecks

/-! Internal affine resource functions. Calls consume owned arguments, create
bounded child loans for borrowed arguments, return those loans, and transfer
owned results. Every actual call is expanded and rechecked against its caller's
real resources. Synthetic all-body probes never become executable schedules.
This component is not public protocol 8 or a replacement for namespace/Fn/edit
acceptance. Dimensions in this first function component are static metadata.

The parts follow the stages of checking: syntax and headers, receipts, the
checking context, operations, numerical operations, the call boundary,
expansion, and the probe, library and entry checks. -/
