import VastitasKernel.Identity

namespace VastitasKernel.Namespace

/-- A kernel-owned module. The public envelope rejects this package source
among user packages, roots and dependency targets. -/
def floatScope : Scope := ⟨⟨"vastitas:compat:float", "monad", "2026.0.0"⟩, ["float"]⟩

end VastitasKernel.Namespace
