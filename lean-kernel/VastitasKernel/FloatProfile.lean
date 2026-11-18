import VastitasKernel.IndexedDispatchSource
import VastitasKernel.FloatNames

namespace VastitasKernel.Indexed.FloatProfile

private def modl (path : List String) (operations : List String) : DispatchSource.Module :=
  { module := { path, isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {},
                resourceFunctions := operations.map fun name => ⟨name, true, {}⟩ }, declarations := [] }

/-- These headers have no executable source body. Resource lowering checks
each resolved operation against this owner and its realization signature. -/
def package : DispatchSource.Package :=
  { id := Namespace.floatScope.package, dependencies := [], modules := [
    modl [] [], modl ["float"] ["realize", "interpret", "point", "run"]] }

end VastitasKernel.Indexed.FloatProfile
