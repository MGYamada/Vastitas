import VastitasKernel.Identity

namespace VastitasKernel.Namespace

/-- A named function, independent of how many methods it has or which scope
currently holds edit authority. Neither import aliases nor emitted Core indices
participate in this identity. -/
structure FunctionId where
  owner : Owner
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

end VastitasKernel.Namespace
