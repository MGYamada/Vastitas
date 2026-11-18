import VastitasKernel.Indexed

namespace VastitasKernel.Indexed.FunctionSource

/-- A static substitution uses nominal category identities even when two instances
share the very same graph or when object tags have the same spelling. -/
inductive StaticIndex where
  | category (owner : DeclId)
  | monad (owner : DeclId)
  | object (category : DeclId) (tag : String)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

end VastitasKernel.Indexed.FunctionSource
