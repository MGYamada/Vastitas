import Std

/-! Canonical package/module/declaration identity, shared by scalar namespaces
and the indexed declaration environment. Files and import aliases are not IDs. -/
namespace VastitasKernel.Namespace

structure PackageId where
  source : String
  name : String
  version : String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Scope where
  package : PackageId
  path : List String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Owner where
  scope : Scope
  name : String
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

end VastitasKernel.Namespace
