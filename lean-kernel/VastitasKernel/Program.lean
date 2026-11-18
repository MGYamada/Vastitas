import VastitasKernel.Core

namespace VastitasKernel

/-- Stage 1's public protocol leaves the proved Stage 0 raw core unchanged. -/
structure RawGenericParam where
  name : String
  span : Span
  deriving Repr, Inhabited

structure RawGeneric where
  name : String
  params : List RawGenericParam
  domain : List (List RawType)
  span : Span
  /-- An implicit family header gets its callable keys from its assembled methods.
  The explicit domain, including the empty one, keeps its declared meaning. -/
  inferDomain : Bool := false
  deriving Repr, Inhabited

structure RawMethod where
  name : String
  params : List RawParam
  returnType : RawType
  requirements : List String
  body : RawBlock
  span : Span
  deriving Repr, Inhabited

structure TypePath where
  path : List String
  span : Span
  deriving Repr, Inhabited, DecidableEq

def TypePath.name (path : TypePath) : String := String.intercalate "::" path.path

structure RawAbstractType where
  name : String
  parents : List TypePath
  span : Span
  deriving Repr, Inhabited

structure RawSubtype where
  scalar : String
  target : TypePath
  span : Span
  deriving Repr, Inhabited

structure RawAbstractMethod where
  name : String
  params : List RawParam
  returnType : RawType
  requirements : List String
  domain : List (List TypePath)
  span : Span
  deriving Repr, Inhabited

structure RawProgram where
  version : Nat
  file : String
  functions : List RawFunction
  generics : List RawGeneric
  methods : List RawMethod
  abstractTypes : List RawAbstractType := []
  subtypes : List RawSubtype := []
  abstractMethods : List RawAbstractMethod := []
  deriving Repr, Inhabited

end VastitasKernel
