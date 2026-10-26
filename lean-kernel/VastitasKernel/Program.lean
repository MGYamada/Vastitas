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
  deriving Repr, Inhabited

structure RawMethod where
  name : String
  params : List RawParam
  returnType : RawType
  requirements : List String
  body : RawBlock
  span : Span
  deriving Repr, Inhabited

structure RawProgram where
  version : Nat
  file : String
  functions : List RawFunction
  generics : List RawGeneric
  methods : List RawMethod
  deriving Repr, Inhabited

end VastitasKernel
