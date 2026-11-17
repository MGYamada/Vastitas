import VastitasKernel.Dispatch

namespace VastitasKernel

/-- Internal identities are structural. Strings are used only for source names
and when serializing names into the preserved core. -/
inductive FunctionName where
  | source (name : String)
  | lambda (id : Nat)
  | method (id : Nat) (key : Dispatch.Key)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Inhabited

def FunctionName.render : FunctionName → String
  | .source name => name
  | .lambda id => s!"__vastitas_l{id}"
  | .method id key => s!"__vastitas_m{id}_" ++ String.intercalate "_" (key.map toString)

end VastitasKernel
