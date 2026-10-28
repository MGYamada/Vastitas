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

def FunctionName.isLambda : FunctionName → Bool
  | .lambda _ => true
  | _ => false

/-- Audit probes cannot alias executable definitions, even if their printed
names would have matched. Each pass allocates its own probe identities. -/
inductive TargetName where
  | concrete (function : FunctionName)
  | probe (id : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Inhabited

def TargetName.isProbe : TargetName → Bool
  | .probe _ => true
  | _ => false

structure InstanceKey where
  function : FunctionName
  arguments : List TargetName
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Inhabited

inductive EmittedName where
  | original (function : FunctionName)
  | specialized (id : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Inhabited

def EmittedName.render : EmittedName → String
  | .original name => name.render
  | .specialized id => s!"__vastitas_h{id}"

end VastitasKernel
