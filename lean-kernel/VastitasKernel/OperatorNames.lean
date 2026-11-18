import VastitasKernel.FunctionId

namespace VastitasKernel.Namespace

/-- The public wire cannot supply a package with this reserved source. The
closed exact families have no externally editable methods. -/
def operatorScope : Scope := ⟨⟨"vastitas:compat:operators", "std", "2026.0.0"⟩, ["operator"]⟩

def operatorName (name : String) : Bool := ["add", "sub", "neg", "mul", "div"].contains name

def operatorShort? : List String → Option String
  | [name] => if operatorName name then some name else none
  | _ => none

def operatorId (name : String) : FunctionId := ⟨⟨operatorScope, name⟩⟩

end VastitasKernel.Namespace
