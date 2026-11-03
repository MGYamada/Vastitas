import VastitasKernel.IndexedProtocol
import VastitasKernel.IndexedCodegen

namespace VastitasKernel.Indexed.Wire

/-- Public acceptance retains the exact decoded JSON input and the exact result
of the combined authority/body checker, including both independently typed passes. -/
structure CheckedInput (json : Lean.Json) (requireMain : Bool) where
  source : DispatchSource.Program
  decoded : program json = .ok source
  checked : AuthoritySource.CheckedProgram source requireMain
  accepted : AuthoritySource.checkProgram source requireMain = .ok checked
  namespaceReceipt : Namespace.RequestReceipt source.source.headers.indexed json checked.namespaceUnits

def check (json : Lean.Json) (requireMain : Bool) : Except Diagnostic (CheckedInput json requireMain) :=
  match decoded : program json with
  | .error message => .error { code := "E_PROTOCOL", message }
  | .ok source =>
    match Namespace.checkRequest source.source.headers.indexed json
        (fun _ => AuthoritySource.checkProgram source requireMain) (·.namespaceUnits) with
    | .error diagnostic => .error diagnostic
    | .ok result => .ok ⟨source, decoded, result.value, result.accepted, result.receipt⟩

end VastitasKernel.Indexed.Wire
