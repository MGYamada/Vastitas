import VastitasKernel.NamespaceChecker

namespace VastitasKernel.Namespace

/-- Presentation only. Failed namespace lowering retains its original source
diagnostic; a surface/core failure uses the same validated declaration table.
This is outside the semantic acceptance path and changes no returned spans. -/
def describeDiagnostic (p : Program) (lowered : Lowered) (diagnostic : Diagnostic) : Diagnostic := Id.run do
  let headers := Surface.headers lowered.surface
  let names := p.declarations.foldl (fun (table : Std.HashMap String String) target =>
    if symbol p target == "main" then table else table.insert (symbol p target)
      (String.intercalate "::" (target.owner.scope.package.name :: target.owner.scope.path ++ [target.owner.name]))) {}
  let render (token : String) :=
    if let some name := names[token]? then name
    else if token.startsWith "ns_b_" then (token.drop 5).toString else token
  let rewrite (message : String) := Id.run do
    let message := (DispatchChecker.describeDiagnostic headers { diagnostic with message, notes := [] }).message
    let mut output := ""
    let mut token := ""
    for char in message.toList do
      if char.isAlphanum || char == '_' then token := token.push char
      else
        output := (output ++ render token).push char
        token := ""
    return output ++ render token
  return { diagnostic with
    message := rewrite diagnostic.message
    notes := diagnostic.notes.map fun note => { note with message := rewrite note.message } }

end VastitasKernel.Namespace
