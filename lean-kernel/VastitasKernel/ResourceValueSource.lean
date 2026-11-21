import VastitasKernel.MethodBodyText
import VastitasKernel.ResourceStatementSource

set_option autoImplicit false

/-! Physical source for pure values inside resource functions, their result
blocks and calls that pass or return resource names. -/
namespace VastitasKernel.ResourceValueSource
open AssemblyText ResourceSource ResourceStatementSource SourceText Indexed

inductive ValueSite where
  | binding (name : String) (type : Core.PureType) (body : FunctionSource.Block)
  | call (binding : Option (String × Core.PureType)) (callee : List String) (arguments results : List String)
  | result (body : FunctionSource.Block) (functionEnd : Nat)

private def select : Statement → Option (ValueSite × Span)
  | .value name type body s => some (.binding name type body, s)
  | .callValue path args outs name type s => some (.call (some (name,type)) path.path args outs, s)
  | .call path args outs s => some (.call none path.path args outs, s)
  | _ => none

private def finalResult (fn : Function) : Option (ValueSite × Span) :=
  let .mk _ _ span := fn.valueBody
  some (.result fn.valueBody fn.span.end, span)

private def annotation (name : String) (type : Core.PureType) : Parser Unit := do
  token (.ident "let")
  token (.ident name)
  token (.punctuation ':')
  match type with
  | .unit => token (.ident "Unit")
  | .nat => token (.ident "Nat")
  | .int => token (.ident "Int")
  | .bool => token (.ident "Bool")
  | .pair elem =>
    token (.ident "Pair")
    token (.punctuation '<')
    token (.ident (match elem with | .nat => "Nat" | .int => "Int"))
    token (.punctuation '>')
  token (.punctuation '=')

private def block (file : File) (before : Cursor) (body : FunctionSource.Block) (span : Span) :
    Except Diagnostic Token := do
  let opening ← (file.next before).mapError (diagnostic span)
  (MethodBodyText.check file opening.span body).mapError fun err =>
    {err with code := "E_RESOURCE_SOURCE"}

private def names (xs : List String) : Parser Unit := do
  token (.punctuation '(')
  for field in listLexemes (xs.map fun name => [.ident name]) ')' do token field

def replay (file : File) (before : Cursor) (v : ValueSite) (span : Span) : Except Diagnostic Token := do
  match v with
  | .result body functionEnd =>
    let last ← block file before body span
    let close ← (file.next last.after).mapError (diagnostic last.span)
    unless (close.kind matches .symbol '}') && close.span.end == functionEnd do
      throw (diagnostic close.span "resource result has a different function extent")
    return last
  | .binding name type body =>
    runStatement (do
      annotation name type
      token (.ident "value")
      let c ← get
      match block file c body span with
      | .ok last => set last.after
      | .error err => throw err) file before span
  | .call binding callee arguments results =>
    runStatement (do
      if let some (name,type) := binding then annotation name type
      token (.ident "call")
      for field in pathLexemes callee do token field
      names arguments
      token .arrow
      names results) file before span

abbrev items := ResourceStatementSource.itemsWithResult select finalResult
abbrev Corresponds := ResourceStatementSource.Corresponds replay
abbrev check := ResourceStatementSource.check replay

end VastitasKernel.ResourceValueSource
