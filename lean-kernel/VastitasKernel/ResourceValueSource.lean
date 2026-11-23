import VastitasKernel.MethodBodyText
import VastitasKernel.ResourceHeaderSource
import VastitasKernel.ResourceViewSource
import VastitasKernel.ResourceTensorSource

set_option autoImplicit false

/-! Physical source for pure values inside resource functions, their result
blocks and calls that pass or return resource names. -/
namespace VastitasKernel.ResourceValueSource
open AssemblyText ResourceSource ResourceStatementSource SourceText Indexed

inductive ValueSite where
  | signature (header : ResourceHeaderSource.Signature)
  | view (operation : ResourceViewSource.View)
  | tensor (op : Storage.Tensor.Operation String)
  | network (graph : Storage.TensorNetwork.Graph String) (output : String)
  | tree (graph : Storage.TensorTree.Graph String) (output : String) (plan : List (Storage.TensorTree.PlanStep String Action))
  | guard (condition : ResourceCondition) (yesLength noLength : Nat)
  | binding (name : String) (type : Core.PureType) (body : FunctionSource.Block)
  | call (binding : Option (String × Core.PureType)) (callee : List String) (arguments results : List String)
  | result (body : FunctionSource.Block) (functionEnd : Nat)

private def select : Statement → Option (ValueSite × Span)
  | .branch b yes no s => some (.guard (.literal b) yes.length no.length, s)
  | .branchValue n yes no s => some (.guard (.binding n) yes.length no.length, s)
  | .value name type body s => some (.binding name type body, s)
  | .callValue path args outs name type s => some (.call (some (name,type)) path.path args outs, s)
  | .call path args outs s => some (.call none path.path args outs, s)
  | .tensor op s => some (.tensor op, s)
  | .network g out .nativeFast s => some (.network g out, s)
  | .tree g out .nativeFast plan s => some (.tree g out plan, s)
  | stmt => (ResourceViewSource.select stmt).map fun (op, span) => (.view op, span)

private def boundaries (fn : Function) : List (Nat × ValueSite × Span) :=
  let .mk _ _ span := fn.valueBody
  [(0, .signature ⟨fn.name, fn.parameters, fn.results, fn.valueType⟩, fn.span),
   (fn.body.length, .result fn.valueBody fn.span.end, span)]

private def annotation (name : String) (type : Core.PureType) : Parser Unit := do
  token (.ident "let")
  token (.ident name)
  token (.punctuation ':')
  tokens (pureTypeTokens type)
  token (.punctuation '=')

private def block (file : File) (before : Cursor) (body : FunctionSource.Block) (span : Span) :
    Except Diagnostic Token := do
  let opening ← (file.next before).mapError (diagnostic span)
  (MethodBodyText.check file opening.span body).mapError fun err =>
    {err with code := "E_RESOURCE_SOURCE"}

private def names (xs : List String) : Parser Unit := do
  token (.punctuation '(')
  for field in listLexemes (xs.map fun name => [.ident name]) ')' do token field

def replay (file : File) (site : ResourceStatementSite) (v : ValueSite) (span : Span) : Except Diagnostic Token := do
  let before := site.before
  match v with
  | .signature header => runGroup (ResourceHeaderSource.header header) file site
  | .view op => runStatement (ResourceViewSource.spelling op) file before span
  | .tensor op => runStatement (ResourceTensorSource.operation op) file before span
  | .network g output => runTerminated '}' (ResourceTensorSource.network g output) file before span
  | .tree g output plan => runTerminated '}' (ResourceTensorSource.tree g output plan) file before span
  | .guard cond yesLength noLength =>
    unless site.branchLengths == some (yesLength, noLength) do
      throw (diagnostic span "the number of statements in a resource branch differs from its source")
    runGroup (do
      token (.ident "if")
      consume fun f c => do
        let guard ← f.next c
        let .word name := guard.kind | throw "expected a resource branch condition"
        unless ResourceCondition.ofWord name == cond do throw "resource branch condition differs from the source"
        return guard.after
      token (.punctuation '{')) file site
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

abbrev items := ResourceStatementSource.itemsWithBoundaries select boundaries
abbrev Corresponds := ResourceStatementSource.Corresponds replay
abbrev check := ResourceStatementSource.check replay

end VastitasKernel.ResourceValueSource
