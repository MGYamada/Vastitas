import VastitasKernel.ResourceStatementSource
import VastitasKernel.ResourceLiteralText

set_option autoImplicit false

/-! Physical operand and coefficient replay for static/runtime GEMM and the
dual and Hermitian evaluation calls that share its optional-coefficient syntax. -/
namespace VastitasKernel.ResourceProductSource
open AssemblyText ResourceSource SourceText ResourceStatementSource

inductive Kind where
  | gemm | runtimeGemm | dual | hermitian (metric : String)

structure Product where
  kind : Kind
  left : String
  right : String
  output : String
  mode : Storage.GemmMode
  alpha : Option Coefficient
  beta : Option Coefficient

def product? : Statement → Option (Product × Span)
  | .numerical (.gemm l r o m .nativeFast a b) s => some (⟨.gemm,l,r,o,m,a,b⟩,s)
  | .runtimeNumerical (.gemm l r o m .nativeFast a b) s => some (⟨.runtimeGemm,l,r,o,m,a,b⟩,s)
  | .numerical (.evaluate l r o k m .nativeFast a b) s =>
    let kind := match k with | .dual => Kind.dual | .hermitian metric => .hermitian metric
    some (⟨kind,l,r,o,m,a,b⟩,s)
  | _ => none

private def next : Parser Token := do
  let f ← read
  match f.next (← get) with
  | .ok t => pure t
  | .error msg => throw (diagnostic {} msg)

private def coefficient : Coefficient → Parser Unit
  | .literal v => consume fun f p => ResourceLiteralText.check f p v
  | .loan name => do
    token (.ident "coefficient")
    token (.punctuation '(')
    token (.ident name)
    token (.punctuation ')')

/-- The frontend accepts either written order. Consume each expected coefficient
once, including its name and whether it reads a loan or provides literal bits. -/
private def coefficients (alpha beta : Option Coefficient) : Parser Unit := do
  let mut a := alpha
  let mut b := beta
  for _ in [:2] do
    unless (← next).kind matches .symbol ',' do break
    token (.punctuation ',')
    let t ← next
    let (value, isAlpha) ← match t.kind with
      | .word "alpha" => pure (a, true)
      | .word "beta" => pure (b, false)
      | _ => throw (diagnostic t.span "expected alpha or beta in numerical product")
    let some v := value | throw (diagnostic t.span "extra or repeated coefficient in numerical product")
    set t.after
    token (.punctuation '=')
    coefficient v
    if isAlpha then a := none else b := none
  unless a.isNone && b.isNone do throw (diagnostic (← next).span "product coefficient missing in physical source")

def replay : Replay Product := fun f site product span => do
  let parser : Parser Unit := do
    token (.ident (match product.kind with
      | .gemm => "gemm" | .runtimeGemm => "runtime_gemm" | .dual => "evaluate" | .hermitian _ => "hermitian"))
    token (.punctuation '(')
    for name in [product.left, product.right, product.output] do
      token (.ident name)
      token (.punctuation ',')
    if let .hermitian metric := product.kind then
      token (.ident metric)
      token (.punctuation ',')
    token (.ident (match product.mode with | .overwrite => "overwrite" | .accumulate => "accumulate"))
    token (.punctuation ',')
    token (.ident "NativeFast")
    coefficients product.alpha product.beta
    token (.punctuation ')')
  runStatement parser f site.before span

abbrev items := ResourceStatementSource.items product?
abbrev Corresponds := ResourceStatementSource.Corresponds replay
abbrev check := ResourceStatementSource.check replay

end VastitasKernel.ResourceProductSource
