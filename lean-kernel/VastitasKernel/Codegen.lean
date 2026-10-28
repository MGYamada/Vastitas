import VastitasKernel.LegacyIndexed
import VastitasKernel.IndexedCodegen

/-! Compatibility entrypoint for annotation-only legacy certificates. Both
independent legacy audits and the declaration-driven Core audit are required.
All native term/type/primitive lowering is implemented by IndexedCodegen. -/
namespace VastitasKernel.Codegen

def generate (certified : CertifiedModule) : Except String String := do
  let module := certified.val
  -- Public callers may construct the legacy annotation certificate directly.
  -- Check the complete core contract at this boundary as well as in checkModule.
  unless Dependency.auditModule module do
    throw "checked IR failed dependency-order audit before code generation"
  unless Typing.auditModule module do
    throw "checked IR failed declarative typing audit before code generation"
  let some mainId := module.mainId
    | throw "native compilation requires fn main() -> Int"
  let some main := module.functions.find? (fun f => f.id == mainId)
    | throw "native entrypoint refers to a missing function"
  unless main.params.isEmpty && main.returnType == .int do
    throw "native entrypoint must have no parameters and return Int"
  let common ← (LegacyIndexed.module module).mapError Diagnostic.message
  let checked ← (Indexed.Core.Typing.checkModule common true).mapError Diagnostic.message
  Indexed.Core.Codegen.generate checked

end VastitasKernel.Codegen
