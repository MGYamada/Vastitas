import VastitasKernel.FunctionChecker
import VastitasKernel.Codegen

namespace VastitasKernel.PairRegression

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Pair regression failed: {name}")

private def pair (element : PairElem) (left right : Term) (result : Ty) : Term :=
  .builtin (.pair element) [left, right] ⟨result, none⟩
private def module (body : Term) : CheckedModule := {
  functions := [{ id := 0, name := "main", params := [], returnType := body.ty, body, span := {} }]
  mainId := some 0 }
private def rejected (body : Term) : Bool :=
  !Typing.auditModule (module body) && match certifyModule (module body) with
    | .error _ => false
    | .ok certified => !(Codegen.generate certified).isOk

private def integers : Term := pair .int (.literal .int 20) (.literal .int 22) (.pair .int)
private def naturals : Term := pair .nat (.literal .nat 20) (.literal .nat 22) (.pair .nat)
#eval check "valid construction" (Typing.auditModule (module integers) && Typing.auditModule (module naturals))
#eval check "heterogeneous operands" (rejected (pair .int (.literal .nat 20) (.literal .int 22) (.pair .int)))
#eval check "forged constructor result" (rejected (pair .int (.literal .int 20) (.literal .int 22) (.pair .nat)))
#eval check "forged projection result" (rejected (.builtin (.pairFirst .int) [integers] ⟨.nat, none⟩))
#eval check "forged projection element" (rejected (.builtin (.pairSecond .nat) [integers] ⟨.nat, none⟩))
#eval check "wrong projection argument" (rejected (.builtin (.pairFirst .int) [.literal .int 1] ⟨.int, none⟩))
#eval check "constructor arity" (rejected (.builtin (.pair .int) [.literal .int 1] ⟨.pair .int, none⟩))
#eval check "no fabricated object identity" (rejected (.builtin (.pair .int)
  [.literal .int 20, .literal .int 22] ⟨.pair .int, some (.local .qq 3)⟩))
#eval check "forged Pair call" (!Typing.auditModule {
  functions := (module integers).functions ++ [{
    id := 1, name := "caller", params := [],
    returnType := .pair .nat, body := .call 0 [] [] ⟨.pair .nat, none⟩, span := {} }]
  mainId := none })

end VastitasKernel.PairRegression
