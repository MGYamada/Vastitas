import VastitasKernel.LegacyIndexed
import VastitasKernel.Codegen

namespace VastitasKernel.LegacyIndexedRegression

private def object (base : BaseKind) (serial : Nat) : ResultType :=
  ⟨.object base, some (.local base serial)⟩
private def point : ResultType := ⟨.point (.local .qq 1) (.base .qq), none⟩
private def affine (base : BaseKind) (serial : Nat) : Term :=
  .builtin (.affine base) [.literal .nat 42] (object base serial)
private def make : CheckedFunction := {
  id := 0, name := "legacy-maker", params := [], returnType := .pointed .qq
  body := .letE 20 (affine .qq 1) (.pack .qq (.var 20 (object .qq 1))
    (.builtin .origin [.var 20 (object .qq 1)] point)) }
private def main : CheckedFunction := {
  id := 1, name := "main", params := [], returnType := .int
  body := .unpack 3 4 (.call 0 [] [] ⟨.pointed .qq, none⟩)
    (.builtin .int [.builtin .dimension [.var 3 (object .qq 3)] ⟨.nat, none⟩] ⟨.int, none⟩) }
private def program : CheckedModule := ⟨[make, main], some 1⟩
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"legacy indexed regression failed: {name}")

#eval check "compatibility profile independently validates"
  (Indexed.Core.validDeclarations LegacyIndexed.declarations)
#eval check "legacy package term reaches the common checker" (LegacyIndexed.check program true).isOk
#eval check "native code imports only the common runtime" (match certifyModule program with
  | .error _ => false
  | .ok legacy => match Codegen.generate legacy with
    | .error _ => false
    | .ok code => code.startsWith "import VastitasKernel.IndexedRuntime\n")
#eval check "old annotation certificate cannot bypass a missing variable" (!(LegacyIndexed.check
  { program with functions := [make, { main with body := .var 500 ⟨.int, none⟩ }] } true).isOk)
#eval check "retagged existential field is rejected" (!(LegacyIndexed.check
  { program with functions := [{ make with body := (.letE 20 (affine .qq 1)
    (.pack .qq (.var 20 (object .qq 1)) (.builtin .origin [.var 20 (object .qq 1)]
      ⟨.point (.local .qq 8) (.base .qq), none⟩))) }, main] } true).isOk)
#eval check "converted Core still rejects a corrupted declaration environment"
  (match LegacyIndexed.module program with
   | .error _ => false
   | .ok common => !(Indexed.Core.Typing.checkModule
       { common with declarations := { common.declarations with primitives := [] } } true).isOk)
#eval check "converted Core still rejects a replaced actual body"
  (match LegacyIndexed.module program with
   | .error _ => false
   | .ok common => !(Indexed.Core.Typing.checkModule { common with functions := (common.functions.map
       (fun function => if function.id == 0 then { function with body := .unit } else function)) } true).isOk)

private def serialCollision : CheckedModule := ⟨[{ main with body :=
  (.letE 20 (affine .qq 7) (.letE 21 (affine .cinfReal 7) (.literal .int 0))) }], some 1⟩
#eval check "new audit is not replaced by the older base-indexed freshness check"
  (Typing.auditModule serialCollision && !(LegacyIndexed.check serialCollision true).isOk)
#eval check "legacy function names never install declarations"
  (LegacyIndexed.check { program with functions := [
    { make with name := "Point\nend VastitasGenerated\naxiom injected : False" }, main] } true).isOk

end VastitasKernel.LegacyIndexedRegression
