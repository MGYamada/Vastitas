import VastitasPromotion.Fixture
import VastitasKernel.NamespaceChecker
import VastitasKernel.Codegen

/-! Test-only evaluation of the scalar/Pair subset, using the actual primitive
semantics. This is a bounded regression harness, not a public interpreter or a
substitute for the oracle's arbitrary-input Eval proofs. -/
namespace VastitasKernel.PromotionRegression
open Semantics PromotionFixture

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"promotion regression failed: {name}")

def evaluate : Nat → List CheckedFunction → Environment → Term → Option Value
  | 0, _, _, _ => none
  | fuel + 1, functions, env, term => do
    match term with
    | .literal .nat n => pure (.nat n)
    | .literal .int n => pure (.int (Int.ofNat n))
    | .boolean b => pure (.bool b)
    | .unit => pure .unit
    | .var symbol _ => env symbol
    | .unary op arg _ => evalUnary op (← evaluate fuel functions env arg)
    | .binary op left right _ =>
      evalBinary op (← evaluate fuel functions env left) (← evaluate fuel functions env right)
    | .builtin op args _ => evalBuiltin op (← args.mapM (evaluate fuel functions env))
    | .letE symbol value body =>
      evaluate fuel functions (bindValue env symbol (← evaluate fuel functions env value)) body
    | .branch condition yes no _ =>
      let .bool b ← evaluate fuel functions env condition | none
      evaluate fuel functions env (if b then yes else no)
    | .call id args _ _ =>
      let f ← lookupFunction functions id
      let env ← bindArguments f.params (← args.mapM (evaluate fuel functions env))
      evaluate fuel functions env f.body
    | _ => none

def run (module : CheckedModule) (name : String) (args : List Value) : Option Value := do
  let f ← module.functions.find? (·.name == name)
  evaluate 256 module.functions (← bindArguments f.params args) f.body

def numericalContract (module : CheckedModule) : Bool :=
  [("__vastitas_m0_0_0", [.nat 20, .nat 22], Value.pairNat 20 22),
   ("__vastitas_m1_0_1", [.nat 20, .int (-7)], .pairInt 20 (-7)),
   ("__vastitas_m2_1_0", [.int (-7), .nat 20], .pairInt (-7) 20),
   ("__vastitas_m3_1_1", [.int (-7), .int (-2)], .pairInt (-7) (-2)),
   ("__vastitas_m5_0_0", [.nat 20, .nat 22], .nat 42),
   ("__vastitas_m6_0_1", [.nat 20, .int 22], .int 42),
   ("__vastitas_m7_1_0", [.int 22, .nat 20], .int 42),
   ("__vastitas_m4_1_1", [.int (-7), .int (-2)], .int (-9)),
   ("__vastitas_m9_0_0", [.nat 20, .nat 22], .nat 22),
   ("__vastitas_m10_0_1", [.nat 20, .int (-7)], .int 20),
   ("__vastitas_m11_1_0", [.int (-7), .nat 20], .int 20),
   ("__vastitas_m8_1_1", [.int (-7), .int (-2)], .int (-2))].all fun (name, args, value) =>
    run module name args == some value

#eval check "actual checked stdlib contract" (numericalContract checked && Typing.auditModule checked)

private def forgedCall : CheckedModule := { checked with
  functions := checked.functions.map fun f =>
    if f.name == "__vastitas_m6_0_1" then
      { f with
        body := .call (function "__vastitas_m1_0_1").id
          [.var 53 ⟨.nat, none⟩, .var 54 ⟨.int, none⟩] [] ⟨.int, none⟩ }
    else f }
#eval check "forged selected call result" (!Typing.auditModule forgedCall &&
  match certifyModule forgedCall with
  | .ok legacy => !(Codegen.generate legacy).isOk
  | .error _ => false)

#eval show IO Unit from do
  let some legacy := raw.legacyExact | throw (IO.userError "expected first-order stdlib")
  check "checkProgram acceptance" (checkProgram legacy).isOk
  check "checkSurfaceProgram acceptance" acceptance.isOk
  let .ok (families, _) := (DispatchChecker.prepareFamilies legacy).run {}
    | throw (IO.userError "family preparation failed")
  for (family, winners) in families.zip [[0, 1, 2, 3], [5, 6, 7, 4], [9, 10, 11, 8]] do
    check "binary key universe stays 16" (family.checked.keys.length == 16)
    for (key, winner) in [[0, 0], [0, 1], [1, 0], [1, 1]].zip winners do
      check "independent selected method" (family.checked.winner key == some winner)
      let name := DispatchChecker.monoName winner key
      check "selected body exists" (checked.functions.any (·.name == name))

private def namespaceModule (path : List String) : Namespace.Module := {
  path, isPublic := true, span := {}, imports := [], functions := [], generics := [], methods := [] }
private def namespaced : Namespace.Program := {
  file := "promotion-fixture", root := "/stdlib/Vastitas.toml"
  packages := [{
    id := ⟨"/stdlib/Vastitas.toml", "vastitas_std", "0.1.0"⟩, dependencies := []
    modules := [namespaceModule [], namespaceModule ["arithmetic"], {
      namespaceModule ["arithmetic", "generic"] with
      functions := raw.functions.map fun f => { f with isPublic := true }
      generics := raw.generics.map fun g => { g with isPublic := true }
      methods := raw.methods }] }] }
#eval check "actual namespace acceptance" (checkNamespaceProgram namespaced).isOk

private def changeMethod (index : Nat) (edit : Surface.Method → Surface.Method) : Surface.Program :=
  { raw with methods := raw.methods.zipIdx.map fun (m, i) => if i == index then edit m else m }
private def badValues := changeMethod 1 fun m => { m with
  body := .mk [] (.call "pair" [.integer "0" {}, .integer "0" {}] {}) {} }
private def badPolicy := changeMethod 0 fun m => { m with
  result := .data (.pair "Int")
  body := .mk [] (.call "pair" [
    .call "int" [.variable "left" {}] {}, .call "int" [.variable "right" {}] {}] {}) {} }

#eval show IO Unit from do
  for (label, program) in [("value-changing", badValues), ("wrong same-type policy", badPolicy)] do
    let .ok certified := checkSurfaceProgram program
      | throw (IO.userError s!"{label} is legal ordinary code, not a compiler type error")
    check s!"{label} violates library contract" (!numericalContract certified.val)

end VastitasKernel.PromotionRegression
