import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedCoreRegression

namespace VastitasKernel.Indexed.Core.SemanticRegression
open Semantics

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed semantics regression failed: {name}")

private def runMain (module : Module) (fuel : Nat := 200) : Option Value := do
  let id ← module.main
  let function ← module.functions.find? fun function => function.id == id
  let arguments ← bindArguments function.parameters []
  eval module fuel arguments function.body

#eval check "actual checked package fixture returns 2" (decide
  (runMain Regression.packageFixture = some (.integer 2)))
#eval check "actual checked primitive fixture returns 42" (decide
  (runMain Regression.primitiveFixture = some (.integer 42)))
#eval check "actual checked Pair/arithmetic fixture retains arbitrary precision" (decide
  (runMain Regression.scalarFixture = some (.integer 999999999999999999999999999999999999999997)))
#eval check "finite observation exhaustion is explicit" (decide
  (runMain Regression.packageFixture 1 = none))

private def empty : Values := fun _ => none
private def module : Module := Regression.packageFixture
private def id (name : String) : DeclId := ⟨⟨⟨"/semantics", "semantics", "1"⟩, []⟩, name⟩
private def type : ObjectType := ⟨id "Shape", id "K"⟩
private def otherType : ObjectType := ⟨id "Other", id "K"⟩
private def object (n : Nat) : Object := ⟨id "Shape", IndexedRuntime.descriptor n⟩
private def world : World := bindLocal (bindLocal (fun _ => none) 1 (object 3)) 2 (object 3)

#eval check "distinct local brands may denote equal runtime objects" (decide
  (interpretRef [] world (.local type 1) = interpretRef [] world (.local type 2)))
#eval check "changing type metadata does not change the world slot" (decide
  (interpretRef [] world (.local otherType 1) = some (object 3)))
#eval check "fresh world binding preserves the earlier slot" (decide
  (interpretRef [] (bindLocal world 3 (object 9)) (.local type 1) = some (object 3)))
#eval check "global interpretation never reads a local world slot" (decide
  (interpretRef [] world (.global (id "Shape")) = none))
#eval check "Nat subtraction is saturating" (decide
  (evalBinary .sub (.natural 1) (.natural 9) = some (.natural 0)))
#eval check "mixed scalar arithmetic is not implicitly promoted" (decide
  (evalBinary .add (.natural 1) (.integer 2) = none))
#eval check "Pair projections reject a mismatched element type" (decide
  (evalProject .int true (.pairNat 1 2) = none))
#eval check "branch evaluates only the selected operand" (decide
  (eval module 10 empty (.branch (.boolean true) (.integer 7)
    (.variable 999 ⟨.pure .int, none⟩) ⟨.pure .int, none⟩) = some (.integer 7)))
#eval check "both branch operands still require independent acceptance" (!
  (Typing.checkModule { module with functions := [{ module.functions[2]! with
    body := .branch (.boolean true) (.integer 7) (.variable 999 ⟨.pure .int, none⟩) ⟨.pure .int, none⟩ }] } true).isOk)
#eval check "result annotations do not select operational values" (decide
  (eval module 10 empty (.unary .neg (.integer 8) ⟨.pure .bool, none⟩) = some (.integer (-8))))
#eval check "lying annotations still fail independent acceptance" (!
  (Typing.checkModule { module with functions := [{ module.functions[2]! with
    body := .unary .neg (.integer 8) ⟨.pure .bool, none⟩ }] } true).isOk)
#eval check "function binding requires exact arity" (decide
  ((bindArguments [⟨0, ⟨.pure .nat, none⟩⟩] []).isNone))
#eval check "package field binding requires exact arity" (decide
  ((bindFields empty [1, 2] [.token]).isNone))

private def taggedPackage (n : Nat) : Option Value :=
  eval module 30 empty (.call 0 [.natural n] [] module.functions[0]!.body.result)
private def packageDimension : Option Value → Option Nat
  | some (.package witness [.point point]) =>
      if witness = point.target && point.source.descriptor.dimension == 0 then some witness.descriptor.dimension else none
  | _ => none
#eval check "repeated activations retain their own package payload" (decide
  (packageDimension (taggedPackage 3) = some 3 ∧ packageDimension (taggedPackage 8) = some 8))
#eval check "closed primitives reject wrong runtime shapes" (decide
  (evalPrimitive [] (.dimension type) [.integer 2] = none ∧
   evalPrimitive [] (.compose (id "Map")) [.object (object 1), .object (object 2)] = none))
#eval check "primitive erasure uses the actual runtime compose operation" (decide
  (evalRuntimePrimitive (.compose (id "Map"))
    [.morphism ⟨⟨3⟩, ⟨7⟩⟩, .morphism ⟨⟨1⟩, ⟨3⟩⟩] = some (.morphism ⟨⟨1⟩, ⟨7⟩⟩)))

end VastitasKernel.Indexed.Core.SemanticRegression
