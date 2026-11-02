import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedCoreRegression

namespace VastitasKernel.Indexed.Core.PackageSemanticRegression
open Semantics

private def id (name : String) : DeclId := ⟨⟨⟨"/core", "core", "1"⟩, []⟩, name⟩
private def concrete : ObjectType := ⟨id "Grid", id "K"⟩
private def abstractObject : ObjectType := ⟨id "Container", id "K"⟩
private def packed : Application := ⟨id "Pointed", [.domain (id "Container"), .marker (id "K")]⟩
private def shape : PackageShape := ⟨abstractObject, [⟨id "Position", [.witness, .global (id "Base")]⟩]⟩
private def objectResult (type : ObjectType) (ref : ObjectRef) : Result := ⟨.object type, some ref⟩
private def witness (symbol : Nat) : Term :=
  .variable symbol (objectResult abstractObject (.local abstractObject symbol))
private def field (symbol brand : Nat) : Term := .variable symbol
  ⟨.indexed ⟨id "Position", [.object (.local abstractObject brand), .object (.global (id "Base"))]⟩, none⟩
private def base : Term := .primitive (id "base") [] (objectResult concrete (.global (id "Base")))
private def globalPackage : Term := .pack packed base
  [.primitive (id "origin") [base]
    ⟨.indexed ⟨id "Position", [.object (.global (id "Base")), .object (.global (id "Base"))]⟩, none⟩]
private def moduleWith (body : Term) : Module :=
  { Regression.packageFixture with functions :=
    [⟨2, id "main", [], .pure .int, body, {}⟩] }

/-- The witness initially equals its explicit global base. Reopening changes
only the bound witness index, twice, while preserving the actual payload. -/
def globalWitnessFixture : Module := moduleWith
  (.letE 50 globalPackage (.unpack 60 [61] (.variable 50 ⟨.package packed, none⟩)
    (.letE 62 (.pack packed (witness 60) [field 61 60])
      (.unpack 70 [71] (.variable 62 ⟨.package packed, none⟩)
        (.natToInt (.primitive (id "dimension") [witness 70] ⟨.pure .nat, none⟩))))))

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed package semantics regression failed: {name}")

#eval check "global witness can be packaged and reopened twice" (Typing.checkModule globalWitnessFixture true).isOk
#eval check "global-witness fixture preserves zero-dimensional payload" (decide
  (eval globalWitnessFixture 100 (fun _ => none) globalWitnessFixture.functions[0]!.body = some (.integer 0)))
#eval check "bound witness and explicit global get different opening indices" (decide
  (shape.instantiate (.local abstractObject 60) =
    [⟨id "Position", [.object (.local abstractObject 60), .object (.global (id "Base"))]⟩]))
#eval check "equal runtime descriptors do not permit cross-opening fields" (!
  (Typing.checkModule (moduleWith (.letE 50 globalPackage
    (.unpack 60 [61] (.variable 50 ⟨.package packed, none⟩)
      (.unpack 70 [71] (.variable 50 ⟨.package packed, none⟩)
        (.letE 80 (.pack packed (witness 60) [field 71 70]) (.integer 0)))))) true).isOk)
#eval check "forged global annotation cannot erase the opened witness" (!
  (Typing.checkModule (moduleWith (.unpack 60 [61] globalPackage
    (.letE 80 (.variable 61 ⟨.indexed ⟨id "Position",
      [.object (.global (id "Base")), .object (.global (id "Base"))]⟩, none⟩) (.integer 0)))) true).isOk)
#eval check "a point cannot escape the opened witness scope" (!
  (Typing.checkModule (moduleWith (.letE 80 (.unpack 60 [61] globalPackage (field 61 60)) (.integer 0))) true).isOk)

private def localObject : Term := .primitive (id "construct") [.natural 41]
  (objectResult concrete (.local concrete 45))
private def localAlias : Term := .variable 49 localObject.result
private def localPackage : Term := .pack packed localAlias
  [.primitive (id "origin") [localAlias]
    ⟨.indexed ⟨id "Position", [.object (.local concrete 45), .object (.global (id "Base"))]⟩, none⟩]
private def escapedAlias (symbol : Nat) : Term := .variable symbol (witness 60).result

/-- The object itself is first class. Its type contains no local object index,
while its result reference retains the opening's exact fresh identity. -/
def escapedObjectFixture : Module := moduleWith
  (.letE 49 localObject (.letE 50 localPackage
    (.letE 80 (.scope (.unpack 60 [61] (.variable 50 ⟨.package packed, none⟩) (witness 60)))
      (.letE 81 (.scope (escapedAlias 80))
        (.natToInt (.primitive (id "dimension") [escapedAlias 81] ⟨.pure .nat, none⟩))))))
#eval check "bare opened object and aliases can leave their blocks" (Typing.checkModule escapedObjectFixture true).isOk
#eval check "escaped bare object retains the actual descriptor" (decide
  (eval escapedObjectFixture 100 (fun _ => none) escapedObjectFixture.functions[0]!.body = some (.integer 41)))
#eval check "escaped object cannot acquire another opening's field" (!
  (Typing.checkModule (moduleWith (.letE 50 globalPackage
    (.letE 80 (.unpack 60 [61] (.variable 50 ⟨.package packed, none⟩) (witness 60))
      (.unpack 70 [71] (.variable 50 ⟨.package packed, none⟩)
        (.letE 81 (.pack packed (escapedAlias 80) [field 71 70]) (.integer 0)))))) true).isOk)
#eval check "an escaped object does not permit reusing its opening serial" (!
  (Typing.checkModule (moduleWith (.letE 80 (.unpack 60 [61] globalPackage (witness 60))
    (.unpack 60 [71] globalPackage (.integer 0)))) true).isOk)

private def multiEnv : Declarations := { Regression.primitiveFixture.declarations with packages :=
  [⟨id "Pointed", [⟨abstractObject, [⟨id "Position", [.witness, .global (id "Base")]⟩,
    ⟨id "Route", [.witness, .witness]⟩]⟩]⟩] }
private def identityBase : Term := .primitive (id "identity") [base]
  ⟨.indexed ⟨id "Route", [.object (.global (id "Base")), .object (.global (id "Base"))]⟩, none⟩
private def originBase : Term := .primitive (id "origin") [base]
  ⟨.indexed ⟨id "Position", [.object (.global (id "Base")), .object (.global (id "Base"))]⟩, none⟩
private def mapField : Term := .variable 62
  ⟨.indexed ⟨id "Route", [.object (.local abstractObject 60), .object (.local abstractObject 60)]⟩, none⟩
private def multiBody (first second : Term) : Term := .unpack 60 [61, 62] (.pack packed base [first, second])
  (.letE 63 (.pack packed (witness 60)
    [.primitive (id "apply") [mapField, field 61 60] (field 61 60).result, mapField])
    (.unpack 70 [71, 72] (.variable 63 ⟨.package packed, none⟩)
      (.natToInt (.primitive (id "dimension") [witness 70] ⟨.pure .nat, none⟩))))

/-- The point and morphism fields are both used after opening, then repackaged
in their declared order. Native structures must retain every actual field. -/
def multipleFieldsFixture : Module :=
  { moduleWith (multiBody originBase identityBase) with declarations := multiEnv }
#eval check "multiple heterogeneous indexed fields retain their order" (Typing.checkModule multipleFieldsFixture true).isOk
#eval check "all ordered fields survive evaluation and reopening" (decide
  (eval multipleFieldsFixture 100 (fun _ => none) multipleFieldsFixture.functions[0]!.body = some (.integer 0)))
#eval check "swapping point and morphism payloads is rejected" (!
  (Typing.checkModule { moduleWith (multiBody identityBase originBase) with declarations := multiEnv } true).isOk)
#eval check "a morphism cannot escape the opened witness scope" (!
  (Typing.checkModule { moduleWith (.letE 80
    (.unpack 60 [61, 62] (.pack packed base [originBase, identityBase]) mapField) (.integer 0))
    with declarations := multiEnv } true).isOk)

private def tokenEnv : Declarations := {
  Regression.packageFixture.declarations with
  indexed := Regression.packageFixture.declarations.indexed ++
    [⟨id "Lock", .family ⟨[.object (id "Container"), .natural], [], .token⟩⟩]
  packages := [⟨id "Sealed", [⟨abstractObject, [⟨id "Lock", [.witness, .natural 3]⟩]⟩]⟩] }
private def sealed : Application := ⟨id "Sealed", [.domain abstractObject.domain, .marker abstractObject.marker]⟩
private def tokenResult (brand : Nat) : Result :=
  ⟨.indexed ⟨id "Lock", [.object (.local abstractObject brand), .natural 3]⟩, none⟩
private def tokenModule (body : Term) : Module := ⟨tokenEnv,
  [⟨0, id "seal", [⟨0, objectResult abstractObject (.local abstractObject 0)⟩, ⟨1, tokenResult 0⟩],
    .package sealed, body, {}⟩], none⟩
#eval check "the same package mechanism admits a non-geometric indexed token" (
  Typing.checkModule (tokenModule (.pack sealed (witness 0) [.variable 1 (tokenResult 0)])) false).isOk
#eval check "empty token representation still rejects a wrong nominal witness" (!
  (Typing.checkModule (tokenModule (.pack sealed (witness 0) [.variable 1 (tokenResult 2)])) false).isOk)

end VastitasKernel.Indexed.Core.PackageSemanticRegression
