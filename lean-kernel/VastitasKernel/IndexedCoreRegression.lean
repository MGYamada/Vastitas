import VastitasKernel.IndexedTypeAudit

namespace VastitasKernel.Indexed.Core.Regression
open Typing
private def id (name : String) : DeclId := ⟨⟨⟨"/core", "core", "1"⟩, []⟩, name⟩
private def concrete : ObjectType := ⟨id "Grid", id "K"⟩
private def abstractObject : ObjectType := ⟨id "Container", id "K"⟩
private def shape : PackageShape := ⟨abstractObject, [⟨id "Position", [.witness, .global (id "Base")]⟩]⟩
private def packed : Application := ⟨id "Pointed", [.domain (id "Container"), .marker (id "K")]⟩
private def env : Declarations := {
  indexed := [⟨id "K", .marker⟩,
    ⟨id "Grid", .implementation (id "K") .affineDescriptor [.origin, .dimension]⟩,
    ⟨id "Sparse", .implementation (id "K") .affineDescriptor []⟩,
    ⟨id "Container", .classification [] [id "Grid"]⟩,
    ⟨id "Base", .global (id "Grid")⟩,
    ⟨id "Position", .family ⟨[.object (id "Container"), .object (id "Container")], [.sameBase 0 1], .point⟩⟩]
  packages := [⟨id "Pointed", [shape]⟩]
  primitives := [⟨id "construct", .descriptor (id "Grid")⟩,
    ⟨id "base", .global (id "Base")⟩,
    ⟨id "origin", .origin concrete (id "Position") (id "Base")⟩,
    ⟨id "dimension", .dimension concrete⟩] }
private def object (type : ObjectType) (brand : Nat) : Result := ⟨.object type, some (.local type brand)⟩
private def point (reference : ObjectRef) : Result :=
  ⟨.indexed ⟨id "Position", [.object reference, .object (.global (id "Base"))]⟩, none⟩
private def construct (brand : Nat) (dimension : Term := .natural 2) : Term :=
  .primitive (id "construct") [dimension] (object concrete brand)
private def origin (value : Term) : Term :=
  .primitive (id "origin") [value] (point value.result.reference.get!)
private def dimension (value : Term) : Term :=
  .primitive (id "dimension") [value] ⟨.pure .nat, none⟩
private def make : Function := {
  id := 0, definition := id "make", parameters := [⟨0, ⟨.pure .nat, none⟩⟩], returnType := .package packed
  body := .letE 20 (construct 1 (.variable 0 ⟨.pure .nat, none⟩))
    (.pack packed (.variable 20 (object concrete 1)) [origin (.variable 20 (object concrete 1))]) }
private def unpackBody (witnessSymbol : Nat) : Term :=
  .natToInt (dimension (.variable witnessSymbol (object abstractObject witnessSymbol)))
private def unwrap : Function := {
  id := 1, definition := id "unwrap", parameters := [⟨30, ⟨.package packed, none⟩⟩], returnType := .pure .int
  body := .unpack 31 [32] (.variable 30 ⟨.package packed, none⟩) (unpackBody 31) }
private def main : Function := {
  id := 2, definition := id "main", parameters := [], returnType := .pure .int
  body := .call 1 [.call 0 [.natural 2] [] ⟨.package packed, none⟩] [] ⟨.pure .int, none⟩ }
private def program : Module := ⟨env, [make, unwrap, main], some 2⟩
private def bodyProgram (body : Term) : Module :=
  ⟨env, [{ main with body }], some 2⟩
/-- Actual audited package fixture, also compiled by the native regression. -/
def packageFixture : Module := program
private def accepts (module : Module) (requireMain : Bool := true) : Bool := (checkModule module requireMain).isOk
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed Core regression failed: {name}")

#eval check "full package/primitive/function composition" (accepts program)
#eval check "all bodies checked, even when main does not call them" (!accepts
  { program with functions := [make, { unwrap with body := .integer 0, returnType := .pure .bool }, { main with body := .integer 0 }] })
#eval check "entry signature and presence" (!accepts { program with main := none } &&
  accepts { program with main := none } false && !accepts { program with main := some 0 })
#eval check "real calls require dependency order" (!accepts { program with functions := [main, make, unwrap] })
#eval check "cycles are rejected" (!accepts (bodyProgram (.call 2 [] [] ⟨.pure .int, none⟩)))
#eval check "unknown call rejected" (!accepts (bodyProgram (.call 99 [] [] ⟨.pure .int, none⟩)))
#eval check "function IDs cannot duplicate" (!accepts { program with functions := [make, unwrap, main, main] })
#eval check "declaration kinds share one namespace" (!accepts { program with declarations :=
  { env with primitives := ⟨id "Pointed", .global (id "Base")⟩ :: env.primitives } })
#eval check "ambiguous existential cases rejected" (!accepts { program with declarations :=
  { env with packages := [⟨id "Pointed", [shape, shape]⟩] } })
#eval check "package index sorts and arity are checked" (!accepts { program with functions :=
  [{ make with returnType := .package ⟨id "Pointed", [.marker (id "K"), .domain (id "Container")]⟩ }, unwrap, main] })
#eval check "added implementation invalidates broad operation use" (!accepts { program with declarations :=
  { env with indexed := env.indexed.map fun entry => if entry.id == id "Container" then
    { entry with declaration := .classification [] [id "Grid", id "Sparse"] } else entry } })
#eval check "scope retains an outer anonymous object's brand" (accepts (bodyProgram
  (.letE 20 (origin (construct 1)) (.letE 21 (.scope (.variable 20 (point (.local concrete 1)))) (.integer 0)))))
#eval check "scope rejects a new anonymous point escaping" (!accepts (bodyProgram
  (.letE 20 (.scope (origin (construct 1))) (.integer 0))))
#eval check "scope rejects a locally bound point escaping" (!accepts (bodyProgram
  (.letE 21 (.scope (.letE 20 (construct 1) (origin (.variable 20 (object concrete 1))))) (.integer 0))))
#eval check "unpack rejects escaped witness-dependent field" (!accepts { program with functions := [make,
  { main with body := .letE 40 (.unpack 41 [42] (.call 0 [.natural 2] [] ⟨.package packed, none⟩)
    (.variable 42 (point (.local abstractObject 41)))) (.integer 0) }] })
#eval check "unpack field symbols cannot be repeated" (!accepts { program with functions := [make,
  { unwrap with body := .unpack 31 [31] (.variable 30 ⟨.package packed, none⟩) (unpackBody 31) }, main] })
#eval check "two constructions cannot reuse a brand" (!accepts (bodyProgram
  (.letE 20 (construct 1) (.letE 21 (construct 1) (.integer 0)))))
#eval check "immutable aliases retain their brand" (accepts (bodyProgram
  (.letE 20 (construct 1) (.letE 21 (.variable 20 (object concrete 1))
    (.natToInt (dimension (.variable 21 (object concrete 1))))))))
#eval check "upcast retains the reference and valid finite domain" (accepts (bodyProgram
  (.letE 20 (.ascribe (.object abstractObject) (construct 1))
    (.natToInt (dimension (.variable 20 ⟨.object abstractObject, some (.local concrete 1)⟩))))))
#eval check "coercion cannot erase indexed obligations" (!accepts (bodyProgram
  (.letE 20 (.ascribe (.pure .unit) (origin (construct 1))) (.integer 0))))
#eval check "unused branch annotations are checked" (!accepts (bodyProgram
  (.branch (.boolean true) (.integer 0) (.variable 900 ⟨.pure .int, none⟩) ⟨.pure .int, none⟩)))
#eval check "constant branches cannot alias distinct object identities" (!accepts (bodyProgram
  (.letE 20 (construct 1) (.letE 21 (construct 2) (.letE 22
    (.branch (.boolean true) (.variable 20 (object concrete 1)) (.variable 21 (object concrete 2)) (object concrete 1))
    (.integer 0))))))
#eval check "branch merge requires a fresh identity" (accepts (bodyProgram
  (.letE 20 (construct 1) (.letE 21 (construct 2) (.letE 22
    (.branch (.boolean true) (.variable 20 (object concrete 1)) (.variable 21 (object concrete 2)) (object concrete 3))
    (.integer 0))))))

private def keep : Function := {
  id := 4, definition := id "keep", parameters := [⟨40, object abstractObject 40⟩,
    ⟨41, point (.local abstractObject 40)⟩], returnType := (point (.local abstractObject 40)).type
  body := .variable 41 (point (.local abstractObject 40)) }
private def withDependentCall (substitution : List (ObjectRef × ObjectRef)) (output : Result) : Module :=
  ⟨env, [keep, { main with body := .letE 20 (construct 1) (.letE 21
    (.call 4 [.variable 20 (object concrete 1), origin (.variable 20 (object concrete 1))] substitution output)
    (.integer 0)) }], some 2⟩
#eval check "dependent calls refine finite domains and preserve endpoints" (accepts
  (withDependentCall [(.local abstractObject 40, .local concrete 1)] (point (.local concrete 1))))
#eval check "forged dependent substitution rejected" (!accepts
  (withDependentCall [(.local abstractObject 40, .local concrete 2)] (point (.local concrete 2))))
#eval check "dependent result cannot use another object" (!accepts
  (withDependentCall [(.local abstractObject 40, .local concrete 1)] (point (.local concrete 2))))
#eval check "global references cannot be rewritten" (!accepts
  (withDependentCall [(.local abstractObject 40, .local concrete 1), (.global (id "Base"), .local concrete 1)]
    (point (.local concrete 1))))

private def same : Function := {
  id := 5, definition := id "same", parameters := [⟨60, object abstractObject 60⟩],
  returnType := .object abstractObject, body := .variable 60 (object abstractObject 60) }
private def withObjectCall (output : Result) : Module := ⟨env, [same, { main with
  body := .letE 20 (construct 1) (.letE 21
    (.call 5 [.variable 20 (object concrete 1)] [(.local abstractObject 60, .local concrete 1)] output)
    (.integer 0)) }], some 2⟩
#eval check "ordinary object results are generative" (accepts (withObjectCall (object abstractObject 2)))
#eval check "object-returning call cannot reuse input serial under another type" (!accepts
  (withObjectCall (object abstractObject 1)))
#eval check "ordinary object call cannot pretend to return a canonical global" (!accepts
  (withObjectCall ⟨.object abstractObject, some (.global (id "Base"))⟩))
private def broadEnv : Declarations := { env with indexed := env.indexed.map (fun entry =>
  if entry.id == id "Container" then
    { entry with declaration := .classification [] [id "Grid", id "Sparse"] } else entry) }
#eval check "ascribed variable cannot recover a hidden capability" (!accepts
  { bodyProgram (.letE 20 (.ascribe (.object abstractObject) (construct 1))
      (.natToInt (dimension (.variable 20 ⟨.object abstractObject, some (.local concrete 1)⟩))))
    with declarations := broadEnv })
#eval check "forged variable annotation cannot undo an upcast" (!accepts
  { bodyProgram (.letE 20 (.ascribe (.object abstractObject) (construct 1))
      (.natToInt (dimension (.variable 20 (object concrete 1))))) with declarations := broadEnv })

private def mapEnv : Declarations := { env with
  indexed := env.indexed ++ [⟨id "Route", .family
    ⟨[.object (id "Container"), .object (id "Container")], [.sameBase 0 1], .morphism⟩⟩]
  primitives := env.primitives ++ [⟨id "identity", .identity concrete (id "Route")⟩,
    ⟨id "compose", .compose (id "Route")⟩, ⟨id "apply", .apply (id "Route") (id "Position")⟩] }
private def route (ref : ObjectRef) : Result := ⟨.indexed ⟨id "Route", [.object ref, .object ref]⟩, none⟩

/-- Every closed primitive is exercised through an actual typed term. The
function and declaration spellings intentionally do not name geometric types. -/
def primitiveFixture : Module := { bodyProgram (.letE 20 (construct 1 (.natural 42))
  (.letE 21 (.primitive (id "base") [] ⟨.object concrete, some (.global (id "Base"))⟩)
  (.letE 22 (.primitive (id "identity") [.variable 20 (object concrete 1)] (route (.local concrete 1)))
  (.letE 23 (.primitive (id "compose") [.variable 22 (route (.local concrete 1)),
    .variable 22 (route (.local concrete 1))] (route (.local concrete 1)))
  (.letE 24 (.primitive (id "apply") [.variable 23 (route (.local concrete 1)),
    origin (.variable 20 (object concrete 1))] (point (.local concrete 1)))
  (.natToInt (dimension (.variable 20 (object concrete 1))))))))) with declarations := mapEnv }
#eval check "all closed primitives in executable terms" (accepts primitiveFixture)

def scalarFixture : Module := bodyProgram
  (.letE 50 (.pair .int (.integer 1000000000000000000000000000000000000000000) (.integer (-3)))
  (.branch (.binary .and (.unary .not (.boolean false) ⟨.pure .bool, none⟩)
    (.binary .le (.natural 2) (.natural 9) ⟨.pure .bool, none⟩) ⟨.pure .bool, none⟩)
    (.binary .add (.project .int true (.variable 50 ⟨.pure (.pair .int), none⟩))
      (.project .int false (.variable 50 ⟨.pure (.pair .int), none⟩)) ⟨.pure .int, none⟩)
    (.natToInt (.binary .sub (.natural 0) (.natural 8) ⟨.pure .nat, none⟩)) ⟨.pure .int, none⟩))
#eval check "scalar arithmetic and Pair remain independent" (accepts scalarFixture)
end VastitasKernel.Indexed.Core.Regression
