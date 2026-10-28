import VastitasKernel.IndexedPrimitives

namespace VastitasKernel.Indexed.PrimitiveRegression
private def id (name : String) : DeclId := ⟨⟨⟨"/primitives", "primitives", "1"⟩, []⟩, name⟩
private def family (representation : FamilyRepresentation) : Declaration :=
  .family ⟨[.object (id "Container"), .object (id "Container")], [.sameBase 0 1], representation⟩
private def env : Environment := [
  ⟨id "K", .marker⟩, ⟨id "L", .marker⟩,
  ⟨id "Grid", .implementation (id "K") .affineDescriptor [.origin, .dimension]⟩,
  ⟨id "Sparse", .implementation (id "K") .affineDescriptor []⟩,
  ⟨id "Other", .implementation (id "L") .affineDescriptor [.origin, .dimension]⟩,
  ⟨id "Container", .classification [] [id "Grid", id "Sparse", id "Other"]⟩,
  ⟨id "Base", .global (id "Grid")⟩, ⟨id "OtherBase", .global (id "Other")⟩,
  ⟨id "Position", family .point⟩, ⟨id "Arrow", family .morphism⟩,
  ⟨id "DifferentArrow", family .morphism⟩, ⟨id "Token", family .token⟩ ]
private def grid : ObjectType := ⟨id "Grid", id "K"⟩
private def abstractGrid : ObjectType := ⟨id "Container", id "K"⟩
private def x : ObjectRef := .local grid 1
private def y : ObjectRef := .local grid 2
private def z : ObjectRef := .local grid 3
private def test : ObjectRef := .local grid 4
private def object (ref : ObjectRef) : ValueType := .object grid ref
private def point (target source : ObjectRef) : ValueType :=
  .indexed ⟨id "Position", [.object target, .object source]⟩
private def map (source target : ObjectRef) : ValueType :=
  .indexed ⟨id "Arrow", [.object source, .object target]⟩
private def accept (binding : PrimitiveBinding) (args : List ValueType) : Bool :=
  match checkEnvironment env with
  | .error _ => false
  | .ok checked => (inferPrimitive checked binding [x, y, z, test] 10 args).isOk
private def audit (binding : PrimitiveBinding) (args : List ValueType) (result : ValueType) : Bool :=
  match checkEnvironment env with
  | .error _ => false
  | .ok checked => (checkPrimitive checked binding [x, y, z, test] 10 args result).isOk
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed primitive regression failed: {name}")

#eval check "finite environment" (validEnvironment env)
#eval check "descriptor constructor" (accept (.descriptor (id "Grid")) [.natural])
#eval check "descriptor cannot construct an abstract classification" (!accept (.descriptor (id "Container")) [.natural])
#eval check "descriptor checks arity" (!accept (.descriptor (id "Grid")) [] &&
  !accept (.descriptor (id "Grid")) [.natural, .natural])
#eval check "global object" (accept (.global (id "Base")) [])
#eval check "coefficient marker is not a global object" (!accept (.global (id "K")) [])
#eval check "origin requires admitted implementation" (accept (.origin grid (id "Position") (id "Base")) [object x])
#eval check "dimension requires admitted implementation" (accept (.dimension grid) [object x])
#eval check "broader abstract domain does not acquire origin" (
  !validPrimitiveBinding env (.origin abstractGrid (id "Position") (id "Base")))
#eval check "broader abstract domain does not acquire dimension" (!validPrimitiveBinding env (.dimension abstractGrid))
#eval check "narrow original brand cannot bypass a broad static annotation" (
  !accept (.origin grid (id "Position") (id "Base")) [.object abstractGrid x] &&
  !accept (.dimension grid) [.object abstractGrid x])
#eval check "a forged narrow annotation on a broad brand is invalid" (
  !accept (.dimension grid) [.object grid (.local abstractGrid 8)])
#eval check "base object must match coefficient" (!validPrimitiveBinding env
  (.origin grid (id "Position") (id "OtherBase")))
#eval check "origin family must be a point representation" (!validPrimitiveBinding env
  (.origin grid (id "Arrow") (id "Base")))
#eval check "token cannot impersonate sealed primitive result" (!validPrimitiveBinding env
  (.identity grid (id "Token")))
#eval check "identity does not require origin or dimension" (
  accept (.identity abstractGrid (id "Arrow")) [.object abstractGrid (.local abstractGrid 8)])
#eval check "compose matching endpoints" (audit (.compose (id "Arrow")) [map y z, map x y] (map x z))
#eval check "compose refuses matching dimensions with different endpoints" (!accept (.compose (id "Arrow"))
  [map y z, map x x])
#eval check "apply retains an arbitrary test object" (audit (.apply (id "Arrow") (id "Position"))
  [map x y, point x test] (point y test))
#eval check "apply refuses a different target" (!accept (.apply (id "Arrow") (id "Position"))
  [map x y, point z test])
#eval check "apply cannot replace the test object" (!audit (.apply (id "Arrow") (id "Position"))
  [map x y, point x test] (point y (.global (id "Base"))))
#eval check "apply cannot replace the result target" (!audit (.apply (id "Arrow") (id "Position"))
  [map x y, point x test] (point z test))
#eval check "family identities are not erased to representations" (!accept (.compose (id "Arrow"))
  [.indexed ⟨id "DifferentArrow", [.object y, .object z]⟩, map x y])
#eval check "unknown family binding rejected" (!validPrimitiveBinding env
  (.apply (id "Arrow") (id "Missing")))
#eval check "forged output type rejected" (!audit (.dimension grid) [object x] (object x))
#eval check "descriptor cannot reuse a known brand" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => !(inferPrimitive checked (.descriptor (id "Grid")) [x] 1 [.natural]).isOk)
#eval check "descriptor cannot fabricate a global result" (!audit (.descriptor (id "Grid")) [.natural]
  (.object grid (.global (id "Base"))))
#eval check "global cannot fabricate a local alias" (!audit (.global (id "Base")) [] (object x))
#eval check "origin cannot fabricate its witness" (!audit (.origin grid (id "Position") (id "Base"))
  [object x] (point y (.global (id "Base"))))
end VastitasKernel.Indexed.PrimitiveRegression
