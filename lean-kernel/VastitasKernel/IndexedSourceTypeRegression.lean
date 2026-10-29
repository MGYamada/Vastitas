import VastitasKernel.IndexedSourceTypes
import VastitasKernel.IndexedSourceRegression

namespace VastitasKernel.Indexed.Source.TypeRegression

private def lib : Namespace.PackageId := ⟨"/source-lib/Vastitas.toml", "geometry", "1.0.0"⟩
private def app : Namespace.Scope := ⟨⟨"/source-app/Vastitas.toml", "app", "1.0.0"⟩, []⟩
private def id (name : String) : DeclId := ⟨⟨lib, []⟩, name⟩
private def path (name : String) : Path := ⟨name.splitOn "::", {}⟩
private def arg (name : String) : TypeArgument := .name (path name)
private def concrete : Indexed.ObjectType := ⟨id "Grid", id "QQ"⟩
private def smooth : Indexed.ObjectType := ⟨id "Smooth", id "CInfReal"⟩
private def object (name : String) (symbol brand : Nat) (type := concrete) : Binding :=
  ⟨name, ⟨symbol, ⟨.object type, some (.local type brand)⟩⟩, {}⟩
private def ctx : TypeContext := [object "X" 10 1, object "Y" 11 2]
private def point (target := "X") (source := "geo::Base") : Source.DataType :=
  .application (path "Point") [arg target, arg source]
private def run (input : Source.DataType) (context := ctx) (scope := app) : Except Diagnostic Core.DataType := do
  let declarations ← checkDeclarations Regression.declarationFixture
  let checked ← checkDataType declarations scope context input
  return checked.resolved.type
private def accepts (input : Source.DataType) (context := ctx) (scope := app) : Bool :=
  (run input context scope).isOk
private def rejects (code : String) (input : Source.DataType) (context := ctx) (scope := app) : Bool :=
  match run input context scope with | .error error => error.code == code | .ok _ => false
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed source type regression failed: {name}")

#eval check "ordinary scalar and Pair types" (accepts (.pure .int) [] && accepts (.pure (.pair .nat)) [])
#eval check "explicit domain and coefficient" (accepts (.object ⟨path "geo::Scheme", path "geo::QQ"⟩) [])
#eval check "point alias resolves declaration and actual local endpoint" (match run (point) with
  | .ok type => type == .indexed ⟨id "Point", [.object (.local concrete 1), .object (.global (id "Base"))]⟩
  | .error _ => false)
#eval check "canonical global endpoint needs no local binder" (accepts (point "geo::Base") [])
#eval check "both local endpoints are retained" (match run (point "X" "Y") with
  | .ok type => type == .indexed ⟨id "Point", [.object (.local concrete 1), .object (.local concrete 2)]⟩
  | .error _ => false)
#eval check "morphism ordering is preserved" (match run (.application (path "geo::Morphism") [arg "Y", arg "X"]) with
  | .ok type => type == .indexed ⟨id "Morphism", [.object (.local concrete 2), .object (.local concrete 1)]⟩
  | .error _ => false)
#eval check "existential family retains domain and marker" (accepts
  (.application (path "geo::Pointed") [arg "geo::Scheme", arg "geo::QQ"]) [])
#eval check "non-geometric family distinguishes all index sorts" (accepts
  (.application (path "geo::Token") [arg "geo::Scheme", arg "geo::QQ", .natural 3, arg "X"]))
#eval check "non-geometric existential package" (accepts
  (.application (path "geo::Sealed") [arg "geo::Scheme", arg "geo::QQ"]) [])
#eval check "index order cannot be reversed" (rejects "E_TYPE"
  (.application (path "geo::Pointed") [arg "geo::QQ", arg "geo::Scheme"]))
#eval check "natural argument cannot replace an object" (rejects "E_TYPE"
  (.application (path "Point") [.natural 1, arg "geo::Base"]))
#eval check "natural index is not a runtime variable" (rejects "E_TYPE"
  (.application (path "geo::Token") [arg "geo::Scheme", arg "geo::QQ", arg "n", arg "X"])
  (ctx ++ [⟨"n", ⟨12, ⟨.pure .nat, none⟩⟩, {}⟩]))
#eval check "markers are not objects" (rejects "E_TYPE" (point "X" "geo::QQ"))
#eval check "implementations are not global objects" (rejects "E_TYPE" (point "X" "geo::Grid"))
#eval check "coefficient mismatch" (rejects "E_TYPE" (point "X" "Z") (ctx ++ [object "Z" 12 3 smooth]))
#eval check "wrong object domain" (rejects "E_TYPE" (point "Z" "Z") [object "Z" 12 3 smooth])
#eval check "empty domain/marker intersection" (rejects "E_TYPE"
  (.object ⟨path "geo::Scheme", path "geo::CInfReal"⟩) [])
#eval check "missing family argument" (rejects "E_TYPE" (.application (path "Point") [arg "X"]))
#eval check "extra family argument" (rejects "E_TYPE" (.application (path "Point") [arg "X", arg "Y", arg "X"]))
#eval check "primitive cannot be used as a family" (rejects "E_TYPE" (.application (path "geo::origin") []))
#eval check "classification is not a family" (rejects "E_TYPE" (.application (path "geo::Scheme") []))
#eval check "unknown local object does not acquire a brand" (rejects "E_NAME" (point "missing"))
#eval check "local scalar cannot be used as an object" (rejects "E_TYPE" (point "n")
  (ctx ++ [⟨"n", ⟨12, ⟨.pure .nat, none⟩⟩, {}⟩]))
#eval check "a qualified path cannot pick a same-spelled local" (rejects "E_NAME" (point "self::X"))
#eval check "wrong result/reference contract in a supplied binding" (rejects "E_CONTEXT" (point)
  [⟨"X", ⟨10, ⟨.object concrete, some (.local smooth 1)⟩⟩, {}⟩])
#eval check "missing object reference" (rejects "E_CONTEXT" (point)
  [⟨"X", ⟨10, ⟨.object concrete, none⟩⟩, {}⟩])
#eval check "duplicate names and symbols rejected" (rejects "E_CONTEXT" (point) (ctx ++ [object "X" 12 3]) &&
  rejects "E_CONTEXT" (point) (ctx ++ [object "Z" 10 3]))
#eval check "module aliases cannot be shadowed" (rejects "E_CONTEXT" (point) (ctx ++ [object "geo" 12 3]))
#eval check "declaration aliases cannot be shadowed" (rejects "E_CONTEXT" (point) (ctx ++ [object "Point" 12 3]))
#eval check "invented module scope rejected" (rejects "E_CONTEXT" (point) ctx { app with path := ["absent"] })
#eval check "immutable value alias keeps nominal identity" (match run (point "Alias") (ctx ++ [object "Alias" 12 1]) with
  | .ok type => type == .indexed ⟨id "Point", [.object (.local concrete 1), .object (.global (id "Base"))]⟩
  | .error _ => false)
#eval check "independent openings retain different local brands" (match run (point "X"), run (point "Y") with
  | .ok left, .ok right => left != right
  | _, _ => false)
#eval check "changing the input context cannot reuse an old type result" (match run (point "X") [object "X" 10 90] with
  | .ok type => type == .indexed ⟨id "Point", [.object (.local concrete 90), .object (.global (id "Base"))]⟩
  | .error _ => false)

/-- Use the actual elaborated dependent parameter/result type in a Core
function and its instantiated call. This fixture still assembles terms directly. -/
def typeFixture : Except Diagnostic Core.Module := do
  let declarations ← checkDeclarations Regression.declarationFixture
  let parameter := object "X" 10 10
  let checkedType ← checkDataType declarations app [parameter] (point)
  let field : Core.Result := ⟨checkedType.resolved.type, none⟩
  let keep : Core.Function := {
    id := 0, definition := ⟨app, "keep"⟩, parameters := [parameter.parameter, ⟨11, field⟩],
    returnType := field.type, body := .variable 11 field }
  let actual : Core.Result := ⟨.object concrete, some (.local concrete 20)⟩
  let substitution := [(ObjectRef.local concrete 10, ObjectRef.local concrete 20)]
  let output : Core.Result := ⟨field.type.rename substitution, none⟩
  let body := Core.Term.letE 20 (.primitive (id "Affine") [.natural 13] actual)
    (.letE 21 (.call 0 [.variable 20 actual, .primitive (id "origin") [.variable 20 actual] output]
      substitution output)
      (.natToInt (.primitive (id "dimension") [.variable 20 actual] ⟨.pure .nat, none⟩)))
  let main : Core.Function := {
    id := 1, definition := ⟨app, "main"⟩, parameters := [], returnType := .pure .int, body }
  return ⟨declarations.resolved.declarations, [keep, main], some 1⟩

#eval check "elaborated dependent types feed actual Core calls and native codegen" ((do
  let module ← typeFixture
  let checked ← Core.Typing.checkModule module true
  let _ ← (Core.Codegen.generate checked).mapError fun message => { code := "E_CODEGEN", message }
  pure () : Except Diagnostic Unit).isOk)

#eval check "a different source endpoint cannot replace the function result" (match typeFixture with
  | .error _ => false
  | .ok module =>
      let wrong := Core.DataType.indexed ⟨id "Point", [.object (.local concrete 99), .object (.global (id "Base"))]⟩
      let changed := { module with functions := [{ module.functions[0]! with returnType := wrong }, module.functions[1]!] }
      !(Core.Typing.checkModule changed true).isOk)

end VastitasKernel.Indexed.Source.TypeRegression
