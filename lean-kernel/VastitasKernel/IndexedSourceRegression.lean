import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedCodegen

namespace VastitasKernel.Indexed.Source.Regression

private def app : Namespace.PackageId := ⟨"/source-app/Vastitas.toml", "app", "1.0.0"⟩
private def lib : Namespace.PackageId := ⟨"/source-lib/Vastitas.toml", "geometry", "1.0.0"⟩
private def path (name : String) : Path := ⟨name.splitOn "::", {}⟩
private def decl (name : String) (body : Body) (isPublic := true) : Declaration := ⟨name, body, isPublic, {}⟩
private def mod (declarations : List Declaration) (path : List String := []) : Module := {
  module := { path, isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }
  declarations }
private def objectType : Source.ObjectType := ⟨path "Scheme", path "QQ"⟩
private def family (representation : FamilyRepresentation) : Body :=
  .family ⟨[.object (path "Scheme"), .object (path "Scheme")], [.sameBase 0 1], representation⟩
private def shape : Source.PackageShape :=
  ⟨objectType, [⟨path "Point", [.witness, .global (path "Base")]⟩]⟩
private def geometry : List Declaration := [
  decl "QQ" .marker, decl "CInfReal" .marker,
  decl "Grid" (.implementation (path "QQ") .affineDescriptor [.origin, .dimension]),
  decl "Smooth" (.implementation (path "CInfReal") .affineDescriptor [.origin, .dimension]),
  decl "Scheme" (.classification [] [path "Grid"]),
  decl "CInfScheme" (.classification [] [path "Smooth"]),
  decl "Base" (.global (path "Grid")),
  decl "Point" (family .point), decl "Morphism" (family .morphism),
  decl "Pointed" (.package [shape]),
  decl "Affine" (.primitive (.descriptor (path "Grid"))),
  decl "baseObject" (.primitive (.global (path "Base"))),
  decl "origin" (.primitive (.origin objectType (path "Point") (path "Base"))),
  decl "id" (.primitive (.identity objectType (path "Morphism"))),
  decl "dimension" (.primitive (.dimension objectType)),
  decl "compose" (.primitive (.compose (path "Morphism"))),
  decl "apply" (.primitive (.apply (path "Morphism") (path "Point"))),
  decl "Token" (.family ⟨[.domain, .marker, .natural, .object (path "Scheme")], [], .token⟩),
  decl "Sealed" (.package [⟨objectType,
    [⟨path "Token", [.domain (path "Scheme"), .marker (path "QQ"), .natural 3, .witness]⟩]⟩]) ]
private def rootModule : Module := {
  mod [decl "Local" (.classification [path "geo::Scheme"] [path "geo::Grid"])] with
  module := { (mod []).module with imports := [⟨["geo", "Point"], "Point", true, {}⟩] } }
private def program : Program := {
  file := "indexed-source-regression", root := app.source,
  packages := [⟨app, [⟨"geo", lib.source⟩, ⟨"other", lib.source⟩], [rootModule]⟩,
    ⟨lib, [], [mod geometry]⟩] }
private def id (name : String) : DeclId := ⟨⟨lib, []⟩, name⟩
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed source regression failed: {name}")
private def accepts (p : Program) : Bool := (checkDeclarations p).isOk
private def rejects (code : String) (p : Program) : Bool :=
  match checkDeclarations p with | .error error => error.code == code | .ok _ => false
private def changeLibrary (f : Module → Module) : Program :=
  { program with packages := [program.packages[0]!, ⟨lib, [], [f (mod geometry)]⟩] }
private def change (name : String) (body : Body) : Program := changeLibrary fun m =>
  { m with declarations := m.declarations.map fun d => if d.name == name then { d with body } else d }
private def add (declaration : Declaration) : Program := changeLibrary fun m =>
  { m with declarations := m.declarations ++ [declaration] }

#eval check "complete geometry and non-geometric contracts" (accepts program)
#eval check "all primitive bindings retained" (match checkDeclarations program with
  | .ok checked => checked.resolved.declarations.primitives.length == 7
  | .error _ => false)
#eval check "alias and re-export retain canonical owner" (
  (Namespace.resolve program.indexed ⟨app, []⟩ ["Point"] {}).toOption.map (·.owner) == some (id "Point") &&
  (Namespace.resolve program.indexed ⟨app, []⟩ ["other", "Point"] {}).toOption.map (·.owner) == some (id "Point"))
#eval check "declaration and package order independent" (accepts { program with packages :=
  [⟨lib, [], [mod geometry.reverse]⟩, program.packages[0]!] })
#eval check "display filename does not affect identities" (match lower program, lower { program with file := "elsewhere.vast" } with
  | .ok a, .ok b => a.declarations == b.declarations
  | _, _ => false)

private def copyId : Namespace.PackageId := { lib with source := "/another-lib/Vastitas.toml" }
private def twoLibraries : Program := { program with packages :=
  [{ program.packages[0]! with dependencies := program.packages[0]!.dependencies ++ [⟨"copy", copyId.source⟩] },
    program.packages[1]!, ⟨copyId, [], [mod geometry]⟩] }
#eval check "equal package names and declarations keep distinct identities" (match checkDeclarations twoLibraries with
  | .error _ => false
  | .ok checked =>
      let other : DeclId := ⟨⟨copyId, []⟩, "QQ"⟩
      other != id "QQ" && isMarker checked.resolved.declarations.indexed other &&
        isMarker checked.resolved.declarations.indexed (id "QQ"))
#eval check "matching display names cannot mix coefficient identities" (rejects "E_TYPE" { twoLibraries with packages :=
  [{ twoLibraries.packages[0]! with modules := [{ rootModule with declarations := rootModule.declarations ++
    [decl "Mixed" (.primitive (.origin ⟨path "geo::Scheme", path "copy::QQ"⟩ (path "geo::Point") (path "geo::Base")))] }] },
    twoLibraries.packages[1]!, twoLibraries.packages[2]!] })
#eval check "base marker cannot serve as test object" (rejects "E_TYPE"
  (change "origin" (.primitive (.origin objectType (path "Point") (path "QQ")))))
#eval check "wrong coefficient marker" (rejects "E_TYPE"
  (change "origin" (.primitive (.origin ⟨path "Scheme", path "CInfReal"⟩ (path "Point") (path "Base")))))
#eval check "classification cycle" (rejects "E_TYPE"
  (change "Scheme" (.classification [path "Scheme"] [path "Grid"])))
#eval check "complete domain capability audit" (rejects "E_TYPE" (changeLibrary fun m =>
  { m with declarations := (m.declarations.map fun d => if d.name == "Scheme" then
      { d with body := .classification [] [path "Grid", path "Bare"] } else d) ++
    [decl "Bare" (.implementation (path "QQ") .affineDescriptor [])] }))
#eval check "wrong declaration kind" (rejects "E_TYPE" (change "Grid"
  (.implementation (path "Base") .affineDescriptor [.origin, .dimension])))
#eval check "point spelling does not select a representation" (rejects "E_TYPE" (change "Point" (family .token)))
#eval check "invalid family arity" (rejects "E_TYPE" (change "Point"
  (.family ⟨[.object (path "Scheme")], [.sameBase 0 1], .point⟩)))
#eval check "unused bad declaration still checked" (rejects "E_NAME"
  (add (decl "Unused" (.global (path "Missing")))))
#eval check "empty classification" (rejects "E_TYPE" (add (decl "Empty" (.classification [] []))))
#eval check "duplicate package case" (rejects "E_TYPE" (change "Pointed" (.package [shape, shape])))
#eval check "package field index sort" (rejects "E_TYPE" (change "Pointed" (.package
  [⟨objectType, [⟨path "Point", [.witness, .marker (path "QQ")]⟩]⟩])))
#eval check "cross-category duplicate owner" (rejects "E_DUPLICATE" (add (decl "Grid" (.package [shape]))))
#eval check "reserved scalar and function types" (rejects "E_RESERVED" (add (decl "Nat" .marker)) &&
  rejects "E_RESERVED" (add (decl "Fn" .marker)))
#eval check "private declaration cannot leak" (rejects "E_VISIBILITY" (changeLibrary fun m =>
  { m with declarations := m.declarations.map fun d => if d.name == "Grid" then { d with isPublic := false } else d }))
#eval check "private re-export cannot confer public access" (rejects "E_VISIBILITY" (changeLibrary fun m =>
  { m with
    declarations := m.declarations.map fun d => if d.name == "Token" then { d with isPublic := false } else d
    module := { m.module with imports := [⟨["Token"], "Exported", true, {}⟩] } }))
#eval check "cyclic import" (rejects "E_CYCLE" (changeLibrary fun m =>
  { m with module := { m.module with imports := [⟨["second"], "first", false, {}⟩, ⟨["first"], "second", false, {}⟩] } }))
#eval check "import collides with declaration" (rejects "E_DUPLICATE" (changeLibrary fun m =>
  { m with module := { m.module with imports := [⟨["Token"], "QQ", false, {}⟩] } }))
#eval check "unknown package dependency" (rejects "E_NAME" { program with packages := [program.packages[0]!] })
#eval check "dependency cycle" (rejects "E_CYCLE" { program with packages :=
  [program.packages[0]!, { program.packages[1]! with dependencies := [⟨"app", app.source⟩] }] })
#eval check "duplicate package location" (rejects "E_DUPLICATE" { program with packages := program.packages ++ [program.packages[1]!] })
#eval check "invalid package identity" (rejects "E_PROTOCOL" { program with packages :=
  [program.packages[0]!, { program.packages[1]! with id := { lib with version := "1" } }] })

private def ordinary : Namespace.Function := {
  name := "ordinary", params := [], result := .data (.named "Int"),
  body := .mk [] (.integer "0" {}) {}, span := {}, isPublic := true }
#eval check "functions are not declaration references" (rejects "E_TYPE" (changeLibrary fun m =>
  { m with
    module := { m.module with functions := [ordinary] }
    declarations := m.declarations ++ [decl "Bad" (.global (path "ordinary"))] }))
#eval check "function alias cannot acquire indexed reserved spelling" (rejects "E_RESERVED" (changeLibrary fun m =>
  { m with
    module := { m.module with functions := [ordinary], imports := [⟨["ordinary"], "CInfScheme", false, {}⟩] }
    declarations := m.declarations.filter (·.name != "CInfScheme") }))

private def privateParent : Program := { file := "parent", root := lib.source, packages := [⟨lib, [], [
  mod [decl "Secret" .marker false],
  mod [decl "Child" (.implementation (path "super::Secret") .affineDescriptor [])] ["child"]]⟩] }
#eval check "descendant can reference private parent but owns its new declaration" (match checkDeclarations privateParent with
  | .ok checked => checked.resolved.declarations.ids.contains ⟨⟨lib, ["child"]⟩, "Child"⟩
  | .error _ => false)
#eval check "no implicit parent name" (rejects "E_NAME" { privateParent with packages := [⟨lib, [], [
  mod [decl "Secret" .marker false], mod [decl "Child" (.implementation (path "Secret") .affineDescriptor [])] ["child"]]⟩] })

#eval check "forged lookup certificates rejected" (match checkDeclarations program with
  | .error _ => false
  | .ok checked => match checked.resolved.references.head? with
    | none => false
    | some reference =>
        !decide (Reference.Valid program.indexed { reference with target := { reference.target with owner := ⟨⟨app, []⟩, "Scheme"⟩ } }) &&
        !decide (Reference.Valid program.indexed { reference with target := { reference.target with isPublic := false } }) &&
        !decide (Reference.Valid program.indexed { reference with path := path "absent" }) &&
        !decide (Reference.Valid program.indexed { reference with scope := ⟨app, ["absent"]⟩ }))

/-- The exact resolved declarations feed actual Core typing and native output;
there is still no public parser or source-term translation in this fixture. -/
def sourceFixture : Except Diagnostic Core.Module := do
  let checked ← checkDeclarations program
  let type : Indexed.ObjectType := ⟨id "Grid", id "QQ"⟩
  let object := Core.Term.primitive (id "Affine") [.natural 7] ⟨.object type, some (.local type 1)⟩
  let body := Core.Term.natToInt (.primitive (id "dimension") [object] ⟨.pure .nat, none⟩)
  return ⟨checked.resolved.declarations,
    [{ id := 0, definition := ⟨⟨app, []⟩, "main"⟩, parameters := [], returnType := .pure .int, body }], some 0⟩

#eval check "resolved declarations reach actual Core and codegen" ((do
  let module ← sourceFixture
  let checked ← Core.Typing.checkModule module true
  let _ ← (Core.Codegen.generate checked).mapError fun message => { code := "E_CODEGEN", message }
  pure () : Except Diagnostic Unit).isOk)

end VastitasKernel.Indexed.Source.Regression
