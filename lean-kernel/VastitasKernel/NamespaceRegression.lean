import VastitasKernel.NamespaceChecker
import VastitasKernel.NamespaceQuery
import VastitasKernel.EditRegression
import VastitasKernel.NamespaceProtocol
import VastitasKernel.Codegen

/-! Retained legacy top-level checker/Core regressions. Current public JSON
acceptance is covered by LegacySourceRegression and
VastitasPublicTest.AuthorityRegression; shared namespace/dispatch/trace helpers
remain live in the indexed composition. -/
namespace VastitasKernel.Namespace.Regression

private def root : PackageId := ⟨"/app/Vastitas.toml", "app", "0.1.0"⟩
private def dependency : PackageId := ⟨"/lib/Vastitas.toml", "lib", "0.1.0"⟩
private def int : Surface.TypeExpr := .data (.named "Int")
private def fn (name : String) (value : Surface.Expr) (pub := true) : Function := {
  name, params := [], result := int, body := .mk [] value {}, span := {}, isPublic := pub }
private def mod (path : List String) (functions : List Function := []) : Module := {
  path, functions, generics := [], methods := [], imports := [], span := {}, isPublic := true }
private def pkg (id : PackageId) (modules : List Module) : Package := { id, modules, dependencies := [] }

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"namespace regression failed: {name}")

-- Index construction must preserve the old first-match result even before
-- validation rejects duplicate package/module/import/dependency identities.
#eval check "lookup indexes retain duplicate precedence and exact package identity" (Id.run do
  let first := pkg root [mod [] [fn "first" (.integer "1" {})], mod [] [fn "second" (.integer "2" {})]]
  let later := pkg {root with version := "2.0.0"} [mod [] [fn "later" (.integer "3" {})]]
  let p : Program := {file := "index-regression", root := root.source, packages := [first, later]}
  return (packageAt p.indexed root.source).map (·.id) == some root &&
    ((moduleAt p.indexed ⟨root, []⟩).map (·.functions.map (·.name))) == some ["first"] &&
    (moduleAt p.indexed ⟨later.id, []⟩).isNone)

#eval check "duplicate import and dependency indexes keep the first record" (Id.run do
  let m := {mod [] with imports := [
    ⟨["self", "first"], "alias", false, {}⟩, ⟨["self", "second"], "alias", true, {}⟩]}
  let p := {pkg root [m] with dependencies := [⟨"dep", "first"⟩, ⟨"dep", "second"⟩]}
  return (m.lookup.imports["alias"]?.map (·.path)) == some ["self", "first"] &&
    (p.lookup.dependencies["dep"]?.map (·.target)) == some "first")

private def program : Program := {
  file := "namespace-regression", root := root.source
  packages := [
    { pkg root [mod [] [fn "main" (.call "other::value" [] {})]] with
      dependencies := [⟨"other", dependency.source⟩, ⟨"alias", dependency.source⟩] },
    pkg dependency [mod [] [fn "value" (.integer "42" {})]] ] }
private def rejects (code : String) (p : Program) : Bool :=
  match checkNamespaceProgram p with
  | .error error => error.code == code
  | .ok _ => false
private def replaceRoot (m : Module) (extra : List Module := []) : Program :=
  { program with packages := [{ program.packages[0]! with modules := m :: extra }, program.packages[1]!] }

#eval check "path dependency and native core" (match checkNamespaceProgram program true with
  | .ok checked => (Codegen.generate checked).isOk
  | .error _ => false)
#eval check "dependency alias preserves target" (
  (resolve program.indexed ⟨root, []⟩ ["other", "value"] {}).toOption ==
  (resolve program.indexed ⟨root, []⟩ ["alias", "value"] {}).toOption)
#eval check "distinct locations preserve owners" (
  (Owner.mk ⟨root, []⟩ "value").symbol != (Owner.mk ⟨dependency, []⟩ "value").symbol)
#eval check "duplicate owner" (rejects "E_DUPLICATE" (replaceRoot
  (mod [] [fn "a" (.integer "0" {}), fn "a" (.integer "1" {})])))
#eval check "unknown dependency" (rejects "E_NAME" { program with packages := [program.packages[0]!] })
#eval check "dependency cycle" (rejects "E_CYCLE" { program with packages :=
  [program.packages[0]!, { program.packages[1]! with dependencies := [⟨"app", root.source⟩] }] })
#eval check "private qualified access" (rejects "E_VISIBILITY" { program with packages :=
  [program.packages[0]!, pkg dependency [mod [] [fn "value" (.integer "42" {}) false]]] })
#eval check "private re-export" (rejects "E_VISIBILITY" (replaceRoot
  { mod [] [fn "hidden" (.integer "0" {}) false] with
    imports := [⟨["hidden"], "exposed", true, {}⟩] }))
#eval check "cyclic aliases" (rejects "E_CYCLE" (replaceRoot
  { mod [] with imports := [⟨["b"], "a", true, {}⟩, ⟨["a"], "b", true, {}⟩] }))
#eval check "no implicit parent names" (rejects "E_NAME" (replaceRoot
  (mod [] [fn "value" (.integer "0" {})]) [mod ["child"] [fn "test" (.call "value" [] {})]]))
#eval check "descendant private access" ((checkNamespaceProgram (replaceRoot
  (mod [] [fn "value" (.integer "0" {}) false]) [mod ["child"] [fn "test" (.call "super::value" [] {})]])).isOk)

private def generic : Generic := {
  name := "choose", params := [], domain := [[]], span := {}, isPublic := true }
private def method (name : String) : Surface.Method := {
  (fn name (.integer "1" {})).toFunction with requirements := [] }
private def ownerModule : Module := { mod [] with generics := [generic], methods := [method "choose"] }
#eval check "owner method" ((checkNamespaceProgram (replaceRoot ownerModule)).isOk)
#eval check "child has no edit authority" (rejects "E_OWNER" (replaceRoot ownerModule
  [{ mod ["child"] with methods := [method "super::choose"] }]))
#eval check "ordinary functions cannot receive methods" (rejects "E_OWNER" (replaceRoot
  { mod [] [fn "value" (.integer "0" {})] with methods := [method "value"] }))

#eval check "contextual generic module path" ((checkNamespaceProgram (replaceRoot
  (mod [] [fn "main" (.call "generic::value" [] {})])
  [mod ["generic"] [fn "value" (.integer "42" {})]])).isOk)
#eval check "generic remains a reserved function name" (rejects "E_RESERVED" (replaceRoot
  (mod [] [fn "generic" (.integer "0" {})])))
#eval check "contextual name grants no method authority" (rejects "E_OWNER" (replaceRoot
  (mod []) [{ ownerModule with path := ["generic"] },
    { mod ["generic", "child"] with methods := [method "super::choose"] }]))

-- A module may take the name of a geometric operation; every other
-- declaration and the name that a `use` binds may not.
#eval check "geometric operation module paths" (
  ["Affine", "Base", "origin", "id", "compose", "apply", "dimension"].all fun name =>
    (checkNamespaceProgram (replaceRoot
      (mod [] [fn "main" (.call (name ++ "::value") [] {})])
      [mod [name] [fn "value" (.integer "42" {})]])).isOk)
#eval check "dimension remains a reserved function name" (rejects "E_RESERVED" (replaceRoot
  (mod [] [fn "dimension" (.integer "0" {})])))
#eval check "a use cannot bind a geometric operation to a module" (rejects "E_RESERVED" (replaceRoot
  { mod [] [fn "main" (.call "dimension::value" [] {})] with
    imports := [⟨["units", "dimension"], "dimension", false, {}⟩] }
  [mod ["units"], mod ["units", "dimension"] [fn "value" (.integer "42" {})]]))
#eval check "other reserved names are no module names" (
  ["int", "Nat", "QQ", "Point", "self"].all fun name =>
    rejects "E_RESERVED" (replaceRoot (mod []) [mod [name] [fn "value" (.integer "42" {})]]))

-- #759: an indexed spelling is the name that a `use` binds only for a `use`
-- without `as` of an indexed declaration, whose alias is the last segment of
-- its path. A request with `use other::dimension as origin` is refused,
-- although `dimension` is an indexed declaration.
/-- The namespace of `program` with an indexed declaration `dimension` in the
root module of the dependency `other`, `imports` in the root module of the
application, and the modules `extra`. -/
private def withIndexed (imports : List Import) (extra : List Module := []) : Indexed :=
  let base := (replaceRoot { mod [] [fn "main" (.integer "0" {})] with imports } extra).indexed
  let declarations := base.declarations ++ [⟨⟨⟨dependency, []⟩, "dimension"⟩, .indexedDeclaration, true⟩]
  { base with declarations, byOwner := ownerIndex declarations, byScope := scopeIndex declarations }
private def validated (p : Indexed) : Option String :=
  match validate p with
  | .ok () => none
  | .error diagnostic => some diagnostic.code
#eval check "a use without as binds an indexed spelling to an indexed declaration" (
  validated (withIndexed [⟨["other", "dimension"], "dimension", false, {}⟩]) == none &&
    validated (withIndexed [⟨["other", "dimension"], "measure", false, {}⟩]) == none)
#eval check "a use with as binds no indexed spelling, also to an indexed declaration" (
  ["origin", "compose", "id", "Base", "Point", "QQ", "apply", "Affine", "Scheme", "CInfReal"].all fun alias =>
    validated (withIndexed [⟨["other", "dimension"], alias, false, {}⟩]) == some "E_RESERVED")
#eval check "a use without as binds no indexed spelling to a module, with indexed declarations" (
  validated (withIndexed [⟨["units", "dimension"], "dimension", false, {}⟩]
    [mod ["units"], mod ["units", "dimension"] [fn "value" (.integer "42" {})]]) == some "E_RESERVED")

-- #747: an error of the names of a module is at the later of the two
-- bindings in the source, with a note at the earlier one, and not at the
-- declaration of the module. A dependency alias comes first and has no place.
private def place (start line : Nat) : Span := { start, «end» := start + 1, line, column := 1 }
private def placed (name : String) (start line : Nat) : Function :=
  { fn name (.integer "0" {}) with span := place start line }
private def placeOf (p : Program) : Option (String × Span × List Span) :=
  match validate p.indexed with
  | .error d => some (d.code, d.span, d.notes.map (·.span))
  | .ok () => none
private def inModule (m : Module) : Program :=
  replaceRoot { mod [] with span := place 0 1 } [{ m with path := ["a"], span := place 1 2 }]
#eval check "a use after a function of its name" (placeOf (inModule
  { mod [] [placed "q" 10 3] with imports := [⟨["self", "q"], "q", false, place 20 5⟩] }) ==
  some ("E_DUPLICATE", place 20 5, [place 10 3]))
#eval check "a function after a use of its name" (placeOf (inModule
  { mod [] [placed "q" 20 5] with imports := [⟨["self", "f"], "q", false, place 10 3⟩] }) ==
  some ("E_DUPLICATE", place 20 5, [place 10 3]))
#eval check "two uses of one name" (placeOf (inModule
  { mod [] [placed "f" 5 2] with imports := [⟨["self", "f"], "q", false, place 10 3⟩,
    ⟨["self", "f"], "q", false, place 20 4⟩] }) ==
  some ("E_DUPLICATE", place 20 4, [place 10 3]))
#eval check "a function of the name of a dependency alias" (placeOf (inModule
  (mod [] [placed "other" 30 4])) == some ("E_DUPLICATE", place 30 4, []))
#eval check "a child module of the name of a function" (placeOf (replaceRoot
  (mod [] [placed "m" 10 1]) [{ mod ["m"] with span := place 5 1 }]) ==
  some ("E_DUPLICATE", place 10 1, [place 5 1]))
#eval check "a generic before a function of its name" (placeOf (replaceRoot
  { mod [] [placed "g" 20 4] with generics := [{ generic with name := "g", span := place 10 3 }] }) ==
  some ("E_DUPLICATE", place 20 4, [place 10 3]))
#eval check "a reserved name of a function" (placeOf (replaceRoot
  { mod [] [placed "use" 30 3] with span := {} }) == some ("E_RESERVED", place 30 3, []))

private def callback : Program := replaceRoot { mod [] [
  fn "value" (.integer "42" {}),
  fn "main" (.invoke (.ite (.boolean true {}) (.mk [] (.variable "value" {}) {})
    (.mk [] (.variable "aliasValue" {}) {}) {}) [] {})] with
  imports := [⟨["value"], "aliasValue", false, {}⟩] }
#eval check "aliases share the same static target" ((checkNamespaceProgram callback true).isOk)

#eval check "alias hits preserve scope, span independence and the original logical charge" (Id.run do
  let child := {mod ["child"] [fn "value" (.integer "7" {})] with
    imports := [⟨["self", "value"], "aliasValue", false, {}⟩]}
  let p := (replaceRoot callback.packages[0]!.modules[0]! [child]).indexed
  let scope : Scope := ⟨root, []⟩
  let other : Scope := ⟨root, ["child"]⟩
  let session : QuerySession := {index := p}
  let path := ["aliasValue"]
  let later : Span := {line := 99, column := 15}
  let .ok (first, s) := session.query scope path {} | return false
  let .ok (again, t) := s.query scope path later | return false
  let .ok (distinct, u) := t.query other path later | return false
  return first == again && again != distinct && s.hits == 0 && t.hits == 1 && u.hits == 1 &&
    s.units.val > 2 && t.units.val == 2 * s.units.val &&
    (resolve p scope path later).toOption == some again &&
    (resolve p other path later).toOption == some distinct)
#eval check "unused invalid dependency body" (rejects "E_TYPE" { program with packages :=
  [program.packages[0]!, pkg dependency [mod [] [fn "value" (.integer "42" {}), fn "bad" (.boolean true {})]]] })
#eval check "unused lambda capture" (rejects "E_CAPTURE" (replaceRoot (mod [] [{
  fn "bad" (.integer "0" {}) with body := (.mk [
    .letE "outside" none (.integer "1" {}) {},
    .letE "callback" none (.lambda [] int (.mk [] (.variable "outside" {}) {}) {}) {}]
    (.integer "0" {}) {}) }])))

private def ref : Reference := {
  scope := ⟨root, []⟩, path := ["other", "value"], span := {},
  target := ⟨⟨⟨dependency, []⟩, "value"⟩, .function, true⟩ }
private def ledger (r : Reference) : Lowered := {
  surface := { version := 2, file := "", functions := [], generics := [], methods := [] }, references := [r] }
#eval check "real reference audit" (decide (ReferencesValid program.indexed (ledger ref)))
#eval check "forged owner" (!decide (ReferencesValid program.indexed (ledger
  { ref with target := { ref.target with owner := ⟨⟨root, []⟩, "value"⟩ } })))
#eval check "forged visibility" (!decide (ReferencesValid program.indexed (ledger
  { ref with target := { ref.target with isPublic := false } })))
#eval check "forged edit authority" (!decide (ReferencesValid program.indexed (ledger { ref with method := true })))
#eval check "forged reference path" (!decide (ReferencesValid program.indexed (ledger { ref with path := ["absent"] })))
#eval check "SemVer" (validVersion "1.2.3-alpha.1+build.01" && !validVersion "1.2" && !validVersion "1.2.3-01")

-- Without completed-node memoization this tiny DAG has 2^40 traversal paths.
private def sharedGraph : Program := {
  file := "shared graph", root := "/0/Vastitas.toml"
  packages := (List.range 40).map fun i => {
    id := ⟨s!"/{i}/Vastitas.toml", "shared", "0.1.0"⟩, modules := [mod []]
    dependencies := if i == 39 then [] else
      [⟨"left", s!"/{i+1}/Vastitas.toml"⟩, ⟨"right", s!"/{i+1}/Vastitas.toml"⟩] } }
#eval check "shared dependency DAG stays bounded" ((checkNamespaceProgram sharedGraph).isOk)
#eval check "shared graph still detects cycles" (rejects "E_CYCLE" {
  sharedGraph with packages := sharedGraph.packages.map fun pkg =>
    if pkg.id.source == "/39/Vastitas.toml" then
      { pkg with dependencies := [⟨"cycle", sharedGraph.root⟩] } else pkg })

private def sharedImports : Program := replaceRoot { mod [] with
  imports := ⟨["self"], "a0", false, {}⟩ :: (List.range 30).map fun i =>
    ⟨[s!"a{i}", s!"a{i}"], s!"a{i+1}", false, {}⟩ }
#eval check "total import work is bounded" (rejects "E_LIMIT" sharedImports)
#eval check "dependency aliases cannot be shadowed" (rejects "E_SHADOW" (replaceRoot
  (mod [] [{ fn "main" (.integer "0" {}) with
    body := .mk [.letE "other" none (.integer "1" {}) {}] (.variable "other" {}) {} }])))
#eval check "self retains private module visibility" (rejects "E_VISIBILITY" (replaceRoot (mod [])
  [{ mod ["hidden"] with isPublic := false, imports := [⟨["self"], "exposed", true, {}⟩] }]))
#eval check "super retains private module visibility" (rejects "E_VISIBILITY" (replaceRoot (mod [])
  [{ mod ["hidden"] with isPublic := false },
   { mod ["hidden", "child"] with imports := [⟨["super"], "exposed", true, {}⟩] }]))


private def abstractDecl (name : String) (parents : List String := []) : AbstractType := {
  name, parents := parents.map fun name => ⟨name.splitOn "::", {}⟩, span := {}, isPublic := true }
private def subtype (scalar target : String) : RawSubtype := {
  scalar, target := ⟨target.splitOn "::", {}⟩, span := {} }
private def inherited (scalar : String) (authorized := true) : Program := {
  program with extended := true, packages := [
    { program.packages[0]! with modules := [{
      mod [] with
      abstractTypes := [abstractDecl "Child" ["alias::Parent"]]
      subtypes := [subtype scalar "Child"] }] },
    pkg dependency [{ mod [] [fn "value" (.integer "42" {})] with
      abstractTypes := [abstractDecl "Parent"],
      subtypes := if authorized then [subtype "Int" "Parent"] else [] }] ] }
#eval check "foreign inheritance reuses owner membership" ((checkNamespaceProgram (inherited "Int")).isOk)
#eval check "foreign inheritance cannot introduce membership" (rejects "E_OWNER" (inherited "Nat"))
#eval check "removing owner support revalidates closure" (rejects "E_OWNER" (inherited "Int" false))
#eval check "independent authority audit rejects indirect extension" (match membershipGraph (inherited "Nat").indexed with
  | .error _ => false
  | .ok graph => !decide (MembershipsAuthorized graph))

end VastitasKernel.Namespace.Regression
