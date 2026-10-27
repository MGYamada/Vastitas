import VastitasKernel.NamespaceChecker
import VastitasKernel.NamespaceProtocol
import VastitasKernel.Codegen

namespace VastitasKernel.Namespace.Regression

private def root : PackageId := ⟨"/app/Vastitas.toml", "app", "0.1.0"⟩
private def dependency : PackageId := ⟨"/lib/Vastitas.toml", "lib", "0.1.0"⟩
private def int : Surface.TypeExpr := .data (.named "Int")
private def fn (name : String) (value : Surface.Expr) (pub := true) : Function := {
  name, params := [], result := int, body := .mk [] value {}, span := {}, isPublic := pub }
private def mod (path : List String) (functions : List Function := []) : Module := {
  path, functions, generics := [], methods := [], imports := [], span := {}, isPublic := true }
private def pkg (id : PackageId) (modules : List Module) : Package := { id, modules, dependencies := [] }
private def program : Program := {
  file := "namespace-regression", root := root.source
  packages := [
    { pkg root [mod [] [fn "main" (.call "other::value" [] {})]] with
      dependencies := [⟨"other", dependency.source⟩, ⟨"alias", dependency.source⟩] },
    pkg dependency [mod [] [fn "value" (.integer "42" {})]] ] }
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"namespace regression failed: {name}")
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

private def callback : Program := replaceRoot { mod [] [
  fn "value" (.integer "42" {}),
  fn "main" (.invoke (.ite (.boolean true {}) (.mk [] (.variable "value" {}) {})
    (.mk [] (.variable "aliasValue" {}) {}) {}) [] {})] with
  imports := [⟨["value"], "aliasValue", false, {}⟩] }
#eval check "aliases share the same static target" ((checkNamespaceProgram callback true).isOk)
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

end VastitasKernel.Namespace.Regression
