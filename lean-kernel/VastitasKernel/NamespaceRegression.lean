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
  (resolve program ⟨root, []⟩ ["other", "value"] {}).toOption ==
  (resolve program ⟨root, []⟩ ["alias", "value"] {}).toOption)
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
#eval check "real reference audit" (decide (ReferencesValid program (ledger ref)))
#eval check "forged owner" (!decide (ReferencesValid program (ledger
  { ref with target := { ref.target with owner := ⟨⟨root, []⟩, "value"⟩ } })))
#eval check "forged visibility" (!decide (ReferencesValid program (ledger
  { ref with target := { ref.target with isPublic := false } })))
#eval check "forged edit authority" (!decide (ReferencesValid program (ledger { ref with method := true })))
#eval check "forged reference path" (!decide (ReferencesValid program (ledger { ref with path := ["absent"] })))
#eval check "SemVer" (validVersion "1.2.3-alpha.1+build.01" && !validVersion "1.2" && !validVersion "1.2.3-01")

end VastitasKernel.Namespace.Regression
