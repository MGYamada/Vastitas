import VastitasKernel.FunctionChecker
import VastitasKernel.Codegen

namespace VastitasKernel.Contracts.Regression
private def path (name : String) : TypePath := ⟨[name], {}⟩
private def param (name ty : String) : RawParam := ⟨name, .named ty, {}⟩
private def contract (result : RawType := .named "Int") : RawAbstractMethod := {
  name := "f", params := [param "x" "Numeric"], returnType := result
  requirements := [], domain := [[path "Numeric"]], span := {} }
private def method (ty : String) (body : RawExpr) : RawMethod := {
  name := "f", params := [param "x" ty], returnType := .named "Int"
  requirements := [], body := .mk [] body {}, span := {} }
private def program : RawProgram := {
  version := 4, file := "contracts"
  functions := [{
    name := "main", params := [], returnType := .named "Int", span := {}
    body := .mk [] (.call "f" [.integer "42" {}] {}) {} }]
  generics := [{ name := "f", params := [⟨"x", {}⟩], domain := [], span := {} }]
  methods := [method "Nat" (.call "int" [.variable "x" {}] {}), method "Int" (.variable "x" {})]
  abstractTypes := [⟨"Numeric", [], {}⟩, ⟨"Empty", [], {}⟩]
  subtypes := [⟨"Nat", path "Numeric", {}⟩, ⟨"Int", path "Numeric", {}⟩]
  abstractMethods := [contract] }
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"abstract contract regression failed: {name}")
private def rejects (code : String) (p : RawProgram) : Bool :=
  match checkProgram p with
  | .error diagnostic => diagnostic.code == code
  | .ok _ => false

#eval check "actual checker and codegen" (match checkProgram program with
  | .ok checked => (Codegen.generate checked).isOk
  | .error _ => false)
#eval check "contract is not an executable candidate" (rejects "E_DISPATCH_COVERAGE" { program with methods := [] })
#eval check "selected result mismatch" (rejects "E_CONTRACT_RESULT" { program with abstractMethods := [contract (.named "Nat")] })
#eval check "overlaps require every result" (rejects "E_CONTRACT_RESULT" {
  program with abstractMethods := [contract, contract (.named "Nat")] })
#eval check "empty clause rejected" (rejects "E_CONTRACT_EMPTY" {
  program with abstractMethods := [{ contract with domain := [[path "Empty"]] }] })
#eval check "explicit empty allowed" ((checkProgram {
  program with functions := [], abstractMethods := [{ contract with domain := [] }], methods := [] }).isOk)
#eval check "domain must satisfy selector" (rejects "E_CONTRACT_DOMAIN" {
  program with abstractMethods := [{ contract with domain := [[path "Bool"]] }] })
#eval check "missing generic rejected" (rejects "E_NAME" { program with generics := [] })
#eval check "duplicate parameters rejected" (rejects "E_DUPLICATE" {
  program with abstractMethods := [{ contract with params := [param "x" "Int", param "x" "Int"] }] })
#eval check "legacy cannot carry contracts" (rejects "E_PROTOCOL" { program with version := 2 })
#eval check "domain-external body audited" (rejects "E_TYPE" {
  program with methods := program.methods ++ [method "Bool" (.variable "x" {})] })
#eval check "raw abstract value result rejected" (rejects "E_TYPE" {
  program with abstractMethods := [contract (.named "Numeric")] })

end VastitasKernel.Contracts.Regression
