import VastitasKernel.FunctionChecker
import VastitasKernel.Codegen

/-! Executable adversarial checks against the actual Stage 1b acceptance path
and its independent static-signature audit, without the Rust frontend. -/
namespace VastitasKernel.Surface.Regression

private def int : TypeExpr := .data (.named "Int")
private def bool : TypeExpr := .data (.named "Bool")
private def unary (ty : TypeExpr) : TypeExpr := .function [ty] int
private def block (expr : Expr) : Block := .mk [] expr {}
private def identity : Function := {
  name := "identity", params := [{ name := "x", ty := int, span := {} }], result := int
  body := block (.variable "x" {}), span := {} }
private def main (expr : Expr) : Function := {
  name := "main", params := [], result := int, body := block expr, span := {} }
private def program (functions : List Function) : Program := {
  version := 2, file := "function-regression.vast", functions, generics := [], methods := [] }
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"function regression failed: {name}")
private def rejects (code : String) (p : Program) : Bool :=
  match checkSurfaceProgram p with
  | .error error => error.code == code
  | .ok _ => false

#eval check "named function invocation" (match checkSurfaceProgram (program [identity,
    main (.invoke (.variable "identity" {}) [.integer "42" {}] {})]) true with
  | .ok checked => (Codegen.generate checked).isOk
  | .error _ => false)

private def captured : Program := program [{ main (.integer "0" {}) with
  body := .mk [
    .letE "outside" none (.integer "1" {}) {},
    .letE "callback" none (.lambda [] int (block (.variable "outside" {})) {}) {}]
    (.integer "0" {}) {} }]
#eval check "actual capture rejection" (rejects "E_CAPTURE" captured)
#eval check "independent capture predicate" (!decide (CaptureFree captured))

#eval check "unused invalid lambda" (rejects "E_TYPE" (program [main (.block (.mk [
  .letE "unused" none (.lambda [] int (block (.boolean true {})) {}) {}]
  (.integer "0" {}) {}) {})]))

#eval check "old protocol version" (rejects "E_PROTOCOL" { program [identity] with version := 1 })
#eval check "forged lifted reference" (rejects "E_RESERVED" (program [main (.reference "__vastitas_l0" {})]))
#eval check "Fn is reserved" (rejects "E_RESERVED" (program [{ identity with name := "Fn" }]))
#eval check "main before function erasure" (rejects "E_MAIN" (program [{
  main (.integer "0" {}) with params := [{ name := "f", ty := unary int, span := {} }] }]))

private def ledger (call : StaticCall) : Lowered := {
  module := { version := 1, file := "ledger", functions := [] }, definitions := [identity], calls := [call] }
#eval check "valid static target" (decide (StaticCallsValid (ledger { target := "identity", signature := unary int })))
#eval check "forged signature with same arity" (!decide (StaticCallsValid (ledger { target := "identity", signature := unary bool })))
#eval check "unknown static target" (!decide (StaticCallsValid (ledger { target := "absent", signature := unary int })))
#eval check "erased argument type mismatch" (!decide (StaticCallsValid (ledger {
  target := "identity", signature := unary int, bindings := [(unary bool, { name := "identity", ty := unary int })] })))
#eval check "erased argument unknown implementation" (!decide (StaticCallsValid (ledger {
  target := "identity", signature := unary int, bindings := [(unary int, { name := "absent", ty := unary int })] })))

end VastitasKernel.Surface.Regression
