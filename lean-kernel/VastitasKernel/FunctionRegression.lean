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

private def shadowing : Program := program [{ main (.integer "0" {}) with
  body := .mk [
    .letE "outside" none (.integer "1" {}) {},
    .letE "callback" none (.lambda [{ name := "outside", ty := int, span := {} }]
      int (block (.variable "outside" {})) {}) {}]
    (.integer "0" {}) {} }]
#eval check "actual enclosing shadow rejection" (rejects "E_SHADOW" shadowing)
#eval check "capture-free does not imply shadow-free" (decide (CaptureFree shadowing) && !decide (LambdaShadowFree shadowing))

#eval check "unused invalid lambda" (rejects "E_TYPE" (program [main (.block (.mk [
  .letE "unused" none (.lambda [] int (block (.boolean true {})) {}) {}]
  (.integer "0" {}) {}) {})]))

#eval check "old protocol version" (rejects "E_PROTOCOL" { program [identity] with version := 1 })
#eval check "forged lifted reference" (rejects "E_RESERVED" (program [main (.reference (.lambda 0) {})]))
#eval check "Fn is reserved" (rejects "E_RESERVED" (program [{ identity with name := "Fn" }]))
#eval check "main before function erasure" (rejects "E_MAIN" (program [{
  main (.integer "0" {}) with params := [{ name := "f", ty := unary int, span := {} }] }]))

private def ledger (call : StaticCall) : Lowered := {
  module := { version := 1, file := "ledger", functions := [] }, definitions := [{ toFunction := identity, id := .source "identity" }], calls := [call] }
#eval check "valid static target" (decide (StaticCallsValid (ledger { target := .source "identity", signature := unary int })))
#eval check "forged signature with same arity" (!decide (StaticCallsValid (ledger { target := .source "identity", signature := unary bool })))
#eval check "unknown static target" (!decide (StaticCallsValid (ledger { target := .source "absent", signature := unary int })))
#eval check "erased argument type mismatch" (!decide (StaticCallsValid (ledger {
  target := .source "identity", signature := unary int, bindings := [(unary bool, { name := .concrete (.source "identity"), ty := unary int })] })))
#eval check "erased argument unknown implementation" (!decide (StaticCallsValid (ledger {
  target := .source "identity", signature := unary int, bindings := [(unary int, { name := .concrete (.source "absent"), ty := unary int })] })))

#eval check "audit probe cannot be an executable argument" (!decide (StaticCallsValid (ledger {
  target := .source "identity", signature := unary int,
  bindings := [(unary int, { name := .probe 0, ty := unary int })] })))

-- Matching printed names cannot forge a different kind of internal identity.
private def forgedIdentity : Lowered := {
  module := { version := 1, file := "ledger", functions := [] }
  definitions := [{ toFunction := identity, id := .source "__vastitas_l0" }]
  calls := [{ target := .lambda 0, signature := unary int }] }
#eval check "rendered name does not establish identity" (!decide (StaticCallsValid forgedIdentity))

-- Plain calls now receive the same static-signature audit as higher-order calls.
private def firstOrder := program [identity, main (.call "identity" [.integer "42" {}] {})]
#eval check "ordinary call ledger and raw compatibility" (match lowerFunctions firstOrder, firstOrder.legacy with
  | .ok lowered, some raw =>
    !lowered.calls.isEmpty && decide (StaticCallsValid lowered) &&
      match checkProgram raw true, checkSurfaceProgram firstOrder true with
      | .ok left, .ok right => reprStr left.val == reprStr right.val
      | _, _ => false
  | _, _ => false)

#eval check "indexed audit rejects forged signature" (!staticCallsValid (ledger {
  target := .source "identity", signature := unary bool }))
#eval check "indexed audit accepts actual signature" (staticCallsValid (ledger {
  target := .source "identity", signature := unary int }))
#eval check "indexed audit rejects probe binding" (!staticCallsValid (ledger {
  target := .source "identity", signature := unary int,
  bindings := [(unary int, { name := .probe 0, ty := unary int })] }))

end VastitasKernel.Surface.Regression
