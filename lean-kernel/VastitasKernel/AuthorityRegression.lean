import VastitasKernel.Authority
import VastitasKernel.RegressionSupport

/-! The assembler `Authority.assemble`, which the public route runs through
`AuthoritySource`, on a Lean value: its acceptance and the independent audits
of its trace state. Public JSON acceptance is covered by
VastitasPublicTest.AuthorityRegression. -/
namespace VastitasKernel.Authority.Regression
open Namespace
private def app : PackageId := ⟨"/app/Vastitas.toml", "app", "0.1.0"⟩
private def base : PackageId := ⟨"/base/Vastitas.toml", "base", "0.1.0"⟩
private def addon : PackageId := ⟨"/addon/Vastitas.toml", "addon", "0.1.0"⟩
private def int : Surface.TypeExpr := .data (.named "Int")
private def method (name selector : String) : Surface.Method := {
  name, params := [{ name := "x", ty := .data (.named selector), span := {} }], result := int,
  body := .mk [] (.integer "42" {}) {}, span := {}, requirements := [] }
private def emptyModule : Namespace.Module := {
  path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }
private def events : List EditEvent := [
  .borrow ["base", "outer"] "parent" {},
  .reborrow "parent" ["addon", "inner"] "child" {},
  .apply ["addon", "ops", "sum"] (some "child") {},
  .release "child" {}, .release "parent" {},
  .transfer ["base", "handoff"] {}, .seal ["base", "choose"] {} ]
private def program : Namespace.Program := {
  authority := true, editable := true, extended := true, file := "authority-regression", root := app.source
  packages := [
    {
      id := app, dependencies := [⟨"base", base.source⟩, ⟨"addon", addon.source⟩]
      modules := [{ emptyModule with
        assembly := some ⟨events, {}⟩
        functions := [{
          name := "main", params := [], result := int,
          body := .mk [] (.call "base::choose" [.integer "0" {}] {}) {}, span := {}, isPublic := true }] }] },
    { id := base, dependencies := [], modules := [{ emptyModule with
      generics := [{ name := "choose", params := [⟨"x", {}⟩], domain := [[.named "Int"]], span := {}, isPublic := true }]
      methods := [method "choose" "Number"]
      grants := [{
        name := "outer", target := ["choose"], granteePackage := .source addon.source,
        granteePath := [], region := [["Int"]], delegable := true, span := {}, isPublic := true }]
      transfers := [{
        name := "handoff", target := ["choose"], granteePackage := .source addon.source,
        granteePath := [], span := {}, isPublic := true }] }] },
    { id := addon, dependencies := [⟨"base", base.source⟩], modules := [
      { emptyModule with delegations := [{
        name := "inner", target := ["base", "choose"],
        granteePackage := .source addon.source, granteePath := ["ops"], region := [["Int"]], span := {}, isPublic := true }] },
      { emptyModule with path := ["ops"], contributions := [{
        name := "sum", target := ["base", "choose"],
        methods := [method "base::choose" "Int"], span := {}, isPublic := true }] }] }] }
private def check := RegressionSupport.check "authority regression failed"
private def rejects (result : Except Diagnostic α) (code : String) : Bool :=
  match result with
  | .ok _ => false
  | .error diagnostic => diagnostic.code == code

#eval check "authority assembly acceptance" ((assemble program.indexed).isOk)

/-- A borrow with no edits still belongs to its enclosing family. The old
trace discipline alone accepted a borrow/return of choose sealed as other. -/
private def twoFamilies (trace : List EditEvent) : Namespace.Program :=
  { program with packages := program.packages.map fun pkg =>
    { pkg with modules := pkg.modules.map fun m =>
      if pkg.id == app then { m with assembly := some ⟨trace, {}⟩ }
      else if pkg.id == base then { m with
        generics := m.generics ++ [{ m.generics.head! with name := "other" }],
        methods := m.methods ++ [method "other" "Number"] }
      else m } }

private def borrowOnly : List EditEvent :=
  [.borrow ["base", "outer"] "loan" {}, .release "loan" {}]
#eval check "two blocks with independent family identities" ((assemble (twoFamilies
  (borrowOnly ++ [.seal ["base", "choose"] {}, .seal ["base", "other"] {}])).indexed).isOk)
#eval check "borrow cannot be hidden in another family block" (rejects (assemble (twoFamilies
  (borrowOnly ++ [.seal ["base", "other"] {}, .seal ["base", "choose"] {}])).indexed) "E_ASSEMBLY")
#eval check "trailing borrow must belong to a sealed block" (rejects (assemble
  (twoFamilies borrowOnly).indexed) "E_ASSEMBLY")

private def auditActive (test : Prepared program.indexed → State → Bool) : Bool :=
  match prepare program.indexed with
  | .error _ => false
  | .ok prepared => match runTrace program.indexed prepared (events.take 2) {} with
    | .error _ => false
    | .ok state => test prepared state

#eval check "forged parent link rejected independently" (auditActive fun prepared state =>
  let child := state.loans.head!
  let forged := { state with loans := { child with parent := none } :: state.loans.tail }
  rejects (runTrace program.indexed prepared [] forged) "E_INTERNAL_AUTHORITY")
#eval check "forged delegation region rejected independently" (auditActive fun prepared state =>
  let child := state.loans.head!
  let forged := { child with chain := child.chain.map fun grant => { grant with region := [] } }
  rejects (runTrace program.indexed prepared [] { state with loans := forged :: state.loans.tail }) "E_INTERNAL_AUTHORITY")
#eval check "parent cannot be returned ahead of child" (auditActive fun prepared state =>
  rejects (runTrace program.indexed prepared [.release "parent" {}] state) "E_BORROW")
#eval check "transfer cannot erase active descendants" (auditActive fun prepared state =>
  rejects (runTrace program.indexed prepared [.transfer ["base", "handoff"] {}] state) "E_BORROW")
#eval check "forged transfer recipient fails full correspondence" (match prepare program.indexed with
  | .error _ => false
  | .ok prepared =>
    let forged := { prepared with transfers := prepared.transfers.map fun transfer => { transfer with recipient := ⟨app, []⟩ } }
    !decide (DeclarationsCorrespond program.indexed forged))
#eval check "invented transfer history fails independent state audit" (match prepare program.indexed with
  | .error _ => false
  | .ok prepared =>
    let transfer := { prepared.transfers.head! with id := ⟨⟨addon, []⟩, "forged"⟩ }
    rejects (runTrace program.indexed prepared [] { history := [transfer] }) "E_INTERNAL_AUTHORITY")
#eval check "trace audit work is charged before each audit (#553)" (match prepare program.indexed with
  | .error _ => false
  | .ok prepared =>
    -- The empty initial state alone costs more than one unit.
    rejects (runTraceWith program.indexed prepared events {} 1) "E_LIMIT" &&
      rejects (runTraceWith program.indexed prepared [] {} 1) "E_LIMIT" &&
      (runTraceWith program.indexed prepared events {} Limits.authorityTraceWork).isOk)

end VastitasKernel.Authority.Regression
