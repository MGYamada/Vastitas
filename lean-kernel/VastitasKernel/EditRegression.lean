import VastitasKernel.Edit

namespace VastitasKernel.Edit.Regression
open Namespace

private def app : PackageId := ⟨"/app/Vastitas.toml", "app", "0.1.0"⟩
private def base : PackageId := ⟨"/base/Vastitas.toml", "base", "0.1.0"⟩
private def addon : PackageId := ⟨"/addon/Vastitas.toml", "addon", "0.1.0"⟩
private def int : Surface.TypeExpr := .data (.named "Int")
private def parameter (name selector : String) : Surface.Param :=
  { name, ty := .data (.named selector), span := {} }
private def method (name selector : String) (body : Surface.Expr) : Surface.Method := {
  name, params := [parameter "x" selector, parameter "y" selector], result := int,
  body := .mk [] body {}, span := {}, requirements := [] }
private def addition : Surface.Method :=
  method "base::choose" "Int" (.binary "+" (.variable "x" {}) (.variable "y" {}) {})
private def rootModule : Namespace.Module := {
  path := [], isPublic := true, imports := [], generics := [], methods := [], span := {}
  functions := [{
    name := "main", params := [], result := int
    body := .mk [] (.call "base::choose" [.integer "40" {}, .integer "2" {}] {}) {},
    span := {}, isPublic := true }] }
private def events : List EditEvent := [
  .borrow ["base", "integers"] "edit" {},
  .apply ["addon", "sum"] (some "edit") {},
  .release "edit" {}, .seal ["base", "choose"] {} ]
private def program (region : List (List String) := [["Int", "Int"]])
    (trace := events) : Namespace.Program := {
  editable := true, extended := true, file := "edit-regression", root := app.source
  packages := [
    {
      id := app, dependencies := [⟨"base", base.source⟩, ⟨"addon", addon.source⟩, ⟨"diamond", addon.source⟩]
      modules := [{ rootModule with assembly := some ⟨trace, {}⟩ }] },
    { id := base, dependencies := [], modules := [{ rootModule with
      functions := []
      generics := [{
        name := "choose", params := [⟨"x", {}⟩, ⟨"y", {}⟩]
        domain := [[.named "Int", .named "Int"]], span := {}, isPublic := true }]
      methods := [method "choose" "Number" (.integer "0" {})]
      grants := [{
        name := "integers", target := ["choose"], granteeSource := addon.source
        granteePath := [], region, span := {}, isPublic := true }] }] },
    { id := addon, dependencies := [⟨"base", base.source⟩], modules := [{ rootModule with
      functions := []
      contributions := [{
        name := "sum", target := ["base", "choose"]
        methods := [addition], span := {}, isPublic := true }] }] }] }

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"edit regression failed: {name}")
private def rejects (code : String) (p : Namespace.Program) : Bool :=
  match checkEditProgram p with
  | .ok _ => false
  | .error diagnostic => diagnostic.code == code

private def withoutAssembly : Namespace.Program :=
  let p := program
  { p with packages := p.packages.map fun pkg =>
      if pkg.id == app then { pkg with modules := pkg.modules.map fun m => { m with assembly := none } }
      else pkg }

#eval check "omitted assembly uses the same empty-trace audits" ((checkEditProgram withoutAssembly true).isOk)
#eval check "omitted assembly still rejects invalid unused grant" (rejects "E_OWNER"
  { withoutAssembly with packages := withoutAssembly.packages.map fun pkg =>
      { pkg with modules := pkg.modules.map fun m =>
          { m with grants := m.grants.map fun g => { g with granteePath := ["absent"] } } } })
#eval check "omitted assembly still checks unapplied bodies" (rejects "E_TYPE"
  { withoutAssembly with packages := withoutAssembly.packages.map fun pkg =>
      { pkg with modules := pkg.modules.map fun m =>
          { m with contributions := m.contributions.map fun c =>
              { c with methods := c.methods.map fun method =>
                  { method with result := .data (.named "Bool") } } } } })

#eval check "external edit accepted by actual checker" ((checkEditProgram (program) true).isOk)
#eval check "legacy checker cannot skip assembly" (match checkNamespaceProgram (program) with
  | .error diagnostic => diagnostic.code == "E_PROTOCOL"
  | .ok _ => false)
#eval check "all-key footprint is independently authorized" (rejects "E_IMPACT" (program [["Nat", "Nat"]]))
#eval check "loan overlap" (rejects "E_BORROW" (program [["Int", "Int"]]
  [.borrow ["base", "integers"] "a" {}, .borrow ["base", "integers"] "b" {}]))
#eval check "double return" (rejects "E_BORROW" (program [["Int", "Int"]]
  [.borrow ["base", "integers"] "a" {}, .release "a" {}, .release "a" {}]))
#eval check "diamond replay is idempotent" ((checkEditProgram (program [["Int", "Int"]]
  [.borrow ["base", "integers"] "edit" {}, .apply ["addon", "sum"] (some "edit") {},
   .apply ["diamond", "sum"] (some "edit") {}, .release "edit" {}, .seal ["base", "choose"] {}])).isOk)

#eval check "redirected lowered body fails full source correspondence" (match prepare (program).indexed with
  | .error _ => false
  | .ok prepared =>
    let contribution := prepared.contributions.head!
    let forged := { contribution with methods := [{ contribution.methods.head! with
      body := .mk [] (.call "redirected" [] {}) {} }] }
    !decide (ContributionsCorrespond (program).indexed { prepared with contributions := [forged] }))

#eval check "forged grant origin fails declaration correspondence" (match prepare (program).indexed with
  | .error _ => false
  | .ok prepared =>
    let grant := prepared.grants.head!
    let forged := { grant with id := { grant.id with scope := ⟨app, []⟩ } }
    !decide (GrantsCorrespond (program).indexed { prepared with grants := [forged] }))

#eval check "same ID and grant cannot replay a changed body" (match prepare (program).indexed with
  | .error _ => false
  | .ok prepared =>
    let grant := prepared.grants.head!
    let contribution := prepared.contributions.head!
    let forged := { contribution with methods := [{ contribution.methods.head! with
      body := .mk [] (.integer "99" {}) {} }] }
    let state : State := {
      loans := [{ name := "edit", grant }]
      usedLoans := ({} : Std.HashSet String).insert "edit"
      applied := [{ contribution := forged, grant := some grant.id, region := some grant.region }] }
    match runTrace (program).indexed prepared [.apply ["addon", "sum"] (some "edit") {}] state with
    | .error diagnostic => diagnostic.code == "E_INTERNAL_ASSEMBLY"
    | .ok _ => false)

#eval check "forged active grant region fails state provenance" (match prepare (program).indexed with
  | .error _ => false
  | .ok prepared =>
    let grant := { prepared.grants.head! with region := [] }
    let state : State := {
      loans := [{ name := "edit", grant }]
      usedLoans := ({} : Std.HashSet String).insert "edit" }
    !decide (StateValid prepared state))

end VastitasKernel.Edit.Regression

