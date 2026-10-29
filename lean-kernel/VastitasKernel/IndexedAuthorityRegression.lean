import VastitasKernel.IndexedAuthorityCheck
import VastitasKernel.IndexedFunctionRegression

namespace VastitasKernel.Indexed.AuthoritySource.Regression
open DispatchSource FunctionSource

private def app : Namespace.PackageId := ⟨"/authority-app/Vastitas.toml", "app", "1.0.0"⟩
private def base : Namespace.PackageId := ⟨"/authority-base/Vastitas.toml", "base", "1.0.0"⟩
private def addon : Namespace.PackageId := ⟨"/authority-addon/Vastitas.toml", "addon", "1.0.0"⟩
private def geo := Source.Regression.declarationFixture.packages[1]!
private def path (name : String) : Source.Path := ⟨name.splitOn "::", {}⟩
private def int : FnType := .data (.pure .int)
private def num (n : Nat) : Expr := .integer (toString n) {}
private def var (name : String) : Expr := .variable name {}
private def call (name : String) (args : List Expr := []) : Expr := .call (path name) args {}
private def block (value : Expr) (statements : List Stmt := []) : Block := .mk statements value {}
private def fn (name : String) (body : Block) (isPublic := false) : FunctionSource.Function :=
  ⟨name, [], int, body, isPublic, {}⟩
private def method (target selector : String) (body : Block) : Method := {
  target := path target, params := [⟨"x", .data (.named selector), {}⟩], result := .int, requirements := [], body }
private def mod : DispatchSource.Module := {
  module := { path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} },
  declarations := [] }
private def events : List Namespace.EditEvent := [
  .borrow ["base", "outer"] "parent" {}, .reborrow "parent" ["addon", "inner"] "child" {},
  .apply ["addon", "ops", "sum"] (some "child") {}, .release "child" {}, .release "parent" {},
  .transfer ["base", "handoff"] {}, .seal ["base", "choose"] {} ]
private def contributionBody := block (.invoke
  (.lambda [⟨"n", int, {}⟩] int (block (.binary "+" (var "n") (call "helper") {})) {}) [var "x"] {})
private def unusedBody := block (.invoke
  (.lambda [⟨"n", int, {}⟩] int (block (call "helper")) {}) [num 0] {})

/-- The generic's defining owner and the contributor's lexical source scope
are different. A private helper uses declaration-based geometry inside a lambda. -/
def authorityFixture : DispatchSource.Program := {
  file := "indexed-authority", root := app.source, extended := true, editable := true, authority := true,
  packages := [
    ⟨app, [⟨"base", base.source⟩, ⟨"addon", addon.source⟩], [{ mod with
      module := { mod.module with assembly := some ⟨events, {}⟩ },
      functions := [fn "main" (block (call "base::choose" [num 38])) true] }]⟩,
    ⟨base, [], [{ mod with
      module := { mod.module with
        generics := [{ name := "choose", params := [⟨"x", {}⟩], domain := [[.named "Int"]], span := {}, isPublic := true }],
        grants := [{
          name := "outer", target := ["choose"], granteeSource := addon.source,
          granteePath := [], region := [["Int"]], delegable := true, span := {}, isPublic := true }],
        transfers := [{
          name := "handoff", target := ["choose"], granteeSource := addon.source,
          granteePath := [], span := {}, isPublic := true }] },
      functions := [fn "helper" (block (num 100))],
      methods := [method "choose" "Number" (block (num 5))],
      contributions := [⟨"own", path "choose", [method "choose" "Nat" (block (num 6))], {}, true⟩] }]⟩,
    ⟨addon, [⟨"base", base.source⟩, ⟨"geo", geo.id.source⟩], [
      { mod with
        module := { mod.module with
          delegations := [{
            name := "inner", target := ["base", "choose"], granteeSource := addon.source,
            granteePath := ["ops"], region := [["Int"]], span := {}, isPublic := true }] },
        contributions := [⟨"post", path "base::choose", [method "base::choose" "Nat" (block (num 7))], {}, true⟩] },
      { mod with
        module := { mod.module with path := ["ops"] },
        functions := [fn "helper" (block (call "int" [call "geo::dimension" [call "geo::Affine" [num 4]]]))],
        contributions := [
          ⟨"sum", path "base::choose", [method "base::choose" "Int" contributionBody], {}, true⟩,
          ⟨"unused", path "base::choose", [method "base::choose" "Number" unusedBody], {}, true⟩] } ]⟩,
    ⟨geo.id, geo.dependencies, geo.modules.map fun m => { module := m.module, declarations := m.declarations }⟩ ] }

private def changeModule (p : DispatchSource.Program) (owner : Namespace.PackageId) (modulePath : List String)
    (change : DispatchSource.Module → DispatchSource.Module) : DispatchSource.Program :=
  { p with packages := p.packages.map fun pkg => { pkg with modules := pkg.modules.map fun m =>
    if pkg.id == owner && m.module.path == modulePath then change m else m } }
private def withEvents (p : DispatchSource.Program) (events : List Namespace.EditEvent) : DispatchSource.Program :=
  changeModule p app [] fun m => { m with module := { m.module with assembly := some ⟨events, {}⟩ } }
private def changeContribution (p : DispatchSource.Program) (name : String) (change : Method → Method) : DispatchSource.Program :=
  changeModule p addon ["ops"] fun m => { m with contributions := m.contributions.map fun c =>
    if c.name == name then { c with methods := c.methods.map change } else c }
private def accepts (name : String) (p : DispatchSource.Program) : IO Unit :=
  match AuthoritySource.checkProgram p true with
  | .ok _ => pure ()
  | .error d => throw (IO.userError s!"indexed authority {name}: {d.code}: {d.message}")
private def rejects (name code : String) (p : DispatchSource.Program) : IO Unit :=
  match AuthoritySource.checkProgram p true with
  | .ok _ => throw (IO.userError s!"indexed authority {name}: unexpectedly accepted")
  | .error d => unless d.code == code do
      throw (IO.userError s!"indexed authority {name}: expected {code}, got {d.code}: {d.message}")
private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"indexed authority regression failed: {name}")

#eval accepts "nested loan, indexed private helper, transfer" authorityFixture
#eval accepts "source package order" { authorityFixture with packages := authorityFixture.packages.reverse }
def transferFixture : DispatchSource.Program := withEvents authorityFixture
  (events.take 6 ++ [.apply ["addon", "post"] none {}, .seal ["base", "choose"] {}])
#eval accepts "new owner edits preserve definition identity" transferFixture
#eval rejects "old owner loses edit authority" "E_OWNER" (withEvents authorityFixture
  (events.take 6 ++ [.apply ["base", "own"] none {}, .seal ["base", "choose"] {}]))
#eval rejects "parent editing suspended" "E_BORROW" (withEvents authorityFixture
  (events.take 2 ++ [.apply ["addon", "ops", "sum"] (some "parent") {}]))
#eval rejects "inside-out return" "E_BORROW" (withEvents authorityFixture
  (events.take 2 ++ [.release "parent" {}]))
#eval rejects "active loan forbids transfer" "E_BORROW" (withEvents authorityFixture
  (events.take 2 ++ [.transfer ["base", "handoff"] {}]))
#eval rejects "delegation permission required" "E_OWNER" (changeModule authorityFixture base [] fun m =>
  { m with module := { m.module with grants := m.module.grants.map fun g => { g with delegable := false } } })
#eval rejects "child region contained" "E_OWNER" (changeModule authorityFixture addon [] fun m =>
  { m with module := { m.module with delegations := m.module.delegations.map fun g => { g with region := [["Int"], ["Nat"]] } } })
#eval rejects "exact child module" "E_OWNER" (changeModule authorityFixture addon [] fun m =>
  { m with module := { m.module with delegations := m.module.delegations.map fun g => { g with granteePath := [] } } })
#eval rejects "unapplied invalid body" "E_TYPE" (changeContribution authorityFixture "unused" fun m =>
  { m with body := block (.boolean true {}) })
#eval rejects "unapplied lambda capture" "E_CAPTURE" (changeContribution authorityFixture "unused" fun m =>
  { m with body := block (.invoke (.lambda [⟨"n", int, {}⟩] int (block (var "x")) {}) [num 0] {}) })
#eval rejects "unapplied out-of-domain specialization" "E_TYPE" (changeContribution authorityFixture "unused" fun m =>
  { m with body := block (.binary "+" (var "x") (num 1) {}) })
#eval rejects "applied indexed scope escape" "E_ESCAPE" (changeContribution authorityFixture "sum" fun m =>
  { m with body := block (num 0) [.letE "p" none (.block
      (block (call "geo::origin" [var "X"]) [.letE "X" none (call "geo::Affine" [num 2]) {}]) {}) {}] })
#eval rejects "contributor cannot read definer private helper" "E_VISIBILITY" (changeContribution authorityFixture "sum" fun m =>
  { m with body := block (call "base::helper") })
#eval rejects "contribution generic recursion" "E_RECURSION" (changeContribution authorityFixture "sum" fun m =>
  { m with body := block (call "base::choose" [var "x"]) })
#eval rejects "ordinary losing body is still checked" "E_TYPE" (changeModule authorityFixture base [] fun m =>
  { m with methods := m.methods.map fun method => { method with body := block (.boolean false {}) } })
#eval rejects "raw contribution body cannot replace rich body" "E_STAGE" (changeModule authorityFixture addon ["ops"] fun m =>
  { m with module := { m.module with contributions := m.contributions.map (·.header) } })
#eval rejects "missing authority envelope" "E_PROTOCOL" { authorityFixture with authority := false }
#eval rejects "nonroot assembly rejected" "E_ASSEMBLY" (changeModule authorityFixture addon [] fun m =>
  { m with module := { m.module with assembly := some ⟨[], {}⟩ } })

def emptyAssemblyFixture : DispatchSource.Program := changeModule authorityFixture app [] fun m =>
  { m with module := { m.module with assembly := none } }
#eval accepts "omitted root assembly is empty" emptyAssemblyFixture
#eval rejects "omitted root still checks unapplied rich bodies" "E_TYPE"
  (changeContribution emptyAssemblyFixture "sum" fun m => { m with body := block (.boolean true {}) })
#eval rejects "omitted root still checks grants" "E_TYPE" (changeModule emptyAssemblyFixture base [] fun m =>
  { m with module := { m.module with grants := m.module.grants.map fun g => { g with region := [["Number"]] } } })
#eval rejects "final footprint includes keys outside callable domain" "E_IMPACT"
  (changeContribution (changeModule authorityFixture base [] fun m =>
    { m with methods := [method "choose" "Any" (block (num 5))] }) "sum" fun m =>
      { m with params := [⟨"x", .data (.named "Number"), {}⟩], body := block (num 42) })

def repairedFixture : DispatchSource.Program := changeModule transferFixture base [] fun m =>
  { m with methods := [], module := { m.module with generics := m.module.generics.map fun g =>
      { g with domain := [[.named "Nat"], [.named "Int"]] } } }
#eval accepts "Open obligation survives return and transfer then is repaired" repairedFixture
#eval rejects "unrepaired obligation after returned loans" "E_DISPATCH_COVERAGE" (withEvents repairedFixture events)
#eval rejects "transfer does not grant contract authority" "E_OWNER" (changeModule transferFixture addon [] fun m =>
  { m with module := { m.module with abstractMethods := [{
    name := "base::choose", params := [⟨"x", .named "Number", {}⟩], returnType := .named "Int",
    domain := [], requirements := [], span := {} }] } })
#eval rejects "transfer does not grant scalar membership authority" "E_OWNER"
  (changeModule (changeModule transferFixture base [] fun m => { m with module := { m.module with
    abstractTypes := [⟨⟨"Arithmetic", [path "Number"], {}⟩, true⟩] } }) addon [] fun m =>
      { m with module := { m.module with subtypes := [⟨"Int", path "base::Arithmetic", {}⟩] } })
#eval rejects "duplicate generic parameters independently validated" "E_DUPLICATE" {
  file := "duplicate-header", root := app.source, extended := true, editable := true, authority := true,
  packages := [⟨app, [], [{ mod with
    functions := [fn "main" (block (num 0)) true],
    module := { mod.module with generics := [{
      name := "choose", params := [⟨"x", {}⟩, ⟨"x", {}⟩], domain := [], span := {}, isPublic := true }] } }]⟩] }

private def orderedFixture (reverse : Bool) : DispatchSource.Program :=
  let p := changeModule authorityFixture base [] fun m => { m with module := { m.module with
    grants := m.module.grants.map fun g => { g with region := [["Nat"], ["Int"]] } } }
  let p := changeModule p addon [] fun m => { m with module := { m.module with
    delegations := m.module.delegations.map fun g => { g with region := [["Nat"], ["Int"]] } } }
  let p := changeModule p addon ["ops"] fun m => { m with contributions := m.contributions ++
    [⟨"natural", path "base::choose", [method "base::choose" "Nat" (block (num 7))], {}, true⟩] }
  let applications := ["sum", "natural"].map fun name =>
    Namespace.EditEvent.apply ["addon", "ops", name] (some "child") {}
  withEvents p (events.take 2 ++ (if reverse then applications.reverse else applications) ++ events.drop 3)
#eval accepts "disjoint contribution order" (orderedFixture false)
#eval accepts "reversed disjoint contribution order" (orderedFixture true)
#eval accepts "same-provenance repeated apply is idempotent" (withEvents authorityFixture
  (events.take 3 ++ [.apply ["addon", "ops", "sum"] (some "child") {}] ++ events.drop 3))

#eval check "all unapplied bodies and lambdas audited, none executable" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => checked.authority.unapplied.instances.length == 4 &&
      checked.audit.lowered.origins.any (fun key => checked.compiler.input.excluded.contains key.definition) &&
      checked.executable.lowered.origins.all (fun key => match checked.compiler.input.prepared[key.definition]? with
        | none => false | some definition => checked.compiler.input.executable definition.definition))
#eval check "canonical generic ID and contributor body scope remain distinct" (match AuthoritySource.checkProgram transferFixture true with
  | .error _ => false
  | .ok checked => checked.authority.applied.any (fun entry =>
      entry.owner == ⟨⟨base, []⟩, "choose"⟩ && entry.scope == ⟨addon, ["ops"]⟩) &&
      checked.authority.headers.assembled.state.history.length == 1)
#eval check "forged contribution body scope rejected independently" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => !Compiler.validScopedDefinitions checked.authority.seeds { checked.lifted with
      definitions := checked.lifted.definitions.map fun definition => { definition with bodyScope := ⟨app, []⟩ } })
#eval check "unapplied method cannot be injected as executable instance" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => let id := checked.compiler.input.sourceCount + checked.authority.applied.length
      !Compiler.validKey checked.compiler.input false ⟨id, []⟩)
#eval check "unapplied lambda cannot be injected as static target" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => checked.compiler.input.prepared.any fun entry => entry.definition.isLambda &&
      checked.compiler.input.excluded.contains entry.definition.origin &&
      match entry.definition.function.callable with
      | none => false
      | some signature => !Compiler.validTargetName checked.compiler.input false (.concrete entry.definition.id) signature)
#eval check "forged dispatch mapping rejected independently" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => !AuthoritySource.instancesValid checked.authority { checked.compiler with input :=
      { checked.compiler.input with dispatch := { checked.compiler.input.dispatch with definitions := {} } } })
#eval check "forged audit exclusion rejected independently" (match AuthoritySource.checkProgram authorityFixture true with
  | .error _ => false
  | .ok checked => !AuthoritySource.instancesValid checked.authority { checked.compiler with input :=
      { checked.compiler.input with excluded := {} } })

end VastitasKernel.Indexed.AuthoritySource.Regression
