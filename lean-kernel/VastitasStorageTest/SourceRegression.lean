import VastitasKernel.ResourceSource
import VastitasKernel.IndexedAuthorityRegression

namespace VastitasKernel.ResourceSource.Regression
open Storage

private def original := Indexed.AuthoritySource.Regression.authorityFixture
private def app := original.packages[0]!.id
private def base := original.packages[1]!.id
private def path (name : String) : Indexed.Source.Path := ⟨name.splitOn "::", {}⟩
private def rectangle : Layout := ⟨8,2,2,4,false⟩
private def buffer : Functions.OwnedType := ⟨.f64,8,[rectangle]⟩
private def value := Literal.f64 0x4008000000000000
private def makeBuffer : Function := {
  name := "makeBuffer", parameters := [], results := [("data", .owned buffer)], isPublic := true,
  body := [.action (.allocate "data" .f64 8) {},
    .action (.borrow "output" "data" rectangle .write) {},
    .action (.fill "output" value) {}, .action (.release "output") {}] }
private def readBuffer : Function := {
  name := "readBuffer", parameters := [.borrowed "input" .f64 2 2 .read false {}], results := [],
  isPublic := true, body := [.action (.expect "input" 0 0 value) {}] }
private def mainBody : List Statement := [
  .call (path "base::makeBuffer") [] ["owned"] {},
  .action (.borrow "view" "owned" rectangle .read) {},
  .call (path "read") ["view"] [] {},
  .action (.release "view") {}, .action (.drop "owned") {}]
private def main : Function := {
  name := "main", parameters := [], results := [], body := mainBody, valueType := .int,
  valueBody := .mk [] (.call (path "answer") [] {}) {} }

/-- The same source includes real nested edit loans, transferred authority,
applicable/nonwinning methods, unapplied contributions and indexed Fn bodies. -/
def fixture : Program := {
  file := original.file, root := original.root,
  packages := original.packages.map fun pkg => {
    id := pkg.id, dependencies := pkg.dependencies, geometryCompat := pkg.geometryCompat,
    modules := pkg.modules.map fun m => {
      pureModule := if pkg.id == app then {m with
        functions := m.functions.map fun function => {function with name := "answer"},
        module := {m.module with imports := [⟨["base", "readBuffer"], "read", false, {}⟩]} } else m,
      functions := if pkg.id == app then [main] else if pkg.id == base then [makeBuffer, readBuffer] else [] } } }

private def changeModule (p : Program) (owner : Namespace.PackageId)
    (change : Module → Module) : Program :=
  {p with packages := p.packages.map fun pkg => {pkg with modules := pkg.modules.map fun m =>
    if pkg.id == owner && m.pureModule.module.path.isEmpty then change m else m}}
private def rootBody (body : List Statement) : Program :=
  changeModule fixture app fun m => {m with functions := [{main with body}]}
private def accepts (name : String) (input : Program) (requireMain := true) : IO Unit := do
  match check input requireMain with
  | .error error => throw (IO.userError s!"{name}: {error.code}: {error.message}")
  | .ok accepted =>
    unless accepted.lowered.owners == input.owned.map Prod.fst do
      throw (IO.userError s!"{name}: owner mapping changed")
private def rejects (name code : String) (input : Program) : IO Unit := do
  match check input true with
  | .ok _ => throw (IO.userError s!"{name}: unexpectedly accepted")
  | .error error => unless error.code == code do
    throw (IO.userError s!"{name}: expected {code}, got {error.code}: {error.message}")

#eval show IO Unit from do
  accepts "shared authority/resource input" fixture
  accepts "declaration order" {fixture with packages := fixture.packages.reverse}
  let library := changeModule fixture app fun m => {m with functions := []}
  accepts "library without fabricated resource entry" library false
  rejects "emit library requires real main" "E_MAIN" library
  rejects "private resource cannot be imported" "E_VISIBILITY" (changeModule fixture base fun m =>
    {m with functions := m.functions.map fun f => {f with isPublic := false}})
  rejects "resource header forgery" "E_OWNER" (changeModule fixture app fun m =>
    {m with pureModule := {m.pureModule with module := {m.pureModule.module with
      resourceFunctions := [⟨"forged", true, {}⟩]}}})
  rejects "cross-kind declaration collision" "E_DUPLICATE" (changeModule fixture app fun m =>
    {m with functions := [{main with name := "answer"}]})
  rejects "pure function is not a resource callee" "E_TYPE" (rootBody [.call (path "answer") [] [] {}])
  rejects "generic is not a resource callee" "E_TYPE" (rootBody [.call (path "base::choose") [] [] {}])
  rejects "resource cannot enter pure Core" "E_TYPE" (changeModule fixture app fun m =>
    {m with pureModule := {m.pureModule with functions := m.pureModule.functions.map fun f =>
      {f with body := .mk [] (.call (path "base::makeBuffer") [] {}) {}}}})
  rejects "source local cannot shadow import" "E_SHADOW" (rootBody [.action (.allocate "read" .f64 1) {}])
  rejects "source local cannot capture caller" "E_RESOURCE_NAME" (changeModule fixture base fun m =>
    {m with functions := m.functions.map fun f => if f.name == "readBuffer" then
      {f with body := [.action (.release "view") {}]} else f})
  rejects "branch-local binding escapes" "E_RESOURCE_NAME" (rootBody [
    .branch true [.action (.allocate "local" .f64 1) {}, .action (.drop "local") {}] [] {},
    .action (.drop "local") {}])
  rejects "unused source resource body" "E_RESOURCE_NAME" (changeModule fixture base fun m =>
    {m with functions := m.functions ++ [{name := "unused", parameters := [], results := [], body := [.action (.drop "missing") {}]}]})
  rejects "source loan fails real initialization" "E_RESOURCE_INIT" (rootBody [
    .action (.allocate "owned" .f64 8) {}, .action (.borrow "view" "owned" rectangle .read) {}])
  rejects "missing assembly return remains rejected" "E_BORROW" (changeModule fixture app fun m =>
    {m with pureModule := {m.pureModule with module := {m.pureModule.module with
      assembly := m.pureModule.module.assembly.map fun a => {a with events := a.events.take 4}}}})
  let badUnapplied := {fixture with packages := fixture.packages.map fun pkg => {pkg with modules := pkg.modules.map fun m =>
    {m with pureModule := {m.pureModule with contributions := m.pureModule.contributions.map fun c =>
      if c.name == "unused" then {c with methods := c.methods.map fun method =>
        {method with body := .mk [] (.boolean true {}) {}}} else c}}}}
  rejects "unapplied pure contribution still checked" "E_TYPE" badUnapplied
  let .ok accepted := check fixture true | throw (IO.userError "fixture disappeared")
  let .ok native := Storage.Native.compile (accepted.execution 0 rfl).checked.statements
    | throw (IO.userError "resolved resource source failed native compilation")
  unless (native.instructions.filter fun op => match op with | .allocate .. => true | _ => false).length == 1 do
    throw (IO.userError "all-body resource probes entered executable schedule")
  IO.println "resource source: package authority, scoped names, real entry/library, call provenance and 14 rejection cases passed"

end VastitasKernel.ResourceSource.Regression
