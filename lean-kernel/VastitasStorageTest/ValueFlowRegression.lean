import VastitasStorageTest.SourceRegression
import VastitasKernel.ResourceCodegen

namespace VastitasKernel.Storage.ValueFlow.Regression
open ResourceSource

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"value flow regression: {name}")

private def signatures : List Signature := [⟨[], .bool⟩, ⟨[], .int⟩, ⟨[.bool, .int], .int⟩]
private def intBlock (value : String) : Indexed.FunctionSource.Block := .mk [] (.integer value {}) {}
private def boolBlock : Indexed.FunctionSource.Block := .mk [] (.boolean true {}) {}

private def changeMain (change : ResourceSource.Function → ResourceSource.Function) : ResourceSource.Program :=
  let input := ResourceSource.Regression.fixture
  {input with packages := input.packages.map fun pkg => {pkg with modules := pkg.modules.map fun m =>
    {m with functions := m.functions.map fun f => if f.name == "main" then change f else f}}}

private def fixture : ResourceSource.Program := changeMain fun f => {f with
  body :=
  [.value "decision" .bool boolBlock {},
   .branchValue "decision" [.value "leftOnly" .int (intBlock "11") {}]
     [.value "rightOnly" .int (intBlock "19") {}] {},
   .value "answerInput" .int (intBlock "42") {}] ++ f.body
  valueBody := .mk [] (.variable "answerInput" {}) {}}

#eval show IO Unit from do
  let code : List ValueFlow.Statement := [.value 0 0 [], .branch (.slot 0)
    [.value 1 1 []] [.value 2 1 []], .value 3 1 [], .value 4 2 [0, 3]]
  let .ok checked := ValueFlow.check signatures [] code
    | throw (IO.userError "well-typed branch slots rejected")
  require "branch locals leave lexical scalar scope"
    (type? checked.finalState.slots 1 == none && type? checked.finalState.slots 2 == none)
  for (name, input) in [
    ("missing fragment", [.value 0 999 []]),
    ("wrong argument order/types", [.value 0 0 [], .value 1 1 [], .value 2 2 [1, 0]]),
    ("undefined branch slot", [.branch (.slot 0) [] []]),
    ("non-Bool branch", [.value 0 1 [], .branch (.slot 0) [] []]),
    ("duplicate slot", [.value 0 0 [], .value 0 1 []]),
    ("sibling slot leak", [.value 0 0 [], .branch (.slot 0) [.value 1 1 []] [.value 2 2 [0, 1]]]),
    ("branch result leak", [.value 0 0 [], .branch (.slot 0) [.value 1 1 []] [], .value 2 2 [0, 1]]),
    ("branch name resurrection", [.value 0 0 [], .branch (.slot 0) [.value 1 1 []] [], .value 1 1 []])
  ] do require name (!(ValueFlow.check signatures [] input).isOk)
  require "duplicate typed inputs" (!(ValueFlow.check signatures [(0, .bool), (0, .bool)] []).isOk)
  let .ok source := ResourceSource.check fixture true
    | throw (IO.userError "mixed full-authority source rejected")
  require "one source position per fragment" (source.lowered.sites.length == source.targets.entries.length)
  require "fresh source positions" (decide source.lowered.sites.Nodup)
  let some entry := fixture.entry | throw (IO.userError "missing source main")
  let some function := source.lowered.functions[entry]? | throw (IO.userError "missing lowered main")
  let some (fragment, arguments, _) := function.valueResult | throw (IO.userError "missing main return")
  let some target := source.targets.entries[fragment]? | throw (IO.userError "missing main Core target")
  require "terminal signature excludes branch-local scalars"
    (target.signature.parameters == [.bool, .int] && arguments.length == 2)
  let .ok generated := ResourceSource.Codegen.generate fixture
    | throw (IO.userError "mixed code generation rejected")
  require "runtime condition rendered from actual slot" ((generated.source.splitOn "if resourceValue_").length > 1)
  let raw : Functions.Program := ⟨source.lowered.functions, entry⟩
  for (name, mutate) in [
    ("forged return fragment", fun (f : Functions.Function) => {f with valueResult := some (999999, arguments, .int)}),
    ("forged return slot", fun f => {f with valueResult := some (fragment, [999999, 999999], .int)}),
    ("forged result type", fun f => {f with valueResult := some (fragment, arguments, .bool)}),
    ("forged branch slot", fun f => {f with body := .branch (.slot 999999) [] [] :: f.body})
  ] do
    let forged := {raw with functions := raw.functions.map fun f => if f.id == entry then mutate f else f}
    require name (!(Functions.check forged (ResourceSource.numericalEnvironment source.pureProgram) source.targets.signatures).isOk)
  let unusedBad : Functions.Function := {
    id := 999999, parameters := [], results := [], body := [], valueResult := some (999999, [], .pair .int)}
  require "discarded Pair result still audits fragment signature"
    (!(Functions.check {raw with functions := raw.functions ++ [unusedBad]}
      (ResourceSource.numericalEnvironment source.pureProgram) source.targets.signatures).isOk)
  IO.println "Resource value flow: both-arm scalar scope, fresh slots, actual Core target signatures, source positions, runtime branch extraction and forged return IR passed"

end VastitasKernel.Storage.ValueFlow.Regression
