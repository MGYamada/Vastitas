import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedCoreRegression
import VastitasKernel.IndexedPackageSemanticRegression
import VastitasKernel.IndexedSourceRegression
import VastitasKernel.IndexedSourceTypeRegression
import VastitasKernel.IndexedSourceBodyRegression
import VastitasKernel.IndexedFunctionRegression
import VastitasKernel.IndexedDispatchRegression
import VastitasKernel.IndexedAuthorityRegression
import VastitasKernel.SmoothObjectRegression
import VastitasKernel.CotangentRegression
import VastitasKernel.MetricFormRegression
import VastitasKernel.ReverseCoreRegression
import VastitasKernel.FrameRegression
import VastitasKernel.SpectralRegression

open VastitasKernel.Indexed.Core

/-- The largest local symbol of a term. -/
partial def maxSymbol : Term → Nat
  | .variable symbol _ => symbol
  | .letE symbol value body => max symbol (max (maxSymbol value) (maxSymbol body))
  | .unpack witness fields package body =>
    max witness (max (fields.foldl max 0) (max (maxSymbol package) (maxSymbol body)))
  | .unary _ value _ | .project _ _ value | .natToInt value | .scope value | .ascribe _ value =>
    maxSymbol value
  | .binary _ left right _ | .pair _ left right => max (maxSymbol left) (maxSymbol right)
  | .branch condition yes no _ => max (maxSymbol condition) (max (maxSymbol yes) (maxSymbol no))
  | .primitive _ arguments _ | .call _ arguments _ _ => arguments.foldl (fun m t => max m (maxSymbol t)) 0
  | .pack _ witness fields => fields.foldl (fun m t => max m (maxSymbol t)) (maxSymbol witness)
  | _ => 0

/-- The module with the body `b` of `main` written as `{ let shown = show!(b); 0 }`
(#836): its first top-level statement binds the old result under a fresh
symbol, and the observation of that statement writes it as `main = value`. -/
def observed (module : Module) : Option Module := do
  let id ← module.main
  let fresh := 1 + module.functions.foldl (fun m function =>
    max m (function.parameters.foldl (fun m p => max m p.symbol) (maxSymbol function.body))) 0
  return { module with functions := module.functions.map fun function =>
    if function.id == id then { function with body := .scope (.letE fresh function.body (.integer 0)) }
    else function }

def shown : List Observation := [{ statement := 0, label := "main" }]

/-- Writes `{name}.lean`, the program of `module`, and `{name}_shown.lean`, the
program that observes the result of its `main` and exits with 0. `compile`
runs between the check and generation. -/
def emit (directory name : String) (module : Module)
    (compile : Typing.CheckedModule true → Except String (Typing.CheckedModule true) := pure) :
    IO Unit := do
  for (file, variant, observations) in [(name, some module, []), (name ++ "_shown", observed module, shown)] do
    let some variant := variant | throw (IO.userError s!"fixture {name} has no entry point")
    let .ok checked := Typing.checkModule variant true
      | throw (IO.userError s!"fixture {file} rejected")
    let .ok compiled := compile checked
      | throw (IO.userError s!"fixture {file} failed its reverse compilation")
    let .ok source := Codegen.generate compiled observations
      | throw (IO.userError s!"fixture {file} failed code generation")
    IO.FS.writeFile (System.FilePath.mk directory / s!"{file}.lean") source

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let .ok sourceFixture := VastitasKernel.Indexed.Source.Regression.sourceFixture
    | throw (IO.userError "source declaration fixture rejected")
  let .ok typeFixture := VastitasKernel.Indexed.Source.TypeRegression.typeFixture
    | throw (IO.userError "source type fixture rejected")
  let mut bodies := []
  for (name, program) in [
      ("source_bodies", VastitasKernel.Indexed.Source.BodyRegression.packageFixture),
      ("source_scalars", VastitasKernel.Indexed.Source.BodyRegression.scalarFixture),
      ("source_fields", VastitasKernel.Indexed.Source.BodyRegression.multipleFixture)] do
    let .ok checked := VastitasKernel.Indexed.Source.Bodies.checkProgram program true
      | throw (IO.userError s!"fixture {name} failed source body checking")
    bodies := bodies ++ [(name, checked.core.module)]
  for (name, program) in [
      ("functions", VastitasKernel.Indexed.FunctionSource.Regression.higherFixture),
      ("function_objects", VastitasKernel.Indexed.FunctionSource.Regression.indexedLambdaFixture),
      ("function_private", VastitasKernel.Indexed.FunctionSource.Regression.privateTargetFixture),
      ("function_fields", VastitasKernel.Indexed.FunctionSource.Regression.dataProgram
        VastitasKernel.Indexed.Source.BodyRegression.multipleFixture)] do
    let .ok checked := VastitasKernel.Indexed.FunctionSource.Compiler.checkProgram program true
      | throw (IO.userError s!"fixture {name} failed source Fn checking")
    bodies := bodies ++ [(name, checked.executable.core.module)]
  for (name, program) in [
      ("dispatch", VastitasKernel.Indexed.DispatchSource.Regression.dispatchFixture),
      ("dispatch_contract", VastitasKernel.Indexed.DispatchSource.Regression.contractFixture),
      ("dispatch_nominal", VastitasKernel.Indexed.DispatchSource.Regression.nominalFixture),
      ("dispatch_pair", VastitasKernel.Indexed.DispatchSource.Regression.pairFixture)] do
    let .ok checked := VastitasKernel.Indexed.DispatchSource.checkProgram program true
      | throw (IO.userError s!"fixture {name} failed source dispatch checking")
    bodies := bodies ++ [(name, checked.executable.core.module)]
  for (name, program) in [
      ("authority", VastitasKernel.Indexed.AuthoritySource.Regression.authorityFixture),
      ("authority_transfer", VastitasKernel.Indexed.AuthoritySource.Regression.transferFixture),
      ("authority_repaired", VastitasKernel.Indexed.AuthoritySource.Regression.repairedFixture),
      ("authority_empty", VastitasKernel.Indexed.AuthoritySource.Regression.emptyAssemblyFixture)] do
    let .ok checked := VastitasKernel.Indexed.AuthoritySource.checkProgram program true
      | throw (IO.userError s!"fixture {name} failed indexed authority checking")
    bodies := bodies ++ [(name, checked.executable.core.module)]
  for (name, module) in [("package", Regression.packageFixture),
      ("primitives", Regression.primitiveFixture), ("scalar", Regression.scalarFixture),
      ("global_witness", PackageSemanticRegression.globalWitnessFixture),
      ("opened_object", PackageSemanticRegression.escapedObjectFixture),
      ("multiple_fields", PackageSemanticRegression.multipleFieldsFixture),
      ("source_declarations", sourceFixture), ("source_types", typeFixture),
      ("smooth_programs", VastitasKernel.Indexed.SmoothObjectRegression.smoothFixture),
      ("smooth_cotangent_programs", VastitasKernel.Indexed.CotangentRegression.cotangentFixture),
      ("smooth_metric_programs", VastitasKernel.Indexed.MetricFormRegression.metricFixture),
      ("frame_programs", VastitasKernel.Indexed.FrameRegression.frameFixture),
      ("spectral_programs", VastitasKernel.Indexed.SpectralRegression.spectralFixture)] ++ bodies do
    emit directory name module
  -- Compiled reverse Core (#623): the reverse sites compiled into Core, checked
  -- again and validated, then lowered.
  for (name, module) in [
      ("smooth_reverse_programs", VastitasKernel.Indexed.CotangentRegression.cotangentFixture),
      ("smooth_reverse_extended", VastitasKernel.Indexed.Core.ReverseCoreRegression.extendedFixture),
      ("spectral_reverse_programs", VastitasKernel.Indexed.SpectralRegression.spectralFixture)] do
    emit directory name module fun checked =>
      (Reverse.compile checked).map (·.core) |>.mapError (·.message)
