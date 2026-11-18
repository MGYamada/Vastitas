import VastitasKernel.LLVM.ExitMain
import VastitasKernel.LLVM.UnaryFunction

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExitFunction
open Indexed MidIR
open UnaryFunction (confirm getChecked only)

abbrev core {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main) :=
  req.checked.pureProgram.compiled.core.module

def literalBody : (t : Core.Term) → Option { l : IntLiteral // t = .scope l.term }
  | .scope t => do
    let ⟨lit, same⟩ ← IntLiteral.inspect t
    return ⟨lit, congrArg Core.Term.scope same⟩
  | _ => none

/-- The chosen Core entry is the one top-level function of the user program.
Even unused resource functions and uninstantiated finite templates are excluded. -/
def sourceEntry {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (f : Core.Function) : Bool :=
  f.definition.name == "main" && f.definition.scope.path.isEmpty &&
    f.definition.scope.package.source == req.input.root &&
    UnaryFunction.coversSourceFunctions req [f.definition]

structure Stage {phase : Phase} (m : MidIR.Module phase) (f : Core.Function)
    (key : FunctionSource.Compiler.Key) (lit : IntLiteral) where
  entry : MidIR.Function phase
  sole : m.functions = #[entry]
  target : entry.target = ⟨⟨f.definition⟩,f.id,key,[],.int⟩
  linked : m.entry = some f.id
  instructions : entry.blocks = #[lit.block phase]

private def stage {phase : Phase} (m : MidIR.Module phase) (f : Core.Function)
    (key : FunctionSource.Compiler.Key) (lit : IntLiteral) : Option (Stage m f key lit) := do
  let ⟨entry, sole⟩ ← only m.functions.toList
  let ⟨target⟩ ← confirm (entry.target = ⟨⟨f.definition⟩,f.id,key,[],.int⟩)
  let ⟨linked⟩ ← confirm (m.entry = some f.id)
  let ⟨instructions⟩ ← confirm (entry.blocks = #[lit.block phase])
  return ⟨entry, Array.toList_inj.mp sole, target, linked, instructions⟩

structure CheckedEntry {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) (Body : Core.Term → IntLiteral → Prop) where
  source : Core.Function
  onlyCore : (core req).functions = [source]
  entry : (core req).main = some source.id
  symbol : source.id = 0
  signature : source.parameters = [] ∧ source.returnType = .pure .int
  sourceFunction : sourceEntry req source = true
  literal : IntLiteral
  body : Body source.body literal
  key : FunctionSource.Compiler.Key
  origin : req.checked.pureProgram.executable.lowered.origins[source.id]? = some key
  opt : MidIR.Module .optimization
  optFrom : MidIR.lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optStage : Stage opt source key literal
  exeStage : Stage exe source key literal
  environment : exe.env = (core req).declarations.indexed
  revision : exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked

abbrev Artifact {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) := CheckedEntry req header (fun t l => t = .scope l.term)

def CheckedEntry.toModule {json : Lean.Json} {main : Bool} {req : ResourceSource.Wire.CheckedInput json main}
    {header : TargetHeader} {Body : Core.Term → IntLiteral → Prop} (a : CheckedEntry req header Body) : ExitMain.Module :=
  ⟨header, ExitMain.statusOf a.literal.value⟩

private def compileWith {Body : Core.Term → IntLiteral → Prop} (inspect : (t : Core.Term) → Option {l // Body t l})
    {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) : Option (CheckedEntry req header Body) := do
  guard req.checked.pureProgram.dispatcher.families.isEmpty
  let ⟨source, onlyCore⟩ ← only (core req).functions
  let ⟨entry⟩ ← confirm ((core req).main = some source.id)
  let ⟨symbol⟩ ← confirm (source.id = 0)
  let ⟨signature⟩ ← confirm (source.parameters = [] ∧ source.returnType = .pure .int)
  let ⟨sourceFunction⟩ ← confirm (sourceEntry req source = true)
  let ⟨literal, body⟩ ← inspect source.body
  let ⟨key, origin⟩ ← getChecked req.checked.pureProgram.executable.lowered.origins[source.id]?
  let ⟨opt, optFrom⟩ ← getChecked (MidIR.lowerChecked req)
  let ⟨exe, exeFrom⟩ ← getChecked opt.execute
  let optStage ← stage opt source key literal
  let exeStage ← stage exe source key literal
  let identity := MidIR.lowerChecked_identity req opt optFrom
  let retained := MidIR.execute_identity opt exe exeFrom
  return {
    source, onlyCore, entry, symbol, signature, sourceFunction, literal, body, key, origin,
    opt, optFrom, exe, exeFrom, optStage, exeStage, environment := retained.1.trans identity.1,
    revision := retained.2.trans identity.2 }

def compile {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) : Option (Artifact req header) := compileWith literalBody req header

structure Site where
  caller : Nat
  selection : ExactOperators.Selection
  method : ExactFold.Method selection

def Site.key (site : Site) := (site.caller, site.selection)

abbrev FoldBody (term : Core.Term) (l : IntLiteral) := ExactFold.Folded [] term (.int l.value)

/-- Every arithmetic site in the actual returned module has one concrete protected
method. The ordered keys match the pass from which the public receipt was printed. -/
structure CheckedSites {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    where
  sites : List Site
  coreSites : sites.map Site.key = ExactOperators.selections (core req)
  revisionSites : sites.map Site.key = ExactOperators.selections req.checked.pureProgram.executable.core.module

structure FoldArtifact {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) extends CheckedEntry req header FoldBody, CheckedSites req

private def foldedBody (t : Core.Term) : Option {l : IntLiteral // FoldBody t l} := do
  let ⟨n, h⟩ ← ExactFold.integer t
  return ⟨.integer n, h⟩

def checkSites {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main) :
    Option (CheckedSites req) := do
  let keys := ExactOperators.selections (core req)
  let sites ← keys.mapM fun (caller, selection) => do
    return Site.mk caller selection (← ExactFold.resolve selection)
  let ⟨coreSites⟩ ← confirm (sites.map Site.key = keys)
  let ⟨revisionSites⟩ ← confirm (sites.map Site.key = ExactOperators.selections req.checked.pureProgram.executable.core.module)
  return ⟨sites, coreSites, revisionSites⟩

def compileFold {json : Lean.Json} {main : Bool} (req : ResourceSource.Wire.CheckedInput json main)
    (header : TargetHeader) : Option (FoldArtifact req header) := do
  let base ← compileWith foldedBody req header
  return { toCheckedEntry := base, toCheckedSites := ← checkSites req }

end VastitasKernel.LLVM.ExitFunction
