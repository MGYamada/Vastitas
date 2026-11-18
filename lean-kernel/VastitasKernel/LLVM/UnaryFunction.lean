import VastitasKernel.MidIR.Checked
import VastitasKernel.LLVM.UnaryTable

set_option autoImplicit false

/-! The complete module accepted by this specialization consists of one
named unary lookup. The library ABI exports it as `vq_lookup`. Both MidIR
passes and the exact checked Core remain attached to the same request. -/
namespace VastitasKernel.LLVM.UnaryFunction
open Indexed MidIR

def inputType (s : UnaryLookup) : Core.Result := ⟨.finite (.carrier s.input), none⟩

/-- The ordinary Core compiler scopes function bodies and freezes each actual
argument of a table lookup in its own hygienic let. -/
def body (s : UnaryLookup) (param temp : Nat) : Core.Term :=
  .scope (.letE temp (.variable param (inputType s)) (.finiteLookup s.site [temp]))

structure BodyView (term : Core.Term) where
  lookup : UnaryLookup
  param : Nat
  temp : Nat
  exactBody : term = body lookup param temp

def inspectBody : (term : Core.Term) → Option (BodyView term)
  | .scope (.letE temp (.variable param ann)
      (.finiteLookup ⟨table, none, [.carrier input], .carrier output⟩ [arg])) =>
    let s := UnaryLookup.mk table input output
    if exactAnn : ann = inputType s then
      if exactArg : arg = temp then
        some ⟨s, param, temp, by subst ann; subst arg; rfl⟩
      else none
    else none
  | _ => none

abbrev checkedCore {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false) :=
  req.checked.pureProgram.compiled.core.module

/-- A complete module must account for source definitions even when Core has
no executable specialization for them. Unused higher-order functions and
finite templates still belong to the program's source interface. -/
def coversSourceFunctions {json : Lean.Json} {main : Bool}
    (req : ResourceSource.Wire.CheckedInput json main) (owners : List Namespace.Owner) : Bool :=
  let p := req.input.pureProgram.source
  Finite.sameCounts (p.functions.map Prod.fst) owners && p.finiteFunctions.isEmpty &&
    req.input.packages.all (fun pkg => pkg.modules.all fun m => m.functions.isEmpty)

/-- This one-symbol foreign library may export only a public top-level
function of the checked root package. -/
def exported {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (id : Namespace.FunctionId) : Bool :=
  id.owner.scope.path.isEmpty && id.owner.scope.package.source == req.input.root &&
    req.input.pureProgram.source.headers.indexed.declarations.any fun t =>
      t.owner == id.owner && t.kind == .function && t.isPublic

/-- Equations keep the returned functions, actual opcode operands, revision
and canonical switch tied to the requested source owner. All fields referring
to an untrusted input must agree in order to construct this result. -/
structure Artifact {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (owner : Namespace.FunctionId) (header : TargetHeader) where
  publicExport : exported req owner = true
  sourceFunctions : coversSourceFunctions req [owner.owner] = true
  source : Core.Function
  onlyCore : (checkedCore req).functions = [source]
  view : BodyView source.body
  params : source.parameters = [⟨view.param, inputType view.lookup⟩]
  result : source.returnType = .finite (.carrier view.lookup.output)
  sourceOwner : source.definition = owner.owner
  opt : MidIR.Module .optimization
  optFrom : MidIR.lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optFn : MidIR.Function .optimization
  exeFn : MidIR.Function .execution
  onlyOpt : opt.functions = #[optFn]
  onlyExe : exe.functions = #[exeFn]
  optOrder : optFn.blocks = #[view.lookup.block .optimization]
  exeOrder : exeFn.blocks = #[view.lookup.block .execution]
  optOwner : optFn.id = owner
  exeOwner : exeFn.id = owner
  coreId : exeFn.coreId = source.id
  specialization : exeFn.specialization = optFn.specialization
  origin : req.checked.pureProgram.executable.lowered.origins[source.id]? = some exeFn.specialization
  env : exe.env = (checkedCore req).declarations.indexed
  revision : exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
  plan : FiniteLookup.Plan exe.env view.lookup.site
  planFrom : view.lookup.site.plan? exe.env = some plan
  image : UnaryTable.Image exe.env view.lookup.table header
  inputCarrier : image.input = view.lookup.input
  outputCarrier : image.output = view.lookup.output

def getChecked {α : Type} (x : Option α) : Option {v // x = some v} :=
  match x with | none => none | some v => some ⟨v, rfl⟩

def only {α : Type} (xs : List α) : Option {x // xs = [x]} :=
  match xs with | [x] => some ⟨x, rfl⟩ | _ => none

def confirm (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then some ⟨h⟩ else none

def compile {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (owner : Namespace.FunctionId) (header : TargetHeader) : Option (Artifact req owner header) := do
  guard req.checked.pureProgram.dispatcher.families.isEmpty
  let ⟨sourceFunctions⟩ ← confirm (coversSourceFunctions req [owner.owner] = true)
  let ⟨publicExport⟩ ← confirm (exported req owner = true)
  let ⟨source, onlyCore⟩ ← only (checkedCore req).functions
  let view ← inspectBody source.body
  let s := view.lookup
  let ⟨params⟩ ← confirm (source.parameters = [⟨view.param, inputType s⟩])
  let ⟨result⟩ ← confirm (source.returnType = .finite (.carrier s.output))
  let ⟨sourceOwner⟩ ← confirm (source.definition = owner.owner)
  let ⟨opt, optFrom⟩ ← getChecked (MidIR.lowerChecked req)
  let ⟨exe, exeFrom⟩ ← getChecked opt.execute
  let ⟨o, onlyOpt⟩ ← only opt.functions.toList
  let ⟨e, onlyExe⟩ ← only exe.functions.toList
  let ⟨optOrder⟩ ← confirm (o.blocks = #[s.block .optimization])
  let ⟨exeOrder⟩ ← confirm (e.blocks = #[s.block .execution])
  let ⟨optOwner⟩ ← confirm (o.id = owner)
  let ⟨exeOwner⟩ ← confirm (e.id = owner)
  let ⟨coreId⟩ ← confirm (e.coreId = source.id)
  let ⟨specialization⟩ ← confirm (e.specialization = o.specialization)
  let ⟨origin⟩ ← confirm (req.checked.pureProgram.executable.lowered.origins[source.id]? = some e.specialization)
  let identity := MidIR.lowerChecked_identity req opt optFrom
  let retained := MidIR.execute_identity opt exe exeFrom
  let ⟨plan, planFrom⟩ ← getChecked (s.site.plan? exe.env)
  let image ← UnaryTable.lower exe.env s.table header
  let ⟨inputCarrier⟩ ← confirm (image.input = s.input)
  let ⟨outputCarrier⟩ ← confirm (image.output = s.output)
  return {
    publicExport, sourceFunctions, source, onlyCore, view, params, result, sourceOwner, opt, optFrom, exe, exeFrom
    optFn := o, exeFn := e, onlyOpt := Array.toList_inj.mp onlyOpt, onlyExe := Array.toList_inj.mp onlyExe
    optOrder, exeOrder, optOwner, exeOwner, coreId, specialization, origin, env := retained.1.trans identity.1, revision := retained.2.trans identity.2,
    plan, planFrom, image, inputCarrier, outputCarrier }

end VastitasKernel.LLVM.UnaryFunction
