import VastitasKernel.LLVM.BinaryTable
import VastitasKernel.LLVM.UnaryFunction
import VastitasKernel.FiniteLookupLayout

set_option autoImplicit false

/-! Compile a complete public library with one binary finite-table export.
Both Hom arguments may belong to different endpoint fibers. The checked
table fixes the order of each axis, including for an empty fiber. -/
namespace VastitasKernel.LLVM.BinaryFunction
open Indexed MidIR
open UnaryFunction (confirm only getChecked checkedCore)

/-- The actual two argument symbols and their hygienic frozen temporaries. -/
structure Site where
  table : DeclId
  category : Option DeclId
  after : FiniteSort
  before : FiniteSort
  output : FiniteSort
  row : Nat
  col : Nat
  rowTemp : Nat
  colTemp : Nat
  swapped : Bool
  fresh : [row, col, rowTemp, colTemp].Nodup

def Site.lookup (s : Site) : FiniteLookup := ⟨s.table, s.category, [s.after,s.before], s.output⟩
def annotation (sort : FiniteSort) : Core.Result := ⟨.finite sort, none⟩
def Site.order {α : Type} (s : Site) (row col : α) : List α :=
  if s.swapped then [col,row] else [row,col]

def Site.params (s : Site) : List Core.Parameter :=
  s.order ⟨s.row, annotation s.after⟩ ⟨s.col, annotation s.before⟩

def Site.body (s : Site) : Core.Term :=
  .scope (.letE s.rowTemp (.variable s.row (annotation s.after))
    (.letE s.colTemp (.variable s.col (annotation s.before))
      (.finiteLookup s.lookup [s.rowTemp,s.colTemp])))

def Site.block (s : Site) (p : Phase) : Block p :=
  let op : Opcode p := match p with
    | .optimization => .lookupTag s.lookup
    | .execution => .lookupOrdinal s.lookup
  ⟨(s.order (.finite s.after) (.finite s.before)).toArray, #[⟨op,s.order ⟨0,0⟩ ⟨0,1⟩⟩], .ret ⟨0⟩ ⟨0,2⟩⟩

def inspect (params : List Core.Parameter) : (term : Core.Term) → Option { s : Site // term = s.body }
  | .scope (.letE rt (.variable r annR) (.letE ct (.variable c annC)
      (.finiteLookup ⟨table,cat,[after,before],out⟩ args))) => do
    let ⟨fresh⟩ ← confirm ([r,c,rt,ct].Nodup)
    let s : Site := ⟨table,cat,after,before,out,r,c,rt,ct,params.head?.any (·.symbol == c),fresh⟩
    let ⟨hr⟩ ← confirm (annR = annotation after)
    let ⟨hc⟩ ← confirm (annC = annotation before)
    let ⟨ha⟩ ← confirm (args = [rt,ct])
    return ⟨s, by subst annR; subst annC; subst args; rfl⟩
  | _ => none

structure Image {env : Environment} {s : Site} (plan : FiniteLookup.Plan env s.lookup)
    (header : TargetHeader) where
  code : BinaryTable.Module
  target : code.header = header
  order : code.swapped = s.swapped
  rows : List String
  cols : List String
  axes : plan.domains = [rows,cols]
  height : code.height.val = rows.length
  width : code.width.val = cols.length
  values : plan.dense? = some (code.outputs.map Fin.val)

def image {env : Environment} {s : Site} (plan : FiniteLookup.Plan env s.lookup)
    (header : TargetHeader) : Option (Image plan header) := do
  let [rows,cols] := plan.domains | none
  let ⟨axes⟩ ← confirm (plan.domains = [rows,cols])
  let ⟨h⟩ ← confirm (rows.length < 4097)
  let ⟨w⟩ ← confirm (cols.length < 4097)
  let ⟨dense, built⟩ ← getChecked plan.dense?
  let tags ← dense.mapM fun n => if small : n < 4096 then some (⟨n,small⟩ : TableSwitch.Tag) else none
  let ⟨rect⟩ ← confirm (tags.length = rows.length * cols.length)
  let ⟨bound⟩ ← confirm (tags.length ≤ 4096)
  let ⟨same⟩ ← confirm (dense = tags.map Fin.val)
  let code : BinaryTable.Module := ⟨header,⟨_,h⟩,⟨_,w⟩,tags,rect,bound,s.swapped⟩
  return ⟨code,rfl,rfl,rows,cols,axes,rfl,rfl,built.trans (congrArg some same)⟩

structure Artifact {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (owner : Namespace.FunctionId) (header : TargetHeader) where
  publicExport : UnaryFunction.exported req owner = true
  sourceFunctions : UnaryFunction.coversSourceFunctions req [owner.owner] = true
  source : Core.Function
  onlyCore : (checkedCore req).functions = [source]
  site : Site
  body : source.body = site.body
  params : source.parameters = site.params
  result : source.returnType = .finite site.output
  ownerEq : source.definition = owner.owner
  opt : MidIR.Module .optimization
  optFrom : MidIR.lowerChecked req = some opt
  exe : MidIR.Module .execution
  exeFrom : opt.execute = some exe
  optFn : MidIR.Function .optimization
  exeFn : MidIR.Function .execution
  onlyOpt : opt.functions = #[optFn]
  onlyExe : exe.functions = #[exeFn]
  optBody : optFn.blocks = #[site.block .optimization]
  exeBody : exeFn.blocks = #[site.block .execution]
  optOwner : optFn.id = owner
  exeOwner : exeFn.id = owner
  coreId : exeFn.coreId = source.id
  specialization : exeFn.specialization = optFn.specialization
  origin : req.checked.pureProgram.executable.lowered.origins[source.id]? = some exeFn.specialization
  env : exe.env = (checkedCore req).declarations.indexed
  revision : exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
  plan : FiniteLookup.Plan exe.env site.lookup
  planFrom : site.lookup.plan? exe.env = some plan
  image : Image plan header

def compile {json : Lean.Json} (req : ResourceSource.Wire.CheckedInput json false)
    (owner : Namespace.FunctionId) (header : TargetHeader) : Option (Artifact req owner header) := do
  guard req.checked.pureProgram.dispatcher.families.isEmpty
  let ⟨publicExport⟩ ← confirm (UnaryFunction.exported req owner = true)
  let ⟨sourceFunctions⟩ ← confirm (UnaryFunction.coversSourceFunctions req [owner.owner] = true)
  let ⟨source,onlyCore⟩ ← only (checkedCore req).functions
  let ⟨site,body⟩ ← inspect source.parameters source.body
  let ⟨params⟩ ← confirm (source.parameters = site.params)
  let ⟨result⟩ ← confirm (source.returnType = .finite site.output)
  let ⟨ownerEq⟩ ← confirm (source.definition = owner.owner)
  let ⟨opt,optFrom⟩ ← getChecked (MidIR.lowerChecked req)
  let ⟨exe,exeFrom⟩ ← getChecked opt.execute
  let ⟨o,onlyOpt⟩ ← only opt.functions.toList
  let ⟨e,onlyExe⟩ ← only exe.functions.toList
  let ⟨optBody⟩ ← confirm (o.blocks = #[site.block .optimization])
  let ⟨exeBody⟩ ← confirm (e.blocks = #[site.block .execution])
  let ⟨optOwner⟩ ← confirm (o.id = owner)
  let ⟨exeOwner⟩ ← confirm (e.id = owner)
  let ⟨coreId⟩ ← confirm (e.coreId = source.id)
  let ⟨specialization⟩ ← confirm (e.specialization = o.specialization)
  let ⟨origin⟩ ← confirm (req.checked.pureProgram.executable.lowered.origins[source.id]? = some e.specialization)
  let ⟨plan,planFrom⟩ ← getChecked (site.lookup.plan? exe.env)
  let img ← image plan header
  let identity := MidIR.lowerChecked_identity req opt optFrom
  let retained := MidIR.execute_identity opt exe exeFrom
  return {
    publicExport, sourceFunctions, source, onlyCore, site, body, params, result, ownerEq
    opt, optFrom, exe, exeFrom, optFn := o, exeFn := e
    onlyOpt := Array.toList_inj.mp onlyOpt, onlyExe := Array.toList_inj.mp onlyExe
    optBody, exeBody, optOwner, exeOwner, coreId, specialization, origin
    env := retained.1.trans identity.1, revision := retained.2.trans identity.2
    plan, planFrom, image := img }

end VastitasKernel.LLVM.BinaryFunction
