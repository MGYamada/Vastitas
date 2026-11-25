import VastitasKernel.LLVM.FiniteModuleSyntax
import VastitasKernel.LLVM.ExitMain
import VastitasKernel.MidIR.Check
import VastitasKernel.FiniteLookupLayout

set_option autoImplicit false

/-! Translation of execution MidIR's finite closure to closed LLVM functions.
Each use of an ordered finite lookup gets its own helper, derived from that
nominal site's checked dense plan. Only the hosted entry projects Int to its
low eight process-status bits. -/
namespace VastitasKernel.LLVM.FiniteModule
open Indexed

def maxUnits : Nat := 32768

def refName (r : MidIR.Ref) := s!"v{r.block}_{r.slot}"
private def value (r : MidIR.Ref) := Operand.reg (refName r)
private def label (i : Nat) := s!"b{i}"
private def functionName (i : Nat) := s!"f{i}"
def widthOf : MidIR.Ty → Option Width
  | .unit | .bool => some .bit
  | .int | .finite _ => some .word
  | .nat | .pair _ => none
private def lit (n : Nat) := Operand.literal n.toUInt32
private def word (n : Nat) : Arg := ⟨.word, lit n⟩
private def caseName (n : Nat) := s!"case{n}"

def axisName : Nat → String
  | 0 => "x" | 1 => "y" | i => s!"axis{i}"

/-- Compare every argument first. Only the success edge computes the Horner
index, extending the address with `previous * width + coordinate`. -/
structure TableAddress where
  guards : List Instr
  arithmetic : List Instr
  inside : Operand
  index : Operand

def TableAddress.push (prev : TableAddress) (axis : Nat × Nat) : TableAddress :=
  let (width,i) := axis
  let arg := Operand.reg (axisName i)
  let ok := if i == 1 then "colOK" else s!"ok{i}"
  let both := if i == 1 then "both" else s!"inside{i}"
  let base := if i == 1 then "base" else s!"base{i}"
  let index := if i == 1 then "index" else s!"index{i}"
  ⟨prev.guards ++ [.compare ok .ult .word arg (.literal width.toUInt32),
      .binary both .band .bit prev.inside (.reg ok)],
    prev.arithmetic ++ [.binary base .mul .word prev.index (.literal width.toUInt32),
      .binary index .add .word (.reg base) arg], .reg both, .reg index⟩

def tableAddress (first : Nat) (rest : List Nat) : TableAddress :=
  (rest.zipIdx 1).foldl TableAddress.push
    ⟨[.compare "rowOK" .ult .word (.reg "x") (.literal first.toUInt32)], [], .reg "rowOK", .reg "x"⟩

/-- The nullary product has one row. A unary switch directly checks its
ordinal. Multi-column helpers guard every axis before flattening the tuple. -/
def table (name : String) (dims rows : List Nat) : Option Func := do
  guard (rows.length == dims.prod && rows.length ≤ 4096 && dims.all (· ≤ 4096) && rows.all (· < 4096))
  guard (dims.length ≤ FiniteTables.maxInputs)
  let arms := rows.zipIdx.map fun (_,i) => (i.toUInt32,caseName i)
  let leaves := rows.zipIdx.map fun (output,i) => Block.mk (caseName i) [] (.ret (word output))
  let miss : Block := ⟨"miss",[],.ret ⟨.word,.literal 0xffffffff⟩⟩
  let params := dims.zipIdx.map fun (_,i) => (Width.word,axisName i)
  let blocks := match dims with
    | [] => [Block.mk "start" [] (.switch (lit 0) "miss" arms)]
    | [_] => [Block.mk "start" [] (.switch (.reg "x") "miss" arms)]
    | first :: second :: more =>
      let addr := tableAddress first (second :: more)
      [⟨"start",addr.guards,.branch addr.inside "lookup" "miss"⟩,
       ⟨"lookup",addr.arithmetic,.switch addr.index "miss" arms⟩]
  return ⟨name,true,.word,params,blocks ++ leaves ++ [miss]⟩

structure TableImage (env : Environment) (site : FiniteLookup) (name : String) where
  plan : FiniteLookup.Plan env site
  selected : site.plan? env = some plan
  rows : List Nat
  dense : plan.dense? = some rows
  function : Func
  emitted : table name (plan.domains.map List.length) rows = some function

def lookupImage (env : Environment) (site : FiniteLookup) (name : String) : Option (TableImage env site name) :=
  match h : site.plan? env with
  | none => none
  | some plan => match d : plan.dense? with
    | none => none
    | some rows => match t : table name (plan.domains.map List.length) rows with
      | none => none
      | some f => some ⟨plan,h,rows,d,f,t⟩

def predEdges (t : MidIR.Terminator) : List MidIR.Edge :=
  match t with | .ret .. => [] | .jump e => [e] | .branch _ y n => [y,n]

def exitOf (output : Width) : MidIR.Terminator → Exit
  | .ret _ r => .ret ⟨output,value r⟩
  | .jump e => .jump (label e.dest)
  | .branch c y n => .branch (value c) (label y.dest) (label n.dest)

def operation (env : Environment) (entry : Bool) (fi : Nat) (dst : MidIR.Ref)
    (op : MidIR.Op .execution) : Option (Instr × Option Func) := do
  let d := refName dst
  match op.code, op.args with
  | .unit, [] => return (.binary d .bor .bit (lit 0) (lit 0), none)
  | .boolean b, [] => return (.binary d .bor .bit (lit 0) (lit (if b then 1 else 0)), none)
  | .boolAnd, [a,b] => return (.binary d .band .bit (value a) (value b),none)
  | .boolOr, [a,b] => return (.binary d .bor .bit (value a) (value b),none)
  | .boolNot, [a] => return (.compare d .eq .bit (value a) (lit 0),none)
  | .integer n, [] =>
    guard entry
    return (.binary d .add .word (lit 0) (lit (ExitMain.statusOf n).toNat),none)
  | .finiteOrdinal _ n, [] =>
    guard (n < 4096)
    return (.binary d .add .word (lit 0) (lit n),none)
  | .compare k t, [a,b] =>
    guard (t != .int && t != .nat)
    let cmp ← match k with | .eq => some Predicate.eq | .ne => some .ne | _ => none
    return (.compare d cmp (← widthOf t) (value a) (value b),none)
  | .call target, args =>
    guard (!target.params.contains .int && target.result != .int && args.length == target.params.length)
    let params ← (target.params.zip args).mapM fun (ty,r) => do return Arg.mk (← widthOf ty) (value r)
    return (.call d (← widthOf target.result) (functionName target.symbol) params,none)
  | .lookupOrdinal s, args =>
    let n := s!"t{fi}_{dst.block}_{dst.slot}"
    let image ← lookupImage env s n
    return (.call d .word n (args.map (fun r => ⟨.word,value r⟩)),some image.function)
  | _, _ => none

/-- A linked source function owns the lookup helpers emitted along with its body.
The body takes its LLVM name from the checked dense symbol table. -/
structure FunctionImage where
  helpers : Array Func
  result : Width
  params : List (Width × String)
  blocks : List Block

def FunctionImage.body (image : FunctionImage) (symbol : Nat) : Func :=
  ⟨functionName symbol, true, image.result, image.params, image.blocks⟩

abbrev Incoming := Array (Array (Nat × List MidIR.Ref))

def recordEdge (fromBlock : Nat) (incoming : Incoming) (e : MidIR.Edge) : Option Incoming :=
  if h : e.dest < incoming.size then
    some (incoming.set e.dest (incoming[e.dest].push (fromBlock, e.args)) h)
  else none

def recordBlock (incoming : Incoming) (row : MidIR.Block .execution × Nat) : Option Incoming :=
  (predEdges row.1.term).foldlM (recordEdge row.2) incoming

def incomingEdges (blocks : Array (MidIR.Block .execution)) : Option Incoming :=
  blocks.toList.zipIdx.foldlM recordBlock (Array.replicate blocks.size #[])

def blockPhis (isEntry : Bool) (incoming : Incoming) (i : Nat) (params : Array MidIR.Ty) :
    Option (List Instr) := do
  if i == 0 then return []
  let preds ← incoming[i]?
  params.toList.zipIdx.mapM fun (param,j) => do
    guard (isEntry || param != .int)
    let arms ← preds.toList.mapM fun (fromBlock,rs) => do return (value (← rs[j]?),label fromBlock)
    return .phi (refName ⟨i,j⟩) (← widthOf param) arms

/-- Emit one instruction at each SSA slot. Only a lookup appends a helper. -/
def emitOps (env : Environment) (isEntry : Bool) (fi block : Nat) :
    List (MidIR.Op .execution) → Nat → Array Instr → Array Func → Option (Array Instr × Array Func)
  | [], _, lines, helpers => some (lines, helpers)
  | op :: rest, slot, lines, helpers => do
    let (line, helper) ← operation env isEntry fi ⟨block,slot⟩ op
    let helpers := match helper with | some h => helpers.push h | none => helpers
    emitOps env isEntry fi block rest (slot + 1) (lines.push line) helpers

def emitBlocks (env : Environment) (isEntry : Bool) (fi : Nat) (output : Width) (incoming : Incoming) :
    List (MidIR.Block .execution) → Nat → Array Block → Array Func → Option (Array Block × Array Func)
  | [], _, blocks, helpers => some (blocks, helpers)
  | b :: rest, i, blocks, helpers => do
    let phis ← blockPhis isEntry incoming i b.params
    let (ops, helpers) ← emitOps env isEntry fi i b.ops.toList b.params.size phis.toArray helpers
    let block := Block.mk (label i) ops.toList (exitOf output b.term)
    emitBlocks env isEntry fi output incoming rest (i + 1) (blocks.push block) helpers

def translateFn (env : Environment) (entry : Nat) (f : MidIR.Function .execution) :
    Option FunctionImage := do
  guard (MidIR.validFunction env f)
  let output ← widthOf f.result
  let isEntry := f.coreId == entry
  guard (!f.params.contains .int && (isEntry || f.result != .int))
  let incoming ← incomingEdges f.blocks
  let (blocks, helpers) ← emitBlocks env isEntry f.coreId output incoming f.blocks.toList 0 #[] #[]
  let params ← f.params.toList.zipIdx.mapM fun (ty,j) => do return (← widthOf ty,refName ⟨0,j⟩)
  return ⟨helpers, output, params, blocks.toList⟩

/-- Charge branch/phi and table work before building case blocks, allocating
their text, or asking the nominal checker to expand a dense Cartesian product. -/
private def withinLimit (m : MidIR.Module .execution) : Bool := Id.run do
  let mut cost := m.functions.size
  for f in m.functions do
    cost := cost + f.params.size + f.blocks.size
    for b in f.blocks do
      cost := cost + b.params.size + b.ops.size
      for e in predEdges b.term do cost := cost + e.args.length + 1
      for op in b.ops do
        cost := cost + op.args.length
        if let .lookupOrdinal s := op.code then
          unless s.inputs.length ≤ FiniteTables.maxInputs do return false
          let some axes := s.inputs.mapM (FiniteSort.tags m.env) | return false
          let dims := axes.map List.length
          unless dims.all (· ≤ 4096) && dims.prod ≤ 4096 do return false
          cost := cost + dims.prod * 2 + 8 + (dims.length - 2) * 4
        if cost > maxUnits then return false
      if cost > maxUnits then return false
  return cost ≤ maxUnits

def hostMain (entry : Nat) : Func :=
  ⟨"main",false,.word,[],[⟨"start",[.call "result" .word (functionName entry) []],
    .ret ⟨.word,.reg "result"⟩⟩]⟩

/-- Consume one function image at a time. The emitted array holds the final
definitions while the next function's control-flow graph is translated. -/
def emitFunctions (env : Environment) (entry : Nat) :
    List (MidIR.Function .execution) → Nat → Array Func → Option (Array Func)
  | [], _, emitted => some emitted
  | f :: fs, slot, emitted => do
    let image ← translateFn env entry f
    emitFunctions env entry fs (slot + 1) ((emitted ++ image.helpers).push (image.body slot))

def translate (m : MidIR.Module .execution) (target : TargetHeader) : Option Code := do
  let entry ← m.entry
  guard (withinLimit m && MidIR.validSymbols m)
  let functions ← emitFunctions m.env entry m.functions.toList 0 #[]
  return ⟨target, (functions.push (hostMain entry)).toList⟩

def lower (m : MidIR.Module .execution) (target : TargetHeader) : Option Module := do
  certify (← translate m target)

end VastitasKernel.LLVM.FiniteModule
