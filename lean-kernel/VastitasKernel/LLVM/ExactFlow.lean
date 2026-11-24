import VastitasKernel.LLVM.ExactLibrary
import VastitasKernel.MidIR.Check

set_option autoImplicit false

/-! Boxed integer control flow with local SSA slots. Non-entry block arguments
are simultaneous phi results. A predecessor supplies both written block arguments
and any dominating values the successor still needs. -/
namespace VastitasKernel.LLVM.ExactFlow
open MidIR ExactLibrary

inductive Op where
  | exact (step : Step)
  | invoke (callee : Nat) (args : List Nat)
  | boolean (b : Bool)
  | boolNot (a : Nat)
  | boolAnd (a b : Nat)
  | boolOr (a b : Nat)
  deriving DecidableEq

structure Edge where
  dest : Nat
  args : List Nat
  deriving DecidableEq

inductive Exit where
  | ret (slot : Nat)
  | jump (edge : Edge)
  | branch (cond : Nat) (yes no : Edge)
  deriving DecidableEq

def Exit.edges : Exit → List Edge
  | .ret _ => [] | .jump e => [e] | .branch _ y n => [y,n]

structure Block where
  params : List Kind
  ops : List Op
  exit : Exit
  deriving DecidableEq

structure Func where
  result : Kind
  blocks : Array Block
  deriving DecidableEq

def Func.params (f : Func) := (f.blocks[0]?).map Block.params

structure Code where
  header : TargetHeader
  functions : Array Func
  entry : Nat
  deriving DecidableEq

def Op.result (fs : Array Func) : Op → Option Kind
  | .exact (.nat _) => some .nat | .exact (.int _) => some .int
  | .exact (.apply op _) => Kind.ofTy op.result
  | .invoke idx _ => (fs[idx]?).map Func.result
  | _ => some .bool

private def Op.inputs (fs : Array Func) (o : Op) : Option (List Nat × List Kind) := do
  match o with
  | .exact (.nat _) | .exact (.int _) | .boolean _ => return ([],[])
  | .exact (.apply op args) => return (args, ← op.operands.mapM Kind.ofTy)
  | .exact (.compare sort _ a b) =>
    let k ← Kind.ofTy (pairScalar sort)
    return ([a,b],[k,k])
  | .invoke i args => return (args, ← (← fs[i]?).params)
  | .boolNot a => return ([a],[.bool])
  | .boolAnd a b | .boolOr a b => return ([a,b],[.bool,.bool])

def Block.slotKinds (b : Block) (fs : Array Func) : Option (Array Kind) := do
  return (b.params ++ (← b.ops.mapM (·.result fs))).toArray

private def validFn (fs : Array Func) (idx : Nat) (f : Func) : Bool := Id.run do
  unless 0 < f.blocks.size && f.blocks.size ≤ 4096 do return false
  let mut reached := #[true] ++ Array.replicate (f.blocks.size - 1) false
  let mut work := 0
  for (b,i) in f.blocks.toList.zipIdx do
    unless reached[i]? == some true && b.params.length + b.ops.length ≤ 4096 do return false
    let mut slots := b.params.toArray
    for op in b.ops do
      let some (args,ps) := op.inputs fs | return false
      unless args.mapM (slots[·]?) == some ps do return false
      if let .invoke target _ := op then unless target < idx do return false
      let some k := op.result fs | return false
      slots := slots.push k
    match b.exit with
    | .ret r => unless slots[r]? == some f.result do return false
    | .branch cond yes no =>
      unless slots[cond]? == some .bool && yes.dest != no.dest do return false
    | .jump _ => pure ()
    work := work + slots.size
    for e in b.exit.edges do
      let some target := f.blocks[e.dest]? | return false
      unless i < e.dest && e.args.mapM (slots[·]?) == some target.params do return false
      reached := reached.set! e.dest true
      work := work + e.args.length
    unless work ≤ Limits.elaborationWork do return false
  return true

def Code.valid (c : Code) : Bool := Id.run do
  let some start := c.functions[c.entry]? | return false
  unless c.functions.size ≤ 4096 && start.params == some [] && start.result == .int do return false
  return c.functions.toList.zipIdx.all fun (f,i) => validFn c.functions i f

/-- References read by a block or needed unchanged on one of its outgoing edges. -/
private def captures (f : MidIR.Function .execution) : Option (Array (List Ref)) := do
  guard (f.blocks.size ≤ 4096)
  let mut result := Array.replicate f.blocks.size []
  let mut work := 0
  for i in (List.range f.blocks.size).reverse do
    let b ← f.blocks[i]?
    let (reads,edges) := match b.term with
      | .ret _ r => ([r],[]) | .jump e => ([],[e]) | .branch r y n => ([r],[y,n])
    let mut refs := b.ops.toList.flatMap (·.args) ++ reads
    for e in edges do
      guard (i < e.dest)
      refs := refs ++ e.args ++ (← result[e.dest]?)
    work := work + refs.length
    guard (work ≤ Limits.elaborationWork)
    let mut seen : Std.HashSet Ref := {}
    let mut needed := #[]
    for r in refs do
      if r.block != i && !seen.contains r then
        seen := seen.insert r
        needed := needed.push r
    result := result.set! i needed.toList
  return result

def translateOp (code : Opcode .execution) (refs : List Nat) : Option Op := do
  match code, refs with
  | .natural n, [] => return .exact (.nat n)
  | .integer n, [] => return .exact (.int n)
  | .exactOp op, args => return .exact (.apply op args)
  | .compare op .nat, [a,b] => return .exact (.compare .nat op a b)
  | .compare op .int, [a,b] => return .exact (.compare .int op a b)
  | .boolean b, [] => return .boolean b
  | .boolNot, [a] => return .boolNot a
  | .boolAnd, [a,b] => return .boolAnd a b
  | .boolOr, [a,b] => return .boolOr a b
  | .call target, args => return .invoke target.symbol args
  | _, _ => none

/-- Translate one SSA block with the dominating values required by its successors. -/
def translateBlock (f : MidIR.Function .execution) (extra : Array (List Ref))
    (b : MidIR.Block .execution) (i : Nat) : Option Block := do
  let kind (r : Ref) := do
    let b ← f.blocks[r.block]?
    let t ← if r.slot < b.params.size then b.params[r.slot]?
            else (b.ops[r.slot - b.params.size]?).map (·.code.result)
    Kind.ofTy t
  let live ← extra[i]?
  let positions := Std.HashMap.ofList (live.zipIdx b.params.size)
  let localSlot (r : Ref) : Option Nat :=
    if r.block == i then some (if r.slot < b.params.size then r.slot else r.slot + live.length)
    else positions[r]?
  let edge (e : MidIR.Edge) := do
    return Edge.mk e.dest (← (e.args ++ (← extra[e.dest]?)).mapM localSlot)
  let params := (← b.params.toList.mapM Kind.ofTy) ++ (← live.mapM kind)
  let ops ← b.ops.toList.mapM fun op => do translateOp op.code (← op.args.mapM localSlot)
  let term : Option Exit := match b.term with
    | .ret _ r => Exit.ret <$> localSlot r
    | .jump e => Exit.jump <$> edge e
    | .branch r y n => do return .branch (← localSlot r) (← edge y) (← edge n)
  return ⟨params, ops, ← term⟩

def translateFn (env : Indexed.Environment) (f : MidIR.Function .execution) : Option Func := do
  guard (validFunction env f)
  let extra ← captures f
  guard (extra[0]? == some [])
  let blocks ← f.blocks.zipIdx.mapM fun (b,i) => translateBlock f extra b i
  return ⟨← Kind.ofTy f.result, blocks⟩

def translate (m : MidIR.Module .execution) (header : TargetHeader) : Option Code := do
  guard (m.functions.size ≤ 4096 && validSymbols m)
  let c := Code.mk header (← m.functions.mapM (translateFn m.env)) (← m.entry)
  guard c.valid
  return c

end VastitasKernel.LLVM.ExactFlow
