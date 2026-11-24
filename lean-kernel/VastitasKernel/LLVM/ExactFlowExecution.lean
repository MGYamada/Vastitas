import VastitasKernel.LLVM.ExactFlow
import VastitasKernel.MidIR.Evaluation

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExactFlow
open MidIR Indexed.Core.Semantics

private def bounded : Value → Bool
  | .natural n => n.log2 < 4096 | .integer n => n.natAbs.log2 < 4096
  | .pairNat a b => a.log2 < 4096 && b.log2 < 4096
  | .pairInt a b => a.natAbs.log2 < 4096 && b.natAbs.log2 < 4096
  | .boolean _ => true | _ => false

private def boolean2 (vs : Array Value) (a b : Nat) (op : Bool → Bool → Bool) : Option Value := do
  let .boolean x ← vs[a]? | none
  let .boolean y ← vs[b]? | none
  return .boolean (op x y)

private def evalOp (call : Nat → List Value → StateT Nat Option Value)
    (vs : Array Value) : Op → StateT Nat Option Value
  | .exact (.nat n) => pure (.natural n)
  | .exact (.int n) => pure (.integer n)
  | .exact (.apply op args) => liftM (do Evaluation.exactValue op (← args.mapM (vs[·]?)))
  | .exact (.compare k op a b) =>
    liftM (do Evaluation.compareValues op (pairScalar k) (← vs[a]?) (← vs[b]?))
  | .invoke i args => do call i (← liftM (args.mapM (vs[·]?)))
  | .boolean b => pure (.boolean b)
  | .boolNot a => liftM (do
    let .boolean x ← vs[a]? | none
    return .boolean (!x))
  | .boolAnd a b => liftM (boolean2 vs a b (· && ·))
  | .boolOr a b => liftM (boolean2 vs a b (· || ·))

private def runBlocks (call : Nat → List Value → StateT Nat Option Value)
    (f : Func) : Nat → Nat → List Value → StateT Nat Option Value
  | 0, _, _ => failure
  | depth+1, i, args => do
    let b ← liftM (f.blocks[i]?)
    guard (args.length == b.params.length)
    let fuel ← get
    let cost := 1 + args.length + b.ops.length
    guard (cost ≤ fuel)
    set (fuel - cost)
    let mut values := args.toArray
    for op in b.ops do
      let v ← evalOp call values op
      guard (bounded v)
      values := values.push v
    let edge ← match b.exit with
      | .ret r => return ← liftM (values[r]?)
      | .jump e => pure e
      | .branch r yes no =>
        let some (.boolean c) := values[r]? | failure
        pure (if c then yes else no)
    runBlocks call f depth edge.dest (← liftM (edge.args.mapM (values[·]?)))

private def invoke (c : Code) : Nat → Nat → List Value → StateT Nat Option Value
  | 0, _, _ => failure
  | depth+1, i, args => do
    let f ← liftM (c.functions[i]?)
    runBlocks (invoke c depth) f f.blocks.size 0 args

def Code.entryValue (c : Code) : Option Int := do
  let .integer n ← (invoke c c.functions.size c.entry []).run' 32768 | none
  return n

end VastitasKernel.LLVM.ExactFlow
