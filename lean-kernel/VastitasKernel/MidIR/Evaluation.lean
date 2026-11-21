import VastitasKernel.MidIR.Check
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

namespace VastitasKernel.MidIR.Evaluation
open Indexed Indexed.Core.Semantics

private def fits : VastitasKernel.MidIR.Ty → Value → Bool
  | .unit, .unit => true
  | .bool, .boolean _ => true
  | .finite c, .finiteTag d _ => c == d
  | _, _ => false

/-- Read the ordered nominal arguments of a table, including the owner and
endpoints of each Hom fiber. Arity mismatches have no value. -/
def lookupKey : List FiniteSort → List Value → Option (List String)
  | [], [] => some []
  | sort :: sorts, .finiteTag actual tag :: args => do
    guard (actual == sort)
    return tag :: (← lookupKey sorts args)
  | _, _ => none

def lookupValue (env : Environment) (site : FiniteLookup) (args : List Value) : Option Value := do
  let plan ← site.plan? env
  let key ← lookupKey site.inputs args
  return .finiteTag site.output (← plan.atKey key)

abbrev Resolver := CallTarget → List Value → Option Value

/-- Interpret only the operand list and kinds specified by the opcode. -/
def exactValue : ExactOp → List Value → Option Value
  | .nat op, [.natural a, .natural b] => some (.natural (match op with
    | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b))
  | .int op, [.integer a, .integer b] => some (.integer (match op with
    | .add => a + b | .sub => a - b | .mul => a * b | .div => a / b))
  | .natIntDiv, [.natural a, .integer b] => some (.integer (Int.ofNat a / b))
  | .intNatDiv, [.integer a, .natural b] => some (.integer (a / Int.ofNat b))
  | .neg, [.integer a] => some (.integer (-a))
  | .natToInt, [.natural a] => some (.integer (Int.ofNat a))
  | .pair e, [a,b] => evalPair e a b
  | .project e first, [p] => evalProject e first p
  | _, _ => none

def denote {p : Phase} (env : Environment) (op : Opcode p) (args : List Value)
    (resolve : Resolver := fun _ _ => none) : Option Value :=
  match op with
  | .unit => if args.isEmpty then some .unit else none
  | .boolean b => if args.isEmpty then some (.boolean b) else none
  | .natural n => if args.isEmpty then some (.natural n) else none
  | .exactOp op => Evaluation.exactValue op args
  | .integer n => if args.isEmpty then some (.integer n) else none
  | .finiteTag c t => if args.isEmpty then some (.finiteTag c t) else none
  | .finiteOrdinal c n => do
    guard args.isEmpty
    let tags ← FiniteSort.tags env c
    return .finiteTag c (← tags[n]?)
  | .lookupTag s | .lookupOrdinal s => lookupValue env s args
  | .boolAnd => match args with
    | [.boolean a, .boolean b] => some (.boolean (a && b))
    | _ => none
  | .boolOr => match args with
    | [.boolean a, .boolean b] => some (.boolean (a || b))
    | _ => none
  | .boolNot => match args with
    | [.boolean a] => some (.boolean (!a))
    | _ => none
  | .call target => resolve target args
  | .compare k t => do
    let [a, b] := args | none
    guard (fits t a && fits t b)
    let equal := decide (a = b)
    return .boolean (match k with | .eq => equal | .ne => !equal)

structure SemanticOp where
  args : List Ref
  eval : List Value → Option Value

structure SemanticBlock where
  params : Array VastitasKernel.MidIR.Ty
  ops : Array SemanticOp
  term : Terminator

private abbrev Frame := Std.HashMap Ref Value

/-- The SSA environment records a value only after its instruction ran. -/
def runGraph (blocks : Array SemanticBlock) (args : List Value) : Option Value :=
  let rec go : Nat → Nat → Frame → List Value → Option Value
    | 0, _, _, _ => none
    | fuel + 1, pc, frame, args => do
      let block ← blocks[pc]?
      guard (args.length == block.params.size)
      let mut values := frame
      for (arg, i) in args.zipIdx do
        values := values.insert ⟨pc, i⟩ arg
      for (op, i) in block.ops.toList.zipIdx do
        let vals ← op.args.mapM (values[·]?)
        let value ← op.eval vals
        values := values.insert ⟨pc, block.params.size + i⟩ value
      let edge ← match block.term with
        | .ret _ ref => return ← values[ref]?
        | .jump edge => pure edge
        | .branch choice yes no => do
          let .boolean b ← values[choice]? | none
          pure (if b then yes else no)
      go fuel edge.dest values (← edge.args.mapM (values[·]?))
  go blocks.size 0 {} args

def observeOp {p : Phase} (resolve : Resolver) (env : Environment) (op : Op p) : SemanticOp :=
  ⟨op.args, fun vs => denote env op.code vs resolve⟩

def observeBlock {p : Phase} (resolve : Resolver) (env : Environment) (b : Block p) : SemanticBlock :=
  ⟨b.params, b.ops.map (observeOp resolve env), b.term⟩

/-- Interpret a direct call with the selected symbol in this exact module.
The decreasing call depth also bounds interpretation of malformed modules. -/
def runWith {p : Phase} (env : Environment) (f : MidIR.Function p) (resolve : Resolver)
    (args : List Value) : Option Value :=
  runGraph (f.blocks.map (observeBlock resolve env)) args

def invoke {p : Phase} (m : Module p) : Nat → Resolver
  | 0, _, _ => none
  | depth + 1, target, args => do
    let f ← m.functions[target.symbol]?
    guard (decide (f.target = target))
    runWith m.env f (invoke m depth) args

end VastitasKernel.MidIR.Evaluation
