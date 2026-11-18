import VastitasKernel.LLVM.FiniteModuleModel
import VastitasKernel.Limits

set_option autoImplicit false

/-! Execution of the finite LLVM instruction set. Call frames, local SSA
registers, predecessor labels and integer widths are taken from the LLVM
model. The evaluator never consults Core, MidIR or a source table. -/
namespace VastitasKernel.LLVM.FiniteModule

namespace Machine
structure Word where
  width : Width
  bits : UInt32

abbrev Registers := Std.HashMap String Word

def read (regs : Registers) (w : Width) : Operand → Option UInt32
  | .literal n => do
    guard (w == .word || n < 2)
    return n
  | .reg name => do
    let value ← regs[name]?
    guard (value.width == w)
    return value.bits

def write (regs : Registers) (name : String) (value : Word) : Option Registers := do
  guard (!regs.contains name)
  return regs.insert name value

def bin (op : Binary) (w : Width) (a b : UInt32) : UInt32 :=
  let n := match op with
    | .band => a &&& b
    | .bor => a ||| b
    | .add => a + b
    | .mul => a * b
  if w == .bit then n &&& 1 else n

def predicate (p : Predicate) (x y : UInt32) : UInt32 :=
  let yes := match p with
    | .eq => x == y
    | .ne => x != y
    | .ult => decide (x < y)
  if yes then 1 else 0

/-- Execute a pure register assignment using the same width checks and word
operations as the full call/CFG evaluator. -/
def assign (regs : Registers) : Instr → Option Registers
  | .binary dst op w a b => do
    write regs dst ⟨w, bin op w (← read regs w a) (← read regs w b)⟩
  | .compare dst op w a b => do
    write regs dst ⟨.bit, predicate op (← read regs w a) (← read regs w b)⟩
  | _ => none

def bindParams (params : List (Width × String)) (args : List Word) : Option Registers := do
  guard (args.length == params.length)
  (params.zip args).foldlM (init := {}) fun regs ((ty,name),arg) => do
    guard (arg.width == ty)
    write regs name arg

end Machine
open Machine

private structure Body where
  f : Func
  labels : Std.HashMap String Block

private def link (code : Code) : Option (Std.HashMap String Body) := do
  let mut symbols := {}
  for f in code.functions do
    guard (!symbols.contains f.name)
    let mut labels := {}
    for block in f.blocks do
      guard (!labels.contains block.label)
      labels := labels.insert block.label block
    symbols := symbols.insert f.name ⟨f, labels⟩
  return symbols

private structure Frame where
  body : Body
  block : Block
  ops : List Instr
  regs : Registers
  /-- All phi instructions in one block read the predecessor's register file. -/
  incoming : Option (String × Registers)

private def activate (body : Body) (args : List Word) : Option Frame := do
  let regs ← bindParams body.f.params args
  let first ← body.f.blocks.head?
  return ⟨body, first, first.ops, regs, none⟩

private def jump (f : Frame) (label : String) : Option Frame := do
  let block ← f.body.labels[label]?
  return { f with block, ops := block.ops, incoming := some (f.block.label, f.regs) }

private structure ReturnTo where
  caller : Frame
  dest : String
  width : Width

/-- One fuel unit pays for one instruction or terminator, across all calls. -/
private def run (symbols : Std.HashMap String Body) : Nat → Frame → List ReturnTo → Option UInt32
  | 0, _, _ => none
  | fuel+1, f, stack => do
    match f.ops with
    | op :: tail =>
      let next := { f with ops := tail, incoming := none }
      match op with
      | .binary .. | .compare .. =>
        run symbols fuel { next with regs := ← assign f.regs op } stack
      | .phi dst width incoming =>
        let (label, before) ← f.incoming
        let [(value, _)] := incoming.filter (fun arm => arm.2 == label) | none
        let bits ← read before width value
        run symbols fuel { f with ops := tail, regs := ← write f.regs dst ⟨width,bits⟩ } stack
      | .call dst width callee args =>
        let body ← symbols[callee]?
        guard (width == body.f.result)
        let args ← args.mapM fun a => do return Word.mk a.ty (← read f.regs a.ty a.value)
        run symbols fuel (← activate body args) (⟨next, dst, width⟩ :: stack)
    | [] =>
      match f.block.exit with
      | .ret arg =>
        guard (arg.ty == f.body.f.result)
        let bits ← read f.regs arg.ty arg.value
        match stack with
        | [] => return bits
        | ret :: rest =>
          guard (ret.width == arg.ty)
          let caller := ret.caller
          run symbols fuel { caller with regs := ← write caller.regs ret.dest ⟨arg.ty,bits⟩ } rest
      | .jump label => run symbols fuel (← jump f label) stack
      | .branch cond yes no =>
        let bit ← read f.regs .bit cond
        run symbols fuel (← jump f (if bit == 1 then yes else no)) stack
      | .switch value miss cases =>
        let ordinal ← read f.regs .word value
        let label := (cases.lookup ordinal).getD miss
        run symbols fuel (← jump f label) stack

/-- Observe the address produced by a guarded table helper before its switch.
The outer Option checks the two-block shape. The inner Option is empty when
the guard takes the miss edge. Register binding, assignment and reads use
the instruction semantics of `Code.invoke`. -/
def Func.guardedIndex (f : Func) (digits : List UInt32) : Option (Option UInt32) := do
  let start :: lookup :: _ := f.blocks | none
  let .branch cond good miss := start.exit | none
  let .switch index fallback _ := lookup.exit | none
  guard (good == lookup.label && miss == fallback)
  let initial ← bindParams f.params (digits.map fun d => ⟨.word,d⟩)
  let checked ← start.ops.foldlM assign initial
  if (← read checked .bit cond) == 0 then return none
  let regs ← lookup.ops.foldlM assign checked
  return some (← read regs .word index)

/-- Call a named helper with explicit ABI widths. All SSA and switch
operations run on the actual instructions and operands of that helper. -/
def Code.invoke (m : Code) (name : String) (args : List (Width × UInt32))
    (fuel : Nat := Limits.elaborationWork) : Option UInt32 := do
  let symbols ← link m
  let body ← symbols[name]?
  let words ← args.mapM fun (w, n) => do
    guard (w == .word || n < 2)
    return Word.mk w n
  run symbols fuel (← activate body words) []

/-- Observe the defined public C entry of a finite LLVM executable, including
actual nested calls, phi predecessor choices and table switches. -/
def Code.entryStatus (m : Code) (fuel : Nat := Limits.elaborationWork) : Option UInt32 := do
  let symbols ← link m
  let main ← symbols["main"]?
  guard (!main.f.internal && main.f.result == .word && main.f.params.isEmpty)
  run symbols fuel (← activate main []) []

end VastitasKernel.LLVM.FiniteModule
