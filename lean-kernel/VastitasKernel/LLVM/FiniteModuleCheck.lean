import VastitasKernel.LLVM.FiniteModuleModel
import Std.Data.HashMap
import Std.Data.HashSet

set_option autoImplicit false

/-! Independent SSA, signature and control-flow checks for the finite,
acyclic LLVM sublanguage, including all incoming edges of every phi. -/
namespace VastitasKernel.LLVM.FiniteModule

private abbrev Regs := Std.HashMap String Width
private abbrev Sigs := Std.HashMap String (List Width × Width)
private abbrev Preds := Std.HashMap String Regs

private def operandAt (regs : Regs) (t : Width) : Operand → Bool
  | .literal n => t == .word || n ≤ 1
  | .reg n => regs[n]? == some t

private def phiValid (preds : Preds) (t : Width) (xs : List (Operand × String)) : Bool := Id.run do
  unless !xs.isEmpty && xs.length == preds.size do return false
  let mut seen : Std.HashSet String := {}
  for (v,p) in xs do
    let some regs := preds[p]? | return false
    unless !seen.contains p && operandAt regs t v do return false
    seen := seen.insert p
  return true

private def assignment (sigs : Sigs) (regs : Regs) (preds : Preds) (atHead : Bool) :
    Instr → Option (String × Width)
  | .binary d op t a b => do
    guard (operandAt regs t a && operandAt regs t b &&
      ((op == .band || op == .bor) || t == .word))
    return (d,t)
  | .compare d _ t a b => do
    guard (operandAt regs t a && operandAt regs t b)
    return (d,.bit)
  | .call d t callee args => do
    guard (sigs[callee]? == some (args.map (·.ty), t) && args.all fun a => operandAt regs a.ty a.value)
    return (d,t)
  | .phi d t xs => do
    guard (atHead && phiValid preds t xs)
    return (d,t)

private def successors (regs : Regs) (result : Width) : Exit → Option (List String)
  | .ret a => do guard (a.ty == result && operandAt regs result a.value); return []
  | .jump n => some [n]
  | .branch c y n => do guard (operandAt regs .bit c); return [y,n]
  | .switch v miss cases => do
    guard (operandAt regs .word v)
    let mut seen : Std.HashSet UInt32 := {}
    for (key,_) in cases do
      guard (!seen.contains key)
      seen := seen.insert key
    return miss :: cases.map Prod.snd

private def checkFn (sigs : Sigs) (f : Func) : Bool := Id.run do
  let some entry := f.blocks.head? | return false
  let mut reserved : Std.HashSet String := {}
  let mut initial : Regs := {}
  for b in f.blocks do
    if reserved.contains b.label then return false
    reserved := reserved.insert b.label
  let labels := reserved
  for (t,n) in f.params do
    if reserved.contains n then return false
    reserved := reserved.insert n
    initial := initial.insert n t
  let mut visited : Std.HashSet String := {}
  let mut intersectionWork := 0
  let mut incoming : Std.HashMap String Preds := {}
  for b in f.blocks do
    visited := visited.insert b.label
    let preds := incoming.getD b.label {}
    let mut regs := initial
    if b.label != entry.label then
      let some (_,first) := preds.toList.head? | return false
      regs := first
      if preds.size > 1 then
        intersectionWork := intersectionWork + first.size * preds.size
        if intersectionWork > 262144 then return false
        regs := preds.fold (fun common _ p => common.filter (fun n t => p[n]? == some t)) first
    let mut atHead := true
    for op in b.ops do
      let some (n,t) := assignment sigs regs preds atHead op | return false
      if reserved.contains n then return false
      reserved := reserved.insert n
      regs := regs.insert n t
      match op with | .phi .. => pure () | _ => atHead := false
    let some dests := successors regs f.result b.exit | return false
    let mut edgeLabels : Std.HashSet String := {}
    for dst in dests do
      if edgeLabels.contains dst || visited.contains dst || !labels.contains dst then return false
      edgeLabels := edgeLabels.insert dst
      incoming := incoming.insert dst ((incoming.getD dst {}).insert b.label regs)
  return true

/-- Every phi operand is available at the identified predecessor. Ordinary
operands are available along every path, and calls name earlier typed bodies. -/
def Code.valid (c : Code) : Bool := Id.run do
  let mut sigs : Sigs := {}
  for f in c.functions do
    if (f.internal == (f.name == "main")) || sigs.contains f.name || !checkFn sigs f then return false
    sigs := sigs.insert f.name (f.params.map Prod.fst, f.result)
  return sigs["main"]? == some ([], .word)

end VastitasKernel.LLVM.FiniteModule
