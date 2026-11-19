import VastitasKernel.MidIR.IR

set_option autoImplicit false

namespace VastitasKernel.MidIR
variable {p : Phase}

private def Block.slotType (b : Block p) (slot : Nat) : Option Ty :=
  if slot < b.params.size then b.params[slot]?
  else (b.ops[slot - b.params.size]?).map (·.code.result)

/-- The finite Core fragment has structured, acyclic control flow. Block
order must be topological. Each incoming edge contributes its dominators;
intersection prevents a definition on only one arm from reaching a join. -/
def validFunction (env : Indexed.Environment) (f : Function p) : Bool := Id.run do
  let some entry := f.blocks[0]? | return false
  unless entry.params == f.params && f.result.valid env do return false
  let mut incoming : Array (Option (Std.HashSet Nat)) := Array.replicate f.blocks.size none
  incoming := incoming.set! 0 (some {})
  for h : i in [:f.blocks.size] do
    let block := f.blocks[i]
    let some dom := incoming[i]?.join | return false
    unless block.params.all (·.valid env) do return false
    let lookup (limit : Nat) (r : Ref) : Option Ty := do
      if r.block == i then guard (r.slot < limit) else guard (dom.contains r.block)
      (← f.blocks[r.block]?).slotType r.slot
    for j in [:block.ops.size] do
      let some op := block.ops[j]? | return false
      unless op.code.valid env && op.args.mapM (lookup (block.params.size + j)) == some op.code.operands do
        return false
    let read := lookup (block.params.size + block.ops.size)
    let edges ← match block.term with
      | .ret token value =>
        if token.block != i || read value != some f.result then return false
        pure []
      | .jump edge => pure [edge]
      | .branch condition yes no =>
        if read condition != some .bool || yes.dest == no.dest then return false
        pure [yes, no]
    let nextDom := dom.insert i
    for edge in edges do
      let some target := f.blocks[edge.dest]? | return false
      unless i < edge.dest && edge.token.block == i &&
          edge.args.mapM read == some target.params.toList do return false
      let merged := match incoming[edge.dest]?.join with
        | none => nextDom
        | some earlier => earlier.inter nextDom
      incoming := incoming.set! edge.dest (some merged)
  return true

/-- Every Core symbol and specialization is unique. Distinct checked methods
can share the family FunctionId. Calls must match the full target, including
that family, its specialization key, and ABI. -/
def validSymbols (m : Module p) : Bool := Id.run do
  if let some id := m.entry then
    let some main := m.functions[id]? | return false
    unless main.id.owner.name == "main" && main.id.owner.scope.path.isEmpty &&
        main.params.isEmpty && main.result == .int do return false
  let mut keys : Std.HashSet Indexed.FunctionSource.Compiler.Key := {}
  for (f, i) in m.functions.toList.zipIdx do
    unless f.coreId == i && (f.specialization.targets.all fun t => !t.isProbe) &&
        !keys.contains f.specialization do return false
    for block in f.blocks do
      for op in block.ops do
        if let .call target := op.code then
          let some callee := m.functions[target.symbol]? | return false
          unless target.symbol < i && decide (callee.target = target) do return false
    keys := keys.insert f.specialization
  return true

def Op.execute (env : Indexed.Environment) (op : Op .optimization) : Option (Op .execution) := do
  return ⟨← op.code.execute env, op.args⟩

def Block.execute (env : Indexed.Environment) (b : Block .optimization) :
    Option (Block .execution) := do
  let ops ← b.ops.mapM (Op.execute env)
  return { b with ops }

def Function.execute (env : Indexed.Environment) (f : Function .optimization) :
    Option (Function .execution) := do
  guard (validFunction env f)
  let blocks ← f.blocks.mapM (Block.execute env)
  let out := { f with blocks : Function .execution }
  guard (validFunction env out)
  return out

def Module.execute (m : Module .optimization) : Option (Module .execution) := do
  guard (validSymbols m)
  let functions ← m.functions.mapM (Function.execute m.env)
  return { m with functions }

end VastitasKernel.MidIR
