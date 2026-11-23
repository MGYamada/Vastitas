import VastitasKernel.IndexedSemantics
import VastitasKernel.Limits

set_option autoImplicit false

/-! Bound the cost of observing the closed, pure finite entry before running
the existing Core semantics. A shared callee contributes its cost separately
at every syntactic call site. Independent branch arms are both charged. -/
namespace VastitasKernel.LLVM.FiniteCost
open Indexed Indexed.Core Indexed.Core.Semantics

private def outside : Nat := Limits.elaborationWork + 1

/-- Size of the checked declarations used to recover table data at run time.
Direct tables charge their own axes, rows and output. Recovering a projected
Hom or Monad also rebuilds finite model maps from the declaration environment. -/
private structure Sizes where
  symbols : Nat
  declarations : Nat
  model : Nat
  rows : Std.HashMap DeclId Nat
  arrows : Std.HashMap DeclId Nat
  oppositeWork : Std.HashMap DeclId Nat

private def sizes (m : Module) : Sizes := Id.run do
  let env := m.declarations.indexed
  let mut rows := {}
  let mut model := env.length
  for item in env do
    let n := match item.declaration with
      | .finiteCarrier tags => tags.length
      | .finiteTable axes _ data | .composableTable axes _ _ _ data =>
        (axes.length + 1) * data.length
      | _ => 0
    if n > 0 then rows := rows.insert item.id n
    model := model + n
  let mut arrows := {}
  for item in env do
    if let .finiteCategory _ graph := item.declaration then
      arrows := arrows.insert item.id (rows.getD graph.arrows 0)
  let views := env.filter fun entry => match entry.declaration with
    | .finiteOpposite .. => true
    | _ => false
  let mut oppositeWork := {}
  if !views.isEmpty then
    let byId := Std.HashMap.ofList (env.map fun entry => (entry.id, entry.declaration))
    -- A view can cross at most this many distinct declarations in an accepted graph.
    let scan := env.length * min views.length (Limits.namespaceResolution + 1)
    for item in views do
      oppositeWork := oppositeWork.insert item.id scan
      if let some (_, fields, _) := FiniteCategories.describe (fun id => byId[id]?)
          (Limits.namespaceResolution + 1) item.id then
        arrows := arrows.insert item.id (rows.getD fields.arrows 0)
  return ⟨m.functions.length, env.length, model, rows, arrows, oppositeWork⟩

private def sortWork (s : Sizes) : FiniteSort → Nat
  | .carrier id => s.declarations + s.rows.getD id 0
  | .hom owner .. => s.model + s.oppositeWork.getD owner 0

private def lookupWork (s : Sizes) (site : FiniteLookup) : Nat :=
  let rows := s.rows.getD site.table 0
  let axes := (site.inputs.map (sortWork s)).sum
  let base := s.declarations + rows + axes + sortWork s site.output
  match site.category, site.inputs with
  | none, _ => base
  | some category, [_, _] =>
    -- restrictComposition checks membership in the output Hom for each row.
    -- A binary table has three cells per row. Its output fiber is a subset
    -- of the selected category's arrow carrier.
    base + s.model + s.oppositeWork.getD category 0 + (rows / 3) * s.arrows.getD category 0
  | some _, _ => base + s.model

private structure Work where
  nodes : Nat
  units : Nat
  deriving Inhabited

private def atom (nodes : Nat) (extra : Nat := 0) : Work := ⟨nodes, nodes + extra⟩

private instance : Add Work := ⟨fun a b => ⟨a.nodes + b.nodes, a.units + b.units⟩⟩

private def localWork (exact : Bool) (s : Sizes) : Indexed.Core.Term → Work
  | .unit | .integer _ | .natural _ | .boolean _ | .variable .. => atom 1
  | .natToInt arg => if exact then atom 1 + localWork exact s arg else atom outside
  | .pair _ a b => if exact then atom 1 + localWork exact s a + localWork exact s b else atom outside
  | .project _ _ a => if exact then atom 1 + localWork exact s a else atom outside
  | .finiteTag t _ => atom 1 (sortWork s t)
  | .finiteLookup site args => atom (1 + args.length) (lookupWork s site)
  | .unary .neg (.integer _) _ => atom 2
  | .unary .neg arg _ => if exact then atom 1 + localWork exact s arg else atom outside
  | .unary .not arg _ => atom 1 + localWork exact s arg
  | .binary op a b _ =>
    match op with
    | .eq | .ne | .and | .or => atom 1 + localWork exact s a + localWork exact s b
    | .add | .sub | .mul | .div | .lt | .le | .gt | .ge =>
      if exact then atom 1 + localWork exact s a + localWork exact s b else atom outside
  | .call _ args [] _ => args.foldl (fun w t => w + localWork exact s t) (atom 1 s.symbols)
  | .scope body | .ascribe _ body => atom 1 + localWork exact s body
  | .letE _ a b => atom 1 + localWork exact s a + localWork exact s b
  | .branch c a b _ => atom 1 + localWork exact s c + localWork exact s a + localWork exact s b
  | _ => atom outside

private structure FunctionCost where
  localCost : Work
  calls : List Nat

private abbrev Costs := Std.HashMap Nat Work

private def expanded (fs : Array FunctionCost) : Nat → Nat → StateT Costs Option Work
  | 0, _ => failure
  | depth+1, id => do
    if let some known := (← get)[id]? then return known
    let cost ← liftM (fs[id]?)
    let mut work := cost.localCost
    guard (work.units ≤ Limits.elaborationWork)
    for callee in cost.calls do
      work := work + (← expanded fs depth callee)
      guard (work.units ≤ Limits.elaborationWork)
    modify (·.insert id work)
    return work

/-- The checked Core symbol table is dense. Repeated calls each pay for their
callee's complete table work. Only the node count is used as execution fuel. -/
def entryWith (exact : Bool) (m : Module) : Option Nat := do
  let start ← m.main
  let s := sizes m
  let costs ← m.functions.zipIdx.mapM fun (f, symbol) => do
    guard (f.id == symbol)
    return FunctionCost.mk (localWork exact s f.body) f.body.callIds
  let cost ← (expanded costs.toArray costs.length start).run' {}
  return cost.nodes

def entry := entryWith false

/-- Enter by the actual symbol and parameter binder of the accepted Core. -/
def coreEntry (m : Module) (fuel : Nat) : Option Value := do
  let id ← m.main
  let f ← m.functions.find? (·.id == id)
  eval m fuel (← bindArguments f.parameters []) f.body

structure Observation (m : Module) where
  fuel : Nat
  value : Int
  budget : entry m = some fuel
  evaluated : coreEntry m fuel = some (.integer value)

def observe (m : Module) : Option (Observation m) :=
  match h : entry m with
  | none => none
  | some fuel => match e : coreEntry m fuel with
    | some (.integer value) => some ⟨fuel, value, h, e⟩
    | _ => none

end VastitasKernel.LLVM.FiniteCost
