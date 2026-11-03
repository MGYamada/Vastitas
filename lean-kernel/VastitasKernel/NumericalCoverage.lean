import VastitasKernel.StorageFunctions
import VastitasKernel.FiniteIndex
import Init.Data.List.Sort.Lemmas

/-! Positional coverage of the static numerical instructions of a public resource
execution. Calls expand into the caller's block. Each arm has its own block,
including the unselected arm. Receipts retain the prefix at the time of emission. -/
namespace VastitasKernel.Storage.NumericalCoverage
open Functions
attribute [local instance] lexOrd

inductive Family where
  | product | network | evaluation | tensor | cached | tree | adjoint | pairing
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable, Inhabited

private def family? : Functions.Statement → Option Family
  | .numerical (.gemm ..) => some .product
  | .network .. => some .network
  | .numerical (.evaluate ..) => some .evaluation
  | .tensor (.contract3 ..) => some .tensor
  | .tensor (.cachedContract3 ..) => some .cached
  | .tree .. => some .tree
  | .numerical (.adjointInto ..) => some .adjoint
  | .numerical (.hermitianDiagonal ..) => some .pairing
  | _ => none

/-- Innermost source statement followed by its exact call sites. -/
abbrev SourceKey := List NumericalSourceSite × Family

private structure Cursor where
  owner : Nat
  path : List Nat
  position : Nat
  callers : List NumericalSourceSite
  first : Functions.Statement
  rest : List Functions.Statement

private def push (owner : Nat) (path : List Nat) (position : Nat) (callers : List NumericalSourceSite)
    (body : List Functions.Statement) (todo : List Cursor) : List Cursor :=
  match body with
  | [] => todo
  | first :: rest => ⟨owner, path, position, callers, first, rest⟩ :: todo

/-- Traverse the reconstructed source independently, once per expanded statement.
The resource checker already spends at least one of its 4096 units per statement.
The lookup table preserves the actual function list's first-match semantics. -/
private def walk (functions : Std.HashMap Nat Function) :
    Nat → List Cursor → List SourceKey → Option (List SourceKey)
  | _, [], acc => some acc.reverse
  | 0, _ :: _, _ => none
  | fuel + 1, task :: pending, acc => do
    let next := push task.owner task.path (task.position + 1) task.callers task.rest pending
    let site : NumericalSourceSite := ⟨some task.owner, task.path ++ [task.position]⟩
    match task.first with
    | .call callee .. | .callValue callee .. =>
      let f ← functions[callee]?
      walk functions fuel (push f.id [] 0 (site :: task.callers) f.body next) acc
    | .branch _ yes no =>
      let right := push task.owner (task.path ++ [task.position, 1]) 0 task.callers no next
      walk functions fuel (push task.owner (task.path ++ [task.position, 0]) 0 task.callers yes right) acc
    | statement =>
      let acc := match family? statement with
        | some family => (site :: task.callers, family) :: acc
        | none => acc
      walk functions fuel next acc

def sourceTrace (functions : List Function) (entry : Nat) : Option (List SourceKey) := do
  let table := Finite.firstIndex Function.id functions
  let f ← table[entry]?
  walk table 4096 (push f.id [] 0 [] f.body []) []

abbrev Address := ScheduleBlock × Nat
abbrev Entry := Address × Action

def required : Action → Bool
  | .gemm _ | .diagonalAdjoint _ | .diagonalPair _ => true
  | _ => false

/-- The key is the actual branch path and offset in that block. -/
def entries (keep : Action → Bool) (block : ScheduleBlock) (start : Nat) :
    List Storage.Statement → List Entry
  | [] => []
  | .action a :: rest =>
    let tail := entries keep block (start + 1) rest
    if keep a then ((block, start), a) :: tail else tail
  | .branch _ yes no :: rest =>
    entries keep ((start, true) :: block) 0 yes ++
      entries keep ((start, false) :: block) 0 no ++ entries keep block (start + 1) rest

structure Slice where
  sites : List NumericalSourceSite
  family : Family
  address : Address
  code : List Storage.Statement

private def sliceAt {prior} (location : NumericalLocation prior) (family : Family)
    (code : List Storage.Statement) : Slice :=
  ⟨location.source :: location.callers, family, (location.block, location.start), code⟩

def Slice.sourceKey (s : Slice) : SourceKey := (s.sites, s.family)

def Slice.entries (s : Slice) (keep : Action → Bool) : List Entry :=
  NumericalCoverage.entries keep s.address.1 s.address.2 s.code

/-- Each constructor carries the original dependent checker receipt. The network
emitter also retains its shared product receipt, checked separately below. -/
inductive Origin where
  | product (receipt : NumericalReceipt)
  | network (receipt : NetworkReceipt)
  | evaluation (receipt : EvaluationReceipt)
  | tensor (receipt : TensorContractionReceipt)
  | cached (receipt : CachedContractionReceipt)
  | tree (receipt : TreeReceipt)
  | adjoint (receipt : AdjointIntoReceipt)
  | pairing (receipt : DiagonalPairingReceipt)

def Origin.slice : Origin → Slice
  | .product r => sliceAt r.location (if r.networkProduct then .network else .product)
      [.action (.gemm (r.checked.product.request r.mode r.policy))]
  | .network r => sliceAt r.location .network [.action (.gemm r.checked.request)]
  | .evaluation r => sliceAt r.location .evaluation (Numerical.evaluationCode
      r.checked.left r.checked.right r.leftChild r.rightChild r.output r.mode r.policy r.alpha r.beta)
  | .tensor r => sliceAt r.location .tensor [.action (.gemm
      (Tensor.contractionRequest r.checked.left r.checked.right r.checked.output r.policy))]
  | .cached r => sliceAt r.location .cached [.action (.requireDependency r.cache.name), .action (.gemm
      (Tensor.contractionRequest r.checked.contraction.left r.checked.contraction.right
        r.checked.contraction.output r.policy))]
  | .tree r => sliceAt r.location .tree (r.checked.finalState.code.map Storage.Statement.action)
  | .adjoint r => sliceAt r.location .adjoint [.action (.diagonalAdjoint
      (Numerical.adjointIntoRequest r.checked.input r.checked.output
        r.checked.sourceRealization.diagonal r.checked.targetRealization.diagonal r.policy))]
  | .pairing r => sliceAt r.location .pairing [.action (.diagonalPair
      (Numerical.diagonalPairRequest r.checked.left r.checked.right r.output r.scratch
        r.writeLoan r.readLoan r.leftChild r.layout r.checked.realization.diagonal r.policy))]

def origins (c : Context) : List Origin :=
  ((c.products.toList.filter fun r => !r.networkProduct).map .product) ++
    c.networks.toList.map .network ++ c.evaluations.toList.map .evaluation ++
    c.tensorContractions.toList.map .tensor ++ c.cachedContractions.toList.map .cached ++
    c.trees.toList.map .tree ++ c.adjoints.toList.map .adjoint ++ c.diagonalPairings.toList.map .pairing

/-- Sorting by the physical address avoids searching the entire receipt ledger
for every instruction. Equality compares the full operation and its operands. -/
def sameEntries [DecidableEq α] (address : α → Address) (actual recorded : List α) : Bool :=
  let order := fun a b => compare (address a) (address b) != .gt
  decide (actual.mergeSort order = recorded.mergeSort order)

theorem sameEntries_perm [DecidableEq α] {address : α → Address} {actual recorded : List α}
    (h : sameEntries address actual recorded = true) : actual.Perm recorded := by
  unfold sameEntries at h
  have equal := of_decide_eq_true h
  exact (List.mergeSort_perm actual _).symm.trans (equal ▸ List.mergeSort_perm recorded _)

def recorded (c : Context) : List Entry :=
  (origins c).flatMap fun origin => origin.slice.entries required

def tagged (items : List Origin) : List (Entry × SourceKey) :=
  items.flatMap fun origin => (origin.slice.entries required).map (·, origin.slice.sourceKey)

private instance : DecidableEq SourceKey :=
  inferInstanceAs (DecidableEq (List NumericalSourceSite × Family))

private instance : DecidableEq Entry := inferInstanceAs (DecidableEq (Address × Action))

def networkCompanions (c : Context) : Bool :=
  sameEntries (fun pair => pair.1.1) (tagged (c.networks.toList.map .network))
    (tagged ((c.products.toList.filter (·.networkProduct)).map .product))

/-- The complete accepted expansion of a composite receipt, including its
borrow/release and dependency instructions, must occupy its claimed cells. -/
def slicesMatch (code : List Storage.Statement) (items : List Origin) : Bool :=
  if items.isEmpty then true else
    let cells := Std.HashMap.ofList (entries (fun _ => true) [] 0 code)
    items.all fun origin => (origin.slice.entries (fun _ => true)).all fun (address, action) =>
      decide (cells[address]? = some action)

/-- Lexical order of the actual emitted program, left arm before right arm. -/
def orderKey (address : Address) : List Nat :=
  address.1.reverse.flatMap (fun (offset, yes) => [offset, if yes then 0 else 1]) ++ [address.2]

def originTrace (items : List Origin) : List SourceKey :=
  let keyed := items.map fun o => (orderKey o.slice.address, o.slice.sourceKey)
  (keyed.mergeSort fun a b => compare a.1 b.1 != .gt).map Prod.snd

def audit (functions : List Function) (entry : Nat) (c : Context) : Bool :=
  let code := c.code.toList
  let items := origins c
  sameEntries Prod.fst (entries required [] 0 code) (recorded c) &&
    decide (sourceTrace functions entry = some (originTrace items)) &&
    slicesMatch code items && networkCompanions c

end VastitasKernel.Storage.NumericalCoverage
