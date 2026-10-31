import VastitasKernel.StorageNumerical

/-! Finite coordinate tensors over the accepted real/complex numerical profile.
Axes retain actual bases, including corresponding dual origins. Grouping changes
physical coordinates, never nominal objects or factor ownership. This first
profile has explicit rank-three packing and rank-three/rank-two contraction. -/
namespace VastitasKernel.Storage.Tensor
open Numerical

def unpacked : Grouping := ⟨[0, 1, 2], 1⟩
def packed : Grouping := ⟨[0, 2, 1], 2⟩
def boundary : Grouping := ⟨[0, 1, 2], 2⟩
def matrix : Grouping := ⟨[0, 1], 1⟩

structure View where
  axes : List Basis
  grouping : Grouping
  loan : Loan
  deriving Repr, BEq, DecidableEq, Inhabited

def View.dimension (view : View) (axis : Nat) : Nat :=
  ((view.axes[axis]?).map (·.space.dimension)).getD 0

def View.extent (view : View) (axes : List Nat) : Nat :=
  (axes.map view.dimension).foldl (· * ·) 1

def View.rows (view : View) : Nat := view.extent (view.grouping.order.take view.grouping.split)
def View.columns (view : View) : Nat := view.extent (view.grouping.order.drop view.grouping.split)

/-- First axis is fastest within each explicitly ordered rectangle group. -/
def View.flatten (view : View) (indices order : List Nat) : Nat :=
  order.foldr (fun axis next => (indices[axis]?).getD 0 + view.dimension axis * next) 0

def View.coordinate (view : View) (indices : List Nat) : Nat × Nat :=
  (view.flatten indices (view.grouping.order.take view.grouping.split),
    view.flatten indices (view.grouping.order.drop view.grouping.split))

def View.address (view : View) (scalar : Scalar) (indices : List Nat) : Nat :=
  let (row, column) := view.coordinate indices
  view.loan.layout.address scalar row column

def sameProfile (left right : Basis) : Prop :=
  left.space.type = right.space.type ∧ left.space.base = right.space.base ∧
  left.space.coefficient = right.space.coefficient ∧ left.space.setting = right.space.setting
instance (left right : Basis) : Decidable (sameProfile left right) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def View.Valid (numerical : Numerical.Values) (view : View) : Prop :=
  (view.axes.length = 2 ∨ view.axes.length = 3) ∧ view.grouping.Valid view.axes.length ∧
  (∀ basis ∈ view.axes, value? numerical basis.brand = some (.basis basis) ∧ basis.space.dimension ≤ dimensionLimit) ∧
  (∀ left ∈ view.axes, ∀ right ∈ view.axes, sameProfile left right)
instance (numerical : Numerical.Values) (view : View) : Decidable (view.Valid numerical) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def View.Live (resources : State) (view : View) : Prop :=
  resources.loan? view.loan.name = some view.loan ∧ resources.suspended view.loan.name = false ∧
  (resources.allocation? view.loan.allocation).map Allocation.scalar =
    (view.axes.head?).map (·.space.scalar) ∧
  view.loan.layout.transposed = false ∧
  view.loan.layout.rows = view.rows ∧ view.loan.layout.columns = view.columns
instance (resources : State) (view : View) : Decidable (view.Live resources) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def View.Initialized (resources : State) (view : View) : Bool :=
  (resources.allocation? view.loan.allocation).any fun allocation =>
    allocation.initialization.covers allocation.scalar view.loan.layout

abbrev Values := List (Symbol × View)
def lookup (values : Values) (name : Symbol) : Option View := (values.find? (·.1 == name)).map Prod.snd

def Valid (environment : Indexed.Environment) (numerical : Numerical.Values) (values : Values) : Prop :=
  Numerical.Valid environment numerical ∧ values.length ≤ 4096 ∧ (values.map Prod.fst).Nodup ∧
  ∀ entry ∈ values, entry.2.Valid numerical
instance (environment : Indexed.Environment) (numerical : Numerical.Values) (values : Values) :
    Decidable (Valid environment numerical values) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive Operation (Name : Type := Symbol) where
  | view (name loan : Name) (axes : List Name) (grouping : Grouping)
  | cachedPack (name source target : Name)
  | cachedContract3 (cache left right output : Name) (policy : NumericalPolicy)
  | pack (source target : Name)
  | contract3 (left right output : Name) (policy : NumericalPolicy)
  deriving Repr, BEq, Inhabited

private def reject (message : String) : Except Error α := .error ⟨"E_TENSOR", message⟩

structure CheckedView (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (axes : List Symbol) (grouping : Grouping) (loan : Symbol) where
  numericalValid : Numerical.Valid environment numerical
  resourcesValid : auditState resources = true
  view : View
  axesFrom : view.axes.map Basis.brand = axes
  groupingFrom : view.grouping = grouping
  loanFrom : view.loan.name = loan
  valid : view.Valid numerical
  live : view.Live resources

def checkView (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (axes : List Symbol) (grouping : Grouping) (loan : Symbol) :
    Except Error (CheckedView environment numerical resources axes grouping loan) := do
  unless axes.length == 2 || axes.length == 3 do reject "tensor views require two or three ordered axes"
  if numericalValid : Numerical.Valid environment numerical then
    if resourcesValid : auditState resources then
      let bases ← axes.mapM fun name => match value? numerical name with
        | some (.basis basis) => pure basis
        | _ => reject "tensor axis requires an actual local basis"
      let some actual := resources.loan? loan | reject "tensor requires a live rectangular loan"
      let view : View := ⟨bases, grouping, actual⟩
      if axesFrom : view.axes.map Basis.brand = axes then
        if loanFrom : view.loan.name = loan then
          if valid : view.Valid numerical then
            if live : view.Live resources then
              return ⟨numericalValid, resourcesValid, view, axesFrom, rfl, loanFrom, valid, live⟩
            else reject "tensor grouping differs from its actual rectangular loan"
          else reject "invalid tensor axes, profile or grouping permutation"
        else reject "tensor loan lost its actual identity"
      else reject "tensor axis identities differ from the actual bases"
    else reject "invalid tensor resource state"
  else reject "invalid tensor declaration or basis provenance"

def packAction (view target : View) : Action :=
  .pack3 view.loan.name target.loan.name (view.dimension 0) (view.dimension 1) (view.dimension 2)

structure CheckedPack (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (source target : Symbol) where
  valuesValid : Valid environment numerical values
  input : View
  output : View
  inputFrom : lookup values source = some input
  outputFrom : lookup values target = some output
  inputLive : input.Live resources
  outputLive : output.Live resources
  rank : input.axes.length = 3
  axes : output.axes = input.axes
  grouping : input.grouping = unpacked ∧ output.grouping = packed
  after : State
  accepted : checkAction resources (packAction input output) = .ok after
  inputRestored : input.Live after
  outputInitialized : output.Initialized after = true

def checkPack (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (source target : Symbol) :
    Except Error (CheckedPack environment numerical resources values source target) := do
  if valid : Valid environment numerical values then
    match inputFrom : lookup values source, outputFrom : lookup values target with
    | some input, some output =>
      if inputLive : input.Live resources then
        if outputLive : output.Live resources then
          if rank : input.axes.length = 3 then
            if axes : output.axes = input.axes then
              if grouping : input.grouping = unpacked ∧ output.grouping = packed then
                match accepted : checkAction resources (packAction input output) with
                | .error error => .error error
                | .ok after =>
                  if restored : input.Live after then
                    if initialized : output.Initialized after then
                      return ⟨valid, input, output, inputFrom, outputFrom, inputLive, outputLive,
                        rank, axes, grouping, after, accepted, restored, initialized⟩
                    else reject "packing failed to initialize its exact destination"
                  else reject "packing changed its input loan"
              else reject "pack3 requires axis groups [0 | 1,2] to [0,2 | 1]"
            else reject "packing cannot change nominal axis bases or their order"
          else reject "pack3 requires exactly three axes"
        else reject "packing destination is stale or suspended"
      else reject "packing input is stale or suspended"
    | _, _ => reject "packing requires actual tensor views"
  else reject "invalid tensor value provenance"

/-- Only an actual accepted packing followed by reconstructed dependency
capture creates this nominal cache. Raw dependency capture proves no packing. -/
structure Cache where
  environment : Indexed.Environment
  numerical : Numerical.Values
  before : State
  values : Values
  source : Symbol
  target : Symbol
  checked : CheckedPack environment numerical before values source target
  accepted : checkPack environment numerical before values source target = .ok checked
  name : Symbol
  after : State
  captured : checkAction checked.after (.captureDependency name checked.input.loan.name checked.output.loan.name) = .ok after
  dependency : Dependency
  selected : after.dependency? name = some ⟨name, some dependency⟩

def captureCache {environment numerical before values source target}
    (checked : CheckedPack environment numerical before values source target)
    (accepted : checkPack environment numerical before values source target = .ok checked)
    (name : Symbol) : Except Error Cache := do
  match captured : checkAction checked.after (.captureDependency name checked.input.loan.name checked.output.loan.name) with
  | .error error => .error error
  | .ok after =>
    match selected : after.dependency? name with
    | some ⟨actual, some dependency⟩ =>
      if equal : actual = name then
        return ⟨environment, numerical, before, values, source, target, checked, accepted,
          name, after, captured, dependency, equal ▸ selected⟩
      else reject "packing dependency lost its fresh identity"
    | _ => reject "packing did not capture its actual post-write dependency"

/-- This is corresponding algebraic dual evaluation, never a dimension-only
match or a conjugate-space/metric conversion. -/
def DualPair (dual primal : Basis) : Prop :=
  dual.parent = some primal.brand ∧ dual.space.origin = .dual primal.space.brand
instance (dual primal : Basis) : Decidable (DualPair dual primal) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ContractionAxes (left right output : View) : Prop :=
  match left.axes, right.axes with
  | [a, d, b], [v, c] => output.axes = [a, b, c] ∧ DualPair d v
  | _, _ => False
instance (left right output : View) : Decidable (ContractionAxes left right output) := by
  unfold ContractionAxes
  split <;> infer_instance

def contractionRequest (left right output : View) (policy : NumericalPolicy) : Gemm :=
  ⟨left.loan.name, right.loan.name, output.loan.name, false, false, .overwrite, policy, none, none⟩

structure CheckedContraction (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (leftName rightName outputName : Symbol) (policy : NumericalPolicy) where
  valuesValid : Valid environment numerical values
  left : View
  right : View
  output : View
  leftFrom : lookup values leftName = some left
  rightFrom : lookup values rightName = some right
  outputFrom : lookup values outputName = some output
  axes : ContractionAxes left right output
  grouping : left.grouping = packed ∧ right.grouping = matrix ∧ output.grouping = boundary
  leftLive : left.Live resources
  rightLive : right.Live resources
  outputLive : output.Live resources
  storage : CheckedGemm resources (contractionRequest left right output policy)
  storageAccepted : checkGemm resources (contractionRequest left right output policy) = .ok storage
  after : State
  accepted : checkAction resources (.gemm (contractionRequest left right output policy)) = .ok after

def checkContraction (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (leftName rightName outputName : Symbol) (policy : NumericalPolicy) :
    Except Error (CheckedContraction environment numerical resources values leftName rightName outputName policy) := do
  if valid : Valid environment numerical values then
    match leftFrom : lookup values leftName, rightFrom : lookup values rightName, outputFrom : lookup values outputName with
    | some left, some right, some output =>
      if axes : ContractionAxes left right output then
        if grouping : left.grouping = packed ∧ right.grouping = matrix ∧ output.grouping = boundary then
          if leftLive : left.Live resources then
            if rightLive : right.Live resources then
              if outputLive : output.Live resources then
                match storageAccepted : checkGemm resources (contractionRequest left right output policy) with
                | .error error => .error error
                | .ok storage => match accepted : checkAction resources (.gemm (contractionRequest left right output policy)) with
                  | .error error => .error error
                  | .ok after => return ⟨valid, left, right, output, leftFrom, rightFrom, outputFrom,
                      axes, grouping, leftLive, rightLive, outputLive, storage, storageAccepted, after, accepted⟩
              else reject "tensor contraction output is stale or suspended"
            else reject "tensor contraction right input is stale or suspended"
          else reject "tensor contraction left input is stale or suspended"
        else reject "contract3 requires groups [0,2 | 1], [0 | 1], and [0,1 | 2]; packing must be explicit"
      else reject "contract3 requires corresponding dual axes left[1]/right[0] and exact ordered boundary [left[0],left[2],right[1]]"
    | _, _, _ => reject "contract3 requires actual tensor views"
  else reject "invalid tensor value provenance"

structure CheckedCachedContraction (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (cache : Cache)
    (left right output : Symbol) (policy : NumericalPolicy) where
  environmentFrom : cache.environment = environment
  dependency : resources.dependency? cache.name = some ⟨cache.name, some cache.dependency⟩
  required : checkAction resources (.requireDependency cache.name) = .ok resources
  contraction : CheckedContraction environment numerical resources values left right output policy
  accepted : checkContraction environment numerical resources values left right output policy = .ok contraction
  axes : contraction.left.axes = cache.checked.output.axes
  grouping : contraction.left.grouping = cache.checked.output.grouping
  allocation : contraction.left.loan.allocation = cache.checked.output.loan.allocation
  layout : contraction.left.loan.layout = cache.checked.output.loan.layout

def checkCachedContraction (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (values : Values) (cache : Cache)
    (left right output : Symbol) (policy : NumericalPolicy) :
    Except Error (CheckedCachedContraction environment numerical resources values cache left right output policy) := do
  if environmentFrom : cache.environment = environment then
    if dependency : resources.dependency? cache.name = some ⟨cache.name, some cache.dependency⟩ then
      match required : checkAction resources (.requireDependency cache.name) with
      | .error error => .error error
      | .ok requiredState =>
        if sameState : requiredState = resources then
          match accepted : checkContraction environment numerical resources values left right output policy with
          | .error error => .error error
          | .ok contraction =>
            if axes : contraction.left.axes = cache.checked.output.axes then
              if grouping : contraction.left.grouping = cache.checked.output.grouping then
                if allocation : contraction.left.loan.allocation = cache.checked.output.loan.allocation then
                  if layout : contraction.left.loan.layout = cache.checked.output.loan.layout then
                    return ⟨environmentFrom, dependency, sameState ▸ required, contraction, accepted, axes, grouping, allocation, layout⟩
                  else reject "cached packed operand has a different physical layout"
                else reject "cached packed operand has a different allocation"
              else reject "cached packed operand has a different axis grouping"
            else reject "cached packed operand has different nominal axes"
        else reject "cached dependency changed resource state"
    else reject "cached source or scratch was changed, dropped or invalidated at a branch join"
  else reject "cache has a different declaration environment"

end VastitasKernel.Storage.Tensor
