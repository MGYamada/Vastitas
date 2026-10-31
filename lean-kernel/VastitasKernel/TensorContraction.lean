import VastitasKernel.TensorNumerical

/-! Explicit regrouping and one-axis contractions for finite rank-two/three
coordinate tensors. The written operand order is retained. No metric, conjugation,
factor ownership, allocation, or nominal grouped basis is inferred. -/
namespace VastitasKernel.Storage.Tensor
open Numerical

def View.dimensions (view : View) : List Nat := view.axes.map (·.space.dimension)

/-- Rank-two physical rectangles use a trailing unit extent in the bounded
native permutation descriptor. This is not a logical axis or nominal basis. -/
def View.regroupDimensions (view : View) : List Nat :=
  if view.axes.length == 2 then view.dimensions ++ [1] else view.dimensions

def View.regroupGrouping (view : View) : Grouping :=
  if view.axes.length == 2 then ⟨view.grouping.order ++ [2], view.grouping.split⟩ else view.grouping

def regroupAction (input output : View) : Action :=
  if input.grouping == unpacked && output.grouping == packed then packAction input output
  else .regroup3 input.loan.name output.loan.name input.regroupDimensions input.regroupGrouping output.regroupGrouping

structure CheckedRegroup (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (input output : View) where
  numericalValid : Numerical.Valid environment numerical
  inputValid : input.Valid numerical
  outputValid : output.Valid numerical
  inputLive : input.Live resources
  outputLive : output.Live resources
  rank : input.axes.length = 2 ∨ input.axes.length = 3
  axes : output.axes = input.axes
  after : State
  accepted : checkAction resources (regroupAction input output) = .ok after
  inputRestored : input.Live after
  outputInitialized : output.Initialized after = true

private def reject (message : String) : Except Error α := .error ⟨"E_TENSOR", message⟩

def checkRegroup (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (input output : View) :
    Except Error (CheckedRegroup environment numerical resources input output) := do
  if numericalValid : Numerical.Valid environment numerical then
    if inputValid : input.Valid numerical then
      if outputValid : output.Valid numerical then
        if inputLive : input.Live resources then
          if outputLive : output.Live resources then
            if rank : input.axes.length = 2 ∨ input.axes.length = 3 then
              if axes : output.axes = input.axes then
                match accepted : checkAction resources (regroupAction input output) with
                | .error error => .error error
                | .ok after =>
                  if restored : input.Live after then
                    if initialized : output.Initialized after = true then
                      return ⟨numericalValid, inputValid, outputValid, inputLive, outputLive,
                        rank, axes, after, accepted, restored, initialized⟩
                    else reject "regrouping failed to initialize its exact destination"
                  else reject "regrouping changed its input loan"
              else reject "regrouping cannot change ordered nominal axes"
            else reject "regroup requires exactly two or three logical axes"
          else reject "regrouping destination is stale or suspended"
        else reject "regrouping input is stale or suspended"
      else reject "regrouping destination has invalid axes or grouping"
    else reject "regrouping input has invalid axes or grouping"
  else reject "regrouping lost its accepted numerical declaration environment"

def freeAxes (rank axis : Nat) : List Nat := (List.range rank).filter (· != axis)
def leftGrouping (rank axis : Nat) : Grouping := ⟨freeAxes rank axis ++ [axis], rank - 1⟩
def rightGrouping (rank axis : Nat) : Grouping := ⟨axis :: freeAxes rank axis, 1⟩
def resultGrouping (leftRank rightRank : Nat) : Grouping :=
  ⟨List.range (leftRank + rightRank - 2), leftRank - 1⟩

def selectedPair (left right : View) (leftAxis rightAxis : Nat) : Prop :=
  match left.axes[leftAxis]?, right.axes[rightAxis]? with
  | some a, some b => DualPair a b ∨ DualPair b a
  | _, _ => False
instance (left right : View) (leftAxis rightAxis : Nat) :
    Decidable (selectedPair left right leftAxis rightAxis) := by
  unfold selectedPair
  split <;> infer_instance

def resultAxes (left right : View) (leftAxis rightAxis : Nat) : List Basis :=
  left.axes.eraseIdx leftAxis ++ right.axes.eraseIdx rightAxis

structure CheckedSingle (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (left right output : View) (leftAxis rightAxis : Nat) (policy : NumericalPolicy) where
  numericalValid : Numerical.Valid environment numerical
  leftValid : left.Valid numerical
  rightValid : right.Valid numerical
  outputValid : output.Valid numerical
  selected : selectedPair left right leftAxis rightAxis
  axes : output.axes = resultAxes left right leftAxis rightAxis
  grouping : left.grouping = leftGrouping left.axes.length leftAxis ∧
    right.grouping = rightGrouping right.axes.length rightAxis ∧
    output.grouping = resultGrouping left.axes.length right.axes.length
  leftLive : left.Live resources
  rightLive : right.Live resources
  outputLive : output.Live resources
  storage : CheckedGemm resources (contractionRequest left right output policy)
  storageAccepted : checkGemm resources (contractionRequest left right output policy) = .ok storage
  after : State
  accepted : checkAction resources (.gemm (contractionRequest left right output policy)) = .ok after
  outputInitialized : output.Initialized after = true

def checkSingle (environment : Indexed.Environment) (numerical : Numerical.Values)
    (resources : State) (left right output : View) (leftAxis rightAxis : Nat) (policy : NumericalPolicy) :
    Except Error (CheckedSingle environment numerical resources left right output leftAxis rightAxis policy) := do
  if numericalValid : Numerical.Valid environment numerical then
    if leftValid : left.Valid numerical then
      if rightValid : right.Valid numerical then
        if outputValid : output.Valid numerical then
          if selected : selectedPair left right leftAxis rightAxis then
            if axes : output.axes = resultAxes left right leftAxis rightAxis then
              if grouping : left.grouping = leftGrouping left.axes.length leftAxis ∧
                  right.grouping = rightGrouping right.axes.length rightAxis ∧
                  output.grouping = resultGrouping left.axes.length right.axes.length then
                if leftLive : left.Live resources then
                  if rightLive : right.Live resources then
                    if outputLive : output.Live resources then
                      match storageAccepted : checkGemm resources (contractionRequest left right output policy) with
                      | .error error => .error error
                      | .ok storage => match accepted : checkAction resources (.gemm (contractionRequest left right output policy)) with
                        | .error error => .error error
                        | .ok after =>
                          if initialized : output.Initialized after = true then
                            return ⟨numericalValid, leftValid, rightValid, outputValid, selected, axes, grouping,
                              leftLive, rightLive, outputLive, storage, storageAccepted, after, accepted, initialized⟩
                          else reject "contraction failed to initialize its exact destination"
                    else reject "contraction output is stale or suspended"
                  else reject "contraction right input is stale or suspended"
                else reject "contraction left input is stale or suspended"
              else reject "contract_axis requires explicit free/contracted axis grouping; regrouping is never implicit"
            else reject "contraction destination must preserve ordered free-left then free-right axes and have rank two or three"
          else reject "selected contraction legs require actual corresponding dual/primal bases"
        else reject "contraction output has invalid axes or grouping"
      else reject "contraction right input has invalid axes or grouping"
    else reject "contraction left input has invalid axes or grouping"
  else reject "contraction lost its accepted numerical declaration environment"

end VastitasKernel.Storage.Tensor
