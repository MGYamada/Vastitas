import VastitasKernel.StorageNumerical

/-! Actual nominal vector evaluation and its resource schedule. Dual evaluation
is bilinear; a Hermitian pairing consumes an explicitly conjugated-space vector.
Neither operation invents a metric, conjugation, allocation or packing buffer. -/
namespace VastitasKernel.Storage.Numerical
open Indexed

private def reject (message : String) : Except Error α :=
  .error ⟨"E_NUMERICAL_TYPE", message⟩

structure CheckedVectorConjugate (env : Environment) (resources : State) (values : Values)
    (name parent child basis selected : Symbol) where
  valuesValid : Valid env values
  original : VectorView
  fromParent : value? values parent = some (.vector original)
  originalLive : original.Live resources
  result : VectorView
  after : State
  borrowed : checkAction resources (.borrow child (.loan original.loan.name) original.loan.layout .read) = .ok after
  resultLoan : after.loan? child = some result.loan
  resultName : result.loan.name = child
  resultBasis : value? values basis = some (.basis result.basis)
  resultOrigin : result.origin = .conjugate parent selected
  resultFlags : result.conjugate = !original.conjugate
  coordinates : result.loan.layout = original.loan.layout ∧ result.loan.allocation = original.loan.allocation ∧
    result.loan.parent = some original.loan.name ∧ result.loan.access = .read
  output : Values
  inserted : insert env values name (.vector result) = .ok output
  outputValid : Valid env output
  fromOutput : value? output name = some (.vector result)
  resultLive : result.Live after

def checkVectorConjugate (env : Environment) (resources : State) (values : Values)
    (name parent child basis selected : Symbol) :
    Except Error (CheckedVectorConjugate env resources values name parent child basis selected) := do
  if valuesValid : Valid env values then
    match fromParent : value? values parent, resultBasis : value? values basis with
    | some (.vector original), some (.basis target) =>
      if originalLive : original.Live resources then
        match borrowed : checkAction resources (.borrow child (.loan original.loan.name) original.loan.layout .read) with
        | .error diagnostic => .error diagnostic
        | .ok after =>
          match resultLoan : after.loan? child with
          | none => reject "conjugated vector lost its checked child loan"
          | some loan =>
            let result : VectorView := ⟨target, loan, !original.conjugate, .conjugate parent selected⟩
            match inserted : insert env values name (.vector result) with
            | .error diagnostic => .error diagnostic
            | .ok output =>
              if outputValid : Valid env output then
                if fromOutput : value? output name = some (.vector result) then
                  if resultLive : result.Live after then
                    if resultName : result.loan.name = child then
                      if coordinates : result.loan.layout = original.loan.layout ∧ result.loan.allocation = original.loan.allocation ∧
                          result.loan.parent = some original.loan.name ∧ result.loan.access = .read then
                        return ⟨valuesValid, original, fromParent, originalLive, result, after, borrowed,
                          resultLoan, resultName, resultBasis, rfl, rfl, coordinates, output, inserted, outputValid,
                          fromOutput, resultLive⟩
                      else reject "conjugated vector changed its coordinates or read permission"
                    else reject "conjugated vector lost its child identity"
                  else reject "conjugated vector is not live"
                else reject "conjugated vector was not retained"
              else reject "conjugated vector has invalid origin or basis"
      else reject "vector no longer matches its live loan"
    | _, _ => reject "vector conjugation requires an actual vector and corresponding conjugate basis"
  else reject "invalid numerical value provenance"

def Evaluation.Accepts (values : Values) (left right : VectorView) : Evaluation → Prop
  | .dual => left.basis.parent = some right.basis.brand ∧
      left.basis.space.origin = .dual right.basis.space.brand
  | .hermitian selected => match value? values selected with
    | some (.metric form) => form.basis = right.basis ∧ form.orthonormal = true ∧
        left.basis.parent = some right.basis.brand ∧
        left.basis.space.origin = .conjugate right.basis.space.brand form.selected
    | _ => False

instance (values : Values) (left right : VectorView) (operation : Evaluation) :
    Decidable (operation.Accepts values left right) := by
  cases operation with
  | dual => unfold Evaluation.Accepts; infer_instance
  | hermitian selected =>
    simp only [Evaluation.Accepts]
    cases value? values selected with
    | none => infer_instance
    | some value => cases value <;> infer_instance

def evaluationRequest (left right : VectorView) (leftChild rightChild output : Symbol)
    (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient) : Gemm :=
  ⟨leftChild, rightChild, output, left.conjugate, right.conjugate, mode, policy, alpha, beta⟩

def evaluationCode (left right : VectorView) (leftChild rightChild output : Symbol)
    (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient) : List Storage.Statement := [
  .action (.borrow leftChild (.loan left.loan.name) left.loan.layout.transpose .read),
  .action (.borrow rightChild (.loan right.loan.name) right.loan.layout .read),
  .action (.gemm (evaluationRequest left right leftChild rightChild output mode policy alpha beta)),
  .action (.release rightChild), .action (.release leftChild)]

def scalarOutputReady (resources : State) (output : Symbol) (scalar : Scalar) : Bool :=
  match resources.loan? output with
  | none => false
  | some loan => match resources.allocation? loan.allocation with
    | none => false
    | some allocation => loan.layout.logicalRows == 1 && loan.layout.logicalColumns == 1 &&
        allocation.scalar == scalar && allocation.initialization.covers scalar loan.layout

structure CheckedEvaluation (env : Environment) (resources : State) (values : Values)
    (leftName rightName output leftChild rightChild : Symbol) (operation : Evaluation)
    (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient) where
  valuesValid : Valid env values
  left : VectorView
  right : VectorView
  leftFrom : value? values leftName = some (.vector left)
  rightFrom : value? values rightName = some (.vector right)
  leftLive : left.Live resources
  rightLive : right.Live resources
  accepts : operation.Accepts values left right
  leftState : State
  rightState : State
  leftBorrow : checkAction resources (.borrow leftChild (.loan left.loan.name) left.loan.layout.transpose .read) = .ok leftState
  rightBorrow : checkAction leftState (.borrow rightChild (.loan right.loan.name) right.loan.layout .read) = .ok rightState
  storage : CheckedGemm rightState (evaluationRequest left right leftChild rightChild output mode policy alpha beta)
  storageAccepted : checkGemm rightState (evaluationRequest left right leftChild rightChild output mode policy alpha beta) = .ok storage
  after : State
  replayed : run 4096 resources (evaluationCode left right leftChild rightChild output mode policy alpha beta) = .ok after
  leftRestored : left.Live after
  rightRestored : right.Live after
  outputInitialized : scalarOutputReady after output right.basis.space.scalar = true

def checkEvaluation (env : Environment) (resources : State) (values : Values)
    (leftName rightName output leftChild rightChild : Symbol) (operation : Evaluation)
    (mode : GemmMode) (policy : NumericalPolicy) (alpha beta : Option Coefficient := none) :
    Except Error (CheckedEvaluation env resources values leftName rightName output leftChild rightChild operation mode policy alpha beta) := do
  if valuesValid : Valid env values then
    match leftFrom : value? values leftName, rightFrom : value? values rightName with
    | some (.vector left), some (.vector right) =>
      if leftLive : left.Live resources then
        if rightLive : right.Live resources then
          if accepts : operation.Accepts values left right then
            match leftBorrow : checkAction resources (.borrow leftChild (.loan left.loan.name) left.loan.layout.transpose .read) with
            | .error diagnostic => .error diagnostic
            | .ok leftState =>
              match rightBorrow : checkAction leftState (.borrow rightChild (.loan right.loan.name) right.loan.layout .read) with
              | .error diagnostic => .error diagnostic
              | .ok rightState =>
                match storageAccepted : checkGemm rightState (evaluationRequest left right leftChild rightChild output mode policy alpha beta) with
                | .error diagnostic => .error diagnostic
                | .ok storage =>
                  match replayed : run 4096 resources (evaluationCode left right leftChild rightChild output mode policy alpha beta) with
                  | .error diagnostic => .error diagnostic
                  | .ok after =>
                    if leftRestored : left.Live after then
                      if rightRestored : right.Live after then
                        if outputInitialized : scalarOutputReady after output right.basis.space.scalar = true then
                          return ⟨valuesValid, left, right, leftFrom, rightFrom, leftLive, rightLive, accepts,
                            leftState, rightState, leftBorrow, rightBorrow, storage, storageAccepted, after,
                            replayed, leftRestored, rightRestored, outputInitialized⟩
                        else reject "evaluation output is not an initialized scalar of the selected profile"
                      else reject "evaluation did not restore its right input loan"
                    else reject "evaluation did not restore its left input loan"
          else reject "evaluation requires the corresponding dual basis, or an explicit conjugate basis and matching orthonormal metric"
        else reject "right vector no longer matches its resource loan"
      else reject "left vector no longer matches its resource loan"
    | _, _ => reject "evaluation requires typed vectors and an explicit scalar output loan"
  else reject "invalid evaluation value provenance"

end VastitasKernel.Storage.Numerical
