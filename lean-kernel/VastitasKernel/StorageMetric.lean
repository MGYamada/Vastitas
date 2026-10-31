import VastitasKernel.StorageEvaluation

/-! Explicit realizations of the existing declared diagonal Hermitian forms.
No coordinate buffer is accepted as Gram evidence. Native arithmetic remains a
separate realization of the ideal operations named by these certificates. -/
namespace VastitasKernel.Storage.Numerical
open Indexed

private def reject (message : String) : Except Error α :=
  .error ⟨"E_NUMERICAL_METRIC", message⟩

def Gram.realizes (gram : Gram) (dimension : Nat) (diagonal : Diagonal) : Bool :=
  diagonal.valid dimension && (dimension == 0 || match gram with
    | .identity => diagonal.uniform && diagonal.entries.map diagonalInteger == [some 1]
    | .scaledIdentity entry => diagonal.uniform && diagonal.entries.map diagonalInteger == [some entry]
    | .diagonal entries => !diagonal.uniform && diagonal.entries.map diagonalInteger == entries.map some)

structure RealizedMetric (metric : Metric) where
  diagonal : Diagonal
  exact : metric.gram.realizes metric.basis.space.dimension diagonal = true

def realizeMetric (metric : Metric) : Except Error (RealizedMetric metric) := do
  let encode (entry : Int) : Except Error UInt64 := match diagonalBits entry with
    | some bits => pure bits
    | none => reject "native diagonal realization requires nonzero exact integer entries with magnitude at most 2^53"
  let diagonal : Diagonal ← if metric.basis.space.dimension == 0 then pure Diagonal.one else
    match metric.gram with
    | .identity => pure Diagonal.one
    | .scaledIdentity entry => do pure ⟨true, [← encode entry]⟩
    | .diagonal entries => do pure ⟨false, ← entries.mapM encode⟩
  if exact : metric.gram.realizes metric.basis.space.dimension diagonal = true then
    return ⟨diagonal, exact⟩
  else reject "diagonal realization differs from the exact declared Gram data"

def adjointIntoRequest (input output : MapView) (source target : Diagonal)
    (policy : NumericalPolicy) : DiagonalAdjoint :=
  ⟨input.loan.name, output.loan.name, source, target, !input.conjugate, policy⟩

structure CheckedAdjointInto (env : Environment) (resources : State) (values : Values)
    (inputName outputName sourceName targetName : Symbol) (policy : NumericalPolicy) where
  valuesValid : Valid env values
  input : MapView
  output : MapView
  inputFrom : value? values inputName = some (.map input)
  outputFrom : value? values outputName = some (.map output)
  inputLive : input.Live resources
  outputLive : output.Live resources
  source : Metric
  target : Metric
  sourceFrom : value? values sourceName = some (.metric source)
  targetFrom : value? values targetName = some (.metric target)
  forms : source.basis = input.source ∧ target.basis = input.target ∧
    source.involution = target.involution
  endpoints : output.source = input.target ∧ output.target = input.source ∧ output.conjugate = false
  sourceRealization : RealizedMetric source
  targetRealization : RealizedMetric target
  sourceAccepted : realizeMetric source = .ok sourceRealization
  targetAccepted : realizeMetric target = .ok targetRealization
  after : State
  accepted : checkAction resources (.diagonalAdjoint
    (adjointIntoRequest input output sourceRealization.diagonal targetRealization.diagonal policy)) = .ok after
  inputRestored : input.Live after
  outputRestored : output.Live after
  initialized : (after.allocation? output.loan.allocation).any
    (fun allocation => allocation.initialization.covers allocation.scalar output.loan.layout) = true

def checkAdjointInto (env : Environment) (resources : State) (values : Values)
    (inputName outputName sourceName targetName : Symbol) (policy : NumericalPolicy) :
    Except Error (CheckedAdjointInto env resources values inputName outputName sourceName targetName policy) := do
  if valuesValid : Valid env values then
    match inputFrom : value? values inputName, outputFrom : value? values outputName,
        sourceFrom : value? values sourceName, targetFrom : value? values targetName with
    | some (.map input), some (.map output), some (.metric source), some (.metric target) =>
      if inputLive : input.Live resources then
        if outputLive : output.Live resources then
          if forms : source.basis = input.source ∧ target.basis = input.target ∧ source.involution = target.involution then
            if endpoints : output.source = input.target ∧ output.target = input.source ∧ output.conjugate = false then
              match sourceAccepted : realizeMetric source, targetAccepted : realizeMetric target with
              | .ok sourceRealization, .ok targetRealization =>
                match accepted : checkAction resources (.diagonalAdjoint
                    (adjointIntoRequest input output sourceRealization.diagonal targetRealization.diagonal policy)) with
                | .error diagnostic => .error diagnostic
                | .ok after =>
                  if inputRestored : input.Live after then
                    if outputRestored : output.Live after then
                      if initialized : (after.allocation? output.loan.allocation).any
                          (fun allocation => allocation.initialization.covers allocation.scalar output.loan.layout) = true then
                        return ⟨valuesValid, input, output, inputFrom, outputFrom, inputLive, outputLive,
                          source, target, sourceFrom, targetFrom, forms, endpoints, sourceRealization,
                          targetRealization, sourceAccepted, targetAccepted, after, accepted,
                          inputRestored, outputRestored, initialized⟩
                      else reject "materialized adjoint output is not initialized"
                    else reject "materialized adjoint changed its output loan"
                  else reject "materialized adjoint did not preserve its input"
              | .error diagnostic, _ | _, .error diagnostic => .error diagnostic
            else reject "adjoint destination must have the exact reversed bases and no lazy conjugation"
          else reject "adjoint requires matching source and target metrics with the same involution"
        else reject "adjoint output no longer matches its live loan"
      else reject "adjoint input no longer matches its live loan"
    | _, _, _, _ => reject "adjoint_into requires typed maps and actual declared metrics"
  else reject "invalid numerical value provenance"

def diagonalPairRequest (left right : VectorView) (output scratch writeLoan readLoan leftChild : Symbol)
    (layout : Layout) (diagonal : Diagonal) (policy : NumericalPolicy) : DiagonalPair :=
  ⟨left.loan.name, right.loan.name, output, scratch, layout, writeLoan, readLoan, leftChild,
    diagonal, left.conjugate, right.conjugate, policy⟩

/-- Explicitly reconstruct the same temporary-loan sequence as the compound
resource action. Native preflight groups these writes into one operation. -/
def diagonalPairCode (left right : VectorView) (request : DiagonalPair) : List Storage.Statement := [
  .action (.borrow request.writeLoan (.owner request.scratch) request.layout .write),
  .action (.diagonalScale ⟨right.loan.name, request.writeLoan, request.diagonal, right.conjugate, request.policy⟩),
  .action (.release request.writeLoan),
  .action (.borrow request.readLoan (.owner request.scratch) request.layout .read),
  .action (.borrow request.leftChild (.loan left.loan.name) left.loan.layout.transpose .read),
  .action (.gemm ⟨request.leftChild, request.readLoan, request.output, left.conjugate, false,
    .overwrite, request.policy, none, none⟩),
  .action (.release request.leftChild), .action (.release request.readLoan)]

structure CheckedDiagonalPairing (env : Environment) (resources : State) (values : Values)
    (leftName rightName output metricName scratch writeLoan readLoan leftChild : Symbol)
    (layout : Layout) (policy : NumericalPolicy) where
  valuesValid : Valid env values
  left : VectorView
  right : VectorView
  leftFrom : value? values leftName = some (.vector left)
  rightFrom : value? values rightName = some (.vector right)
  leftLive : left.Live resources
  rightLive : right.Live resources
  metric : Metric
  metricFrom : value? values metricName = some (.metric metric)
  form : metric.basis = right.basis ∧ left.basis.parent = some right.basis.brand ∧
    left.basis.space.origin = .conjugate right.basis.space.brand metric.selected
  realization : RealizedMetric metric
  realizationAccepted : realizeMetric metric = .ok realization
  after : State
  accepted : checkAction resources (.diagonalPair
    (diagonalPairRequest left right output scratch writeLoan readLoan leftChild layout realization.diagonal policy)) = .ok after
  replayed : run 4096 resources (diagonalPairCode left right
    (diagonalPairRequest left right output scratch writeLoan readLoan leftChild layout realization.diagonal policy)) = .ok after
  leftRestored : left.Live after
  rightRestored : right.Live after
  ownersRestored : (after.allocations.map fun allocation => (allocation.owner, allocation.identity)) =
    (resources.allocations.map fun allocation => (allocation.owner, allocation.identity))
  loansRestored : after.loans = resources.loans
  initialized : scalarOutputReady after output right.basis.space.scalar = true

def checkDiagonalPairing (env : Environment) (resources : State) (values : Values)
    (leftName rightName output metricName scratch writeLoan readLoan leftChild : Symbol)
    (layout : Layout) (policy : NumericalPolicy) :
    Except Error (CheckedDiagonalPairing env resources values leftName rightName output metricName
      scratch writeLoan readLoan leftChild layout policy) := do
  if valuesValid : Valid env values then
    match leftFrom : value? values leftName, rightFrom : value? values rightName, metricFrom : value? values metricName with
    | some (.vector left), some (.vector right), some (.metric metric) =>
      if leftLive : left.Live resources then
        if rightLive : right.Live resources then
          if form : metric.basis = right.basis ∧ left.basis.parent = some right.basis.brand ∧
              left.basis.space.origin = .conjugate right.basis.space.brand metric.selected then
            match realizationAccepted : realizeMetric metric with
            | .error diagnostic => .error diagnostic
            | .ok realization =>
              let request := diagonalPairRequest left right output scratch writeLoan readLoan leftChild layout realization.diagonal policy
              match accepted : checkAction resources (.diagonalPair request) with
              | .error diagnostic => .error diagnostic
              | .ok after =>
                match replayed : run 4096 resources (diagonalPairCode left right request) with
                | .error diagnostic => .error diagnostic
                | .ok replayedState =>
                  if same : replayedState = after then
                      if leftRestored : left.Live after then
                        if rightRestored : right.Live after then
                          if ownersRestored : (after.allocations.map fun allocation => (allocation.owner, allocation.identity)) =
                              (resources.allocations.map fun allocation => (allocation.owner, allocation.identity)) then
                            if loansRestored : after.loans = resources.loans then
                              if initialized : scalarOutputReady after output right.basis.space.scalar = true then
                                return ⟨valuesValid, left, right, leftFrom, rightFrom, leftLive, rightLive, metric,
                                  metricFrom, form, realization, realizationAccepted, after, accepted, same ▸ replayed,
                                  leftRestored, rightRestored, ownersRestored, loansRestored, initialized⟩
                              else reject "diagonal pairing output is not an initialized scalar"
                            else reject "diagonal pairing did not restore temporary loans"
                          else reject "diagonal pairing changed caller ownership"
                        else reject "diagonal pairing did not restore its right input"
                      else reject "diagonal pairing did not restore its left input"
                    else reject "diagonal pairing differs from its explicit scratch transitions"
          else reject "diagonal pairing requires an explicit corresponding conjugate basis and the exact declared form"
        else reject "diagonal pairing right vector is not live"
      else reject "diagonal pairing left vector is not live"
    | _, _, _ => reject "diagonal pairing requires typed vectors and a declared metric"
  else reject "invalid numerical value provenance"

end VastitasKernel.Storage.Numerical
