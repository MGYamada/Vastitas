import VastitasKernel.StorageFunctionOperations

/-! Numerical, tensor, tree and network operations of a function body. Each
operation records a typed receipt of its accepted check and emitted code. -/
namespace VastitasKernel.Storage.Functions

open Internal

private structure ProductEmission (resources : State) (request : Gemm) (priorCode : List Storage.Statement) where
  after : State
  transitioned : checkAction resources (.gemm request) = .ok after
  code : List Storage.Statement
  emitted : priorCode ++ [.action (.gemm request)] = code

private def emitProduct (context : Context) (site : NumericalSourceSite) (networkProduct : Bool)
    {left right output mode policy alpha beta}
    (checked : Numerical.CheckedProduct context.environment context.resources context.numerical
      left right output mode policy alpha beta)
    (accepted : Numerical.checkProduct context.environment context.resources context.numerical
      left right output mode policy alpha beta = .ok checked) :
    M (ProductEmission context.resources (checked.product.request mode policy) context.code.toList) := do
  step (.gemm (checked.product.request mode policy))
  match transitioned : checkAction context.resources (.gemm (checked.product.request mode policy)) with
  | .error diagnostic => throw diagnostic
  | .ok resources =>
    let ⟨after, same, emitted⟩ ← checkEmitted context.code.toList
      [.action (.gemm (checked.product.request mode policy))] resources
      {code := "E_NUMERICAL_TYPE", message := "typed GEMM differs from its resource transition"}
      {code := "E_NUMERICAL_TYPE", message := "typed GEMM differs from its emitted schedule"}
    let receipt : NumericalReceipt :=
      ⟨context.environment, context.resources, context.numerical, left, right, output, mode, policy, alpha, beta,
        checked, accepted, after.resources, same.symm ▸ transitioned, context.code.toList, after.code.toList, emitted, context.location site, networkProduct⟩
    set {after with products := after.products.push receipt}
    return ⟨after.resources, same.symm ▸ transitioned, after.code.toList, emitted⟩

/-- Values share the activation's fresh-name supply, but never enter the native
heap. Only the checked product's exact physical request enters the schedule. -/
def numericalOperation (site : NumericalSourceSite) (frame : Frame) (operation : Numerical.Operation) : M Frame := do
  let context ← get
  match operation with
  | .adjointInto input output source target policy =>
    let input ← resolve frame input
    let output ← resolve frame output
    let source ← resolve frame source
    let target ← resolve frame target
    match accepted : Numerical.checkAdjointInto context.environment context.resources context.numerical input output source target policy with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let action := Action.diagonalAdjoint (Numerical.adjointIntoRequest checked.input checked.output
        checked.sourceRealization.diagonal checked.targetRealization.diagonal policy)
      let ⟨after, transitioned, emitted⟩ ← emitChecked context.code.toList [action] checked.after
        {code := "E_NUMERICAL_METRIC", message := "materialized adjoint differs from its resource transition"}
        {code := "E_NUMERICAL_METRIC", message := "materialized adjoint differs from its emitted operation"}
      let receipt : AdjointIntoReceipt := ⟨context.environment, context.resources, context.numerical,
        input, output, source, target, policy, checked, accepted, after.resources, transitioned,
        context.code.toList, after.code.toList, emitted, context.location site⟩
      set {after with adjoints := after.adjoints.push receipt}
      return frame
  | .hermitianDiagonal left right output metric scratch layout policy =>
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let metric ← resolve frame metric
    let scratch ← resolve frame scratch
    rejectOpaque scratch
    let writeLoan ← fresh
    let readLoan ← fresh
    let leftChild ← fresh
    match accepted : Numerical.checkDiagonalPairing context.environment context.resources context.numerical
        left right output metric scratch writeLoan readLoan leftChild layout policy with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let action := Action.diagonalPair (Numerical.diagonalPairRequest checked.left checked.right
        output scratch writeLoan readLoan leftChild layout checked.realization.diagonal policy)
      let ⟨after, transitioned, emitted⟩ ← emitChecked context.code.toList [action] checked.after
        {code := "E_NUMERICAL_METRIC", message := "diagonal pairing differs from its resource transition"}
        {code := "E_NUMERICAL_METRIC", message := "diagonal pairing differs from its emitted operation"}
      let receipt : DiagonalPairingReceipt := ⟨context.environment, context.resources, context.numerical,
        left, right, output, metric, scratch, writeLoan, readLoan, leftChild, layout, policy,
        checked, accepted, after.resources, transitioned, context.code.toList, after.code.toList, emitted, context.location site⟩
      set {after with diagonalPairings := after.diagonalPairings.push receipt}
      return frame
  | .conjugateVector name parent basis selected =>
    let parent ← resolve frame parent
    let basis ← resolve frame basis
    let selected ← resolve frame selected
    let (frame, name) ← bindName frame name
    let child ← fresh
    match accepted : Numerical.checkVectorConjugate context.environment context.resources context.numerical name parent child basis selected with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let action := Action.borrow child (.loan checked.original.loan.name) checked.original.loan.layout .read
      let ⟨after, transitioned, emitted⟩ ← emitChecked context.code.toList [action] checked.after
        {code := "E_NUMERICAL_TYPE", message := "vector conjugation differs from its actual resource transition"}
        {code := "E_NUMERICAL_TYPE", message := "vector conjugation differs from its emitted borrow"}
      let receipt : VectorConjugateReceipt := ⟨context.environment, context.resources, context.numerical,
        name, parent, child, basis, selected, checked, accepted, after.resources, transitioned.symm,
        context.code.toList, after.code.toList, emitted⟩
      set {after with numerical := checked.output, vectorConjugates := after.vectorConjugates.push receipt}
      return frame
  | .evaluate left right output operation mode policy alpha beta =>
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let operation ← match operation with
      | .dual => pure Numerical.Evaluation.dual
      | .hermitian selected => pure (.hermitian (← resolve frame selected))
    let alpha ← lowerCoefficient frame alpha
    let beta ← lowerCoefficient frame beta
    let leftChild ← fresh
    let rightChild ← fresh
    match accepted : Numerical.checkEvaluation context.environment context.resources context.numerical
        left right output leftChild rightChild operation mode policy alpha beta with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let code := Numerical.evaluationCode checked.left checked.right leftChild rightChild output mode policy alpha beta
      for statement in code do
        match statement with
        | .action action => step action
        | _ => throw {code := "E_NUMERICAL_TYPE", message := "evaluation contains an unexpected branch"}
      let ⟨after, transitioned, emitted⟩ ← checkEmitted context.code.toList code checked.after
        {code := "E_NUMERICAL_TYPE", message := "evaluation differs from its actual resource transition"}
        {code := "E_NUMERICAL_TYPE", message := "evaluation differs from its emitted resource schedule"}
      let receipt : EvaluationReceipt := ⟨context.environment, context.resources, context.numerical,
        left, right, output, leftChild, rightChild, operation, mode, policy, alpha, beta,
        checked, accepted, after.resources, transitioned.symm, context.code.toList, after.code.toList, emitted, context.location site⟩
      set {after with evaluations := after.evaluations.push receipt}
      return frame
  | .transform name parent operation =>
    let parent ← resolve frame parent
    let operation ← match operation with
      | .dual source target => pure (Numerical.Transform.dual (← resolve frame source) (← resolve frame target))
      | .conjugate source target selected => pure (.conjugate (← resolve frame source) (← resolve frame target) (← resolve frame selected))
      | .adjoint source target => pure (.adjoint (← resolve frame source) (← resolve frame target))
    let (frame, name) ← bindName frame name
    let child ← fresh
    match accepted : Numerical.checkTransform context.environment context.resources context.numerical name parent child operation with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let action := Action.borrow child (.loan checked.original.loan.name)
        (if operation.transpose then checked.original.loan.layout.transpose else checked.original.loan.layout) .read
      let ⟨after, transitioned, emitted⟩ ← emitChecked context.code.toList [action] checked.after
        {code := "E_NUMERICAL_TYPE", message := "transformed map differs from its actual resource transition"}
        {code := "E_NUMERICAL_TYPE", message := "transformed map differs from its emitted borrow"}
      let receipt : TransformReceipt := ⟨context.environment, context.resources, context.numerical,
        name, parent, child, operation, checked, accepted, after.resources, transitioned.symm,
        context.code.toList, after.code.toList, emitted⟩
      set {after with numerical := checked.output, transforms := after.transforms.push receipt}
      return frame
  | .packMap name owner =>
    let owner ← resolve frame owner
    let (frame, name) ← bindName frame name
    packageStep .pack owner name
    return frame
  | .unpackMap package space basis owner =>
    let package ← resolve frame package
    let (frame, space) ← bindName frame space
    let (frame, basis) ← bindName frame basis
    let (frame, owner) ← bindName frame owner
    packageStep (.open space basis) package owner
    return frame
  | .borrowOwned name owner access =>
    let owner ← resolve frame owner
    let some (.ownedMap view) := Numerical.value? context.numerical owner
      | throw {code := "E_NUMERICAL_TYPE", message := "implicit coordinate layout requires an owned map"}
    unless view.Live context.resources do
      throw {code := "E_RESOURCE_MOVE", message := "owned map is no longer live"}
    let (frame, name) ← bindName frame name
    step (.borrow name (.owner view.owner) view.layout access)
    return frame
  | .ownedMap name owner layout source target =>
    let owner ← resolve frame owner
    rejectOpaque owner
    let source ← resolve frame source
    let target ← resolve frame target
    let (frame, name) ← bindName frame name
    let values ← Numerical.construct context.environment context.resources context.numerical
      (.ownedMap name owner layout source target)
    let some (.ownedMap view) := Numerical.value? values name
      | throw {code := "E_NUMERICAL_TYPE", message := "owned map constructor lost its interpretation"}
    transferMap view name
    return frame
  | .gemm left right output mode policy alpha beta =>
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let alpha ← lowerCoefficient frame alpha
    let beta ← lowerCoefficient frame beta
    match accepted : Numerical.checkProduct context.environment context.resources context.numerical
        left right output mode policy alpha beta with
    | .error diagnostic => throw diagnostic
    | .ok checked =>
      let _ ← emitProduct context site false checked accepted
      return frame
  | other =>
    let (frame, operation) ← match other with
      | .space name implementation dimension => do
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.space name implementation dimension)
      | .basis name space => do
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.basis name space)
      | .involution name space => do
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.involution name space)
      | .dualSpace name parent => do
        let parent ← resolve frame parent
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.dualSpace name parent)
      | .conjugateSpace name parent selected => do
        let parent ← resolve frame parent
        let selected ← resolve frame selected
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.conjugateSpace name parent selected)
      | .derivedBasis name parent space => do
        let parent ← resolve frame parent
        let space ← resolve frame space
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.derivedBasis name parent space)
      | .metric name basis selected gram => do
        let basis ← resolve frame basis
        let selected ← resolve frame selected
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.metric name basis selected gram)
      | .map name loan source target => do
        let loan ← resolve frame loan
        let source ← resolve frame source
        let target ← resolve frame target
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.map name loan source target)
      | .vector name loan basis => do
        let loan ← resolve frame loan
        let basis ← resolve frame basis
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.vector name loan basis)
      | .ownedView name loan owner => do
        let loan ← resolve frame loan
        let owner ← resolve frame owner
        let (frame, name) ← bindName frame name
        pure (frame, Numerical.Operation.ownedView name loan owner)
      | .gemm .. | .ownedMap .. | .borrowOwned .. | .transform .. | .conjugateVector .. | .evaluate .. | .packMap .. | .unpackMap .. | .adjointInto .. | .hermitianDiagonal .. =>
        throw {code := "E_NUMERICAL_TYPE", message := "invalid numerical constructor"}
    let values ← Numerical.construct context.environment context.resources context.numerical operation
    modify fun after => {after with numerical := values}
    return frame

def tensorOperation (site : NumericalSourceSite) (frame : Frame) (operation : Tensor.Operation) : M Frame := do
  match operation with
  | .view name loan axes grouping =>
    let loan ← resolve frame loan
    let axes ← (axes.mapM (resolve frame) : Except Error (List Symbol))
    let (frame, name) ← bindName frame name
    let before ← get
    match accepted : Tensor.checkView before.environment before.numerical before.resources axes grouping loan with
    | .error error => throw error
    | .ok checked =>
      let values := (name, checked.view) :: before.tensors
      if valid : Tensor.Valid before.environment before.numerical values then
        if bound : Tensor.lookup values name = some checked.view then
          let receipt : TensorViewReceipt := ⟨before.environment, before.numerical, before.resources,
            axes, grouping, loan, checked, accepted, name, values, bound, valid⟩
          set {before with tensors := values, tensorViews := before.tensorViews.push receipt}
          return frame
        else throw {code := "E_TENSOR", message := "tensor constructor lost its actual value"}
      else throw {code := "E_TENSOR", message := "invalid tensor constructor identity"}
  | .pack source target =>
    let source ← resolve frame source
    let target ← resolve frame target
    let before ← get
    match accepted : Tensor.checkPack before.environment before.numerical before.resources before.tensors source target with
    | .error error => throw error
    | .ok checked =>
      let ⟨after, transitioned, emitted⟩ ← emitChecked before.code.toList
        [Tensor.packAction checked.input checked.output] checked.after
        {code := "E_TENSOR", message := "packing differs from its actual resource transition"}
        {code := "E_TENSOR", message := "packing differs from its emitted schedule"}
      let receipt : TensorPackReceipt := ⟨before.environment, before.numerical, before.resources,
        before.tensors, source, target, checked, accepted, after.resources, transitioned,
        before.code.toList, after.code.toList, emitted⟩
      set {after with tensorPacks := after.tensorPacks.push receipt}
      return frame
  | .cachedPack name source target =>
    let source ← resolve frame source
    let target ← resolve frame target
    let (frame, name) ← bindName frame name
    let before ← get
    match accepted : Tensor.checkPack before.environment before.numerical before.resources before.tensors source target with
    | .error error => throw error
    | .ok checked =>
      let cache ← Tensor.captureCache checked accepted name
      step (Tensor.packAction checked.input checked.output)
      step (.captureDependency name checked.input.loan.name checked.output.loan.name)
      -- The schedule is compared with the cache's own actions, not with the
      -- ones just stepped.
      let ⟨after, transitioned, emitted⟩ ← checkEmitted before.code.toList
        [.action (Tensor.packAction cache.checked.input cache.checked.output),
          .action (.captureDependency cache.name cache.checked.input.loan.name cache.checked.output.loan.name)]
        cache.after
        {code := "E_TENSOR_CACHE", message := "cached packing differs from its actual post-pack capture"}
        {code := "E_TENSOR_CACHE", message := "cached packing differs from its emitted schedule"}
      let receipt : CacheCaptureReceipt := ⟨cache, after.resources, transitioned, before.code.toList, after.code.toList, emitted⟩
      set {after with packCaches := cache :: after.packCaches, cacheCaptures := after.cacheCaptures.push receipt}
      return frame
  | .cachedContract3 cache left right output policy =>
    let cacheName ← resolve frame cache
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let before ← get
    let some cache := before.packCaches.find? (·.name == cacheName)
      | throw {code := "E_TENSOR_CACHE", message := "cached contraction requires a local actual packing certificate"}
    match accepted : Tensor.checkCachedContraction before.environment before.numerical before.resources before.tensors cache left right output policy with
    | .error error => throw error
    | .ok checked =>
      let request := Tensor.contractionRequest checked.contraction.left checked.contraction.right checked.contraction.output policy
      let ⟨after, transitioned, emitted⟩ ← emitChecked before.code.toList
        [.requireDependency cache.name, .gemm request] checked.contraction.after
        {code := "E_TENSOR_CACHE", message := "cached contraction differs from its actual resource transition"}
        {code := "E_TENSOR_CACHE", message := "cached contraction differs from emitted dependency/GEMM schedule"}
      let receipt : CachedContractionReceipt := ⟨before.environment, before.numerical, before.resources,
        before.tensors, cache, left, right, output, policy, checked, accepted, after.resources,
        transitioned, before.code.toList, after.code.toList, emitted, before.location site⟩
      set {after with cachedContractions := after.cachedContractions.push receipt}
      return frame
  | .contract3 left right output policy =>
    let left ← resolve frame left
    let right ← resolve frame right
    let output ← resolve frame output
    let before ← get
    match accepted : Tensor.checkContraction before.environment before.numerical before.resources before.tensors left right output policy with
    | .error error => throw error
    | .ok checked =>
      let request := Tensor.contractionRequest checked.left checked.right checked.output policy
      let ⟨after, transitioned, emitted⟩ ← emitChecked before.code.toList [.gemm request] checked.after
        {code := "E_TENSOR", message := "contraction differs from its actual resource transition"}
        {code := "E_TENSOR", message := "contraction differs from its emitted schedule"}
      let receipt : TensorContractionReceipt := ⟨before.environment, before.numerical, before.resources,
        before.tensors, left, right, output, policy, checked, accepted, after.resources, transitioned,
        before.code.toList, after.code.toList, emitted, before.location site⟩
      set {after with tensorContractions := after.tensorContractions.push receipt}
      return frame

private def resolveTreePlan (frame : Frame) (plan : List TensorTree.Event) : M (List TensorTree.Event) := do
  unless plan.length ≤ 1024 do throw {code := "E_TENSOR_TREE", message := "tree plan exceeds 1024 explicit steps"}
  let mut localFrame := frame
  let mut resolved := []
  for event in plan do
    spend
    let (next, event) ← match event with
      | .action (.borrow name source layout access) => do
        let source ← lowerSource localFrame source
        let (next, name) ← bindName localFrame name
        pure (next, TensorTree.PlanStep.action (.borrow name source layout access))
      | .action (.release name) => do
        let name ← resolve localFrame name
        let loan := match Numerical.value? (← get).numerical name with
          | some (.map view) => view.loan.name
          | some (.vector view) => view.loan.name
          | _ => name
        pure (localFrame, .action (.release loan))
      | .action _ => throw {code := "E_TENSOR_TREE", message := "tree preparation permits only explicit borrow/release"}
      | .view name loan axes grouping => do
        let loan ← resolve localFrame loan
        let axes ← (axes.mapM (resolve localFrame) : Except Error (List Symbol))
        let (next, name) ← bindName localFrame name
        pure (next, .view name loan axes grouping)
      | .regroup component target => pure (localFrame, .regroup component (← resolve localFrame target))
      | .rebind component view => pure (localFrame, .rebind component (← resolve localFrame view))
      | .join name edge left right output => pure (localFrame, .join name edge left right (← resolve localFrame output))
    localFrame := next
    resolved := resolved ++ [event]
  return resolved

def treeOperation (site : NumericalSourceSite) (frame : Frame) (graph : TensorTree.Graph) (output : Symbol)
    (policy : NumericalPolicy) (plan : List TensorTree.Event) : M Frame := do
  unless graph.Bounded do throw {code := "E_TENSOR_TREE", message := "tree exceeds bounded occurrence/edge/boundary profile"}
  let graph ← (graph.mapM (resolve frame) : Except Error TensorTree.Graph)
  let output ← resolve frame output
  let before ← get
  let plan ← resolveTreePlan frame plan
  match policy with
  | .nativeFast =>
    match accepted : TensorTree.check before.environment before.numerical before.resources before.tensors graph output plan with
    | .error error => throw error
    | .ok checked =>
      let ⟨after, transitioned, emitted⟩ ← emitChecked before.code.toList checked.finalState.code
        checked.finalState.resources
        {code := "E_TENSOR_TREE", message := "tree differs from its actual resource expansion"}
        {code := "E_TENSOR_TREE", message := "tree emission changed an earlier resource operation"}
      let receipt : TreeReceipt := ⟨before.environment, before.numerical, before.resources, before.tensors,
        graph, output, plan, checked, accepted, after.resources, transitioned, before.code.toList, after.code.toList, emitted, before.location site⟩
      set {after with trees := after.trees.push receipt}
      return frame

def networkOperation (site : NumericalSourceSite) (frame : Frame) (graph : TensorNetwork.Graph) (output : Symbol)
    (policy : NumericalPolicy) : M Frame := do
  unless graph.Bounded do throw {code := "E_NETWORK", message := "unsupported network profile"}
  let graph ← (graph.mapM (resolve frame) : Except Error TensorNetwork.Graph)
  let output ← resolve frame output
  let context ← get
  match accepted : TensorNetwork.check context.environment context.resources context.numerical graph output policy with
  | .error diagnostic => throw diagnostic
  | .ok checked =>
    let receipt ← emitProduct context site true checked.product checked.acceptedProduct
    let network : NetworkReceipt := ⟨context.environment, context.resources, context.numerical,
      graph, output, policy, checked, accepted, receipt.after, receipt.transitioned,
      context.code.toList, receipt.code, receipt.emitted, context.location site⟩
    modify fun after => {after with networks := after.networks.push network}
    return frame

end VastitasKernel.Storage.Functions
