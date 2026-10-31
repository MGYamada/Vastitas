import VastitasKernel.IndexedAudit
import VastitasKernel.Storage

/-! Nominal numerical values for the resource function compiler. Constructors
reconstruct profiles from the common indexed environment; dimensions are not
object identities. A map is an explicit interpretation of a live buffer in two
bases, not evidence of field laws or a theorem about its floating-point payload.
This internal component does not introduce a public wire format. -/
namespace VastitasKernel.Storage.Numerical
open Indexed

inductive SpaceOrigin where
  | primal
  | dual (parent : Symbol)
  | conjugate (parent involution : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Space where
  type : ObjectType
  brand : Symbol
  base : DeclId
  coefficient : CoefficientKind
  setting : GeometricSetting
  dimension : Nat
  origin : SpaceOrigin := .primal
  deriving Repr, BEq, DecidableEq, Inhabited

def Space.object (space : Space) : ObjectRef := .local space.type space.brand

def Space.scalar (space : Space) : Scalar :=
  match space.coefficient with | .real => .f64 | .complex => .complexF64

/-- Complex smooth dimension is over C; the underlying real dimension is 2n. -/
def Space.realDimension (space : Space) : Nat :=
  if space.coefficient == .complex then 2 * space.dimension else space.dimension

def Space.Valid (env : Environment) (space : Space) : Prop :=
  lookup env space.type.domain = some (.implementation space.type.marker
    (.linearDescriptor space.base space.coefficient) []) ∧
  space.type.Valid env ∧
  (scalarBaseProfile env space.base).map (fun profile => profile.2.1) = some space.setting ∧
  space.dimension * space.scalar.width ≤ byteLimit

instance (env : Environment) (space : Space) : Decidable (space.Valid env) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Basis where
  space : Space
  brand : Symbol
  parent : Option Symbol := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The admitted involution is identity over R and conjugation over C. The
descriptor is reconstructed from an actual profile, never from a dimension. -/
structure Involution where
  type : ObjectType
  base : DeclId
  coefficient : CoefficientKind
  setting : GeometricSetting
  deriving Repr, BEq, DecidableEq, Inhabited

def Involution.ofSpace (space : Space) : Involution :=
  ⟨space.type, space.base, space.coefficient, space.setting⟩

inductive Gram where
  | identity
  | scaledIdentity (entry : Int)
  | diagonal (entries : List Int)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Declared coordinate Hermitian data, not measured orthogonality. A diagonal
form is nondegenerate exactly when every exact integer entry is nonzero. -/
structure Metric where
  basis : Basis
  involution : Involution
  selected : Symbol
  gram : Gram
  deriving Repr, BEq, DecidableEq, Inhabited

def Metric.nondegenerate (metric : Metric) : Bool := match metric.gram with
  | .identity => true
  | .scaledIdentity entry => metric.basis.space.dimension == 0 || entry != 0
  | .diagonal entries => entries.length ≤ 4096 && entries.length == metric.basis.space.dimension &&
      entries.all (· != 0)

def Metric.orthonormal (metric : Metric) : Bool := match metric.gram with
  | .identity => true
  | .scaledIdentity entry => metric.basis.space.dimension == 0 || entry == 1
  | .diagonal entries => entries.all (· == 1)

inductive MapOrigin where
  | direct
  | reborrow (parent : Symbol)
  | dual (parent : Symbol)
  | conjugate (parent involution : Symbol)
  | adjoint (parent sourceMetric targetMetric : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

structure MapView where
  source : Basis
  target : Basis
  loan : Loan
  conjugate : Bool := false
  origin : MapOrigin := .direct
  deriving Repr, BEq, DecidableEq, Inhabited

inductive VectorOrigin where
  | direct
  | reborrow (parent : Symbol)
  | conjugate (parent involution : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A vector is a column of coordinates in one actual basis. A covector uses
an explicitly selected dual space and its corresponding basis. -/
structure VectorView where
  basis : Basis
  loan : Loan
  conjugate : Bool := false
  origin : VectorOrigin := .direct
  deriving Repr, BEq, DecidableEq, Inhabited

def VectorView.Live (resources : Storage.State) (view : VectorView) : Prop :=
  resources.loan? view.loan.name = some view.loan ∧
  resources.suspended view.loan.name = false ∧
  (resources.allocation? view.loan.allocation).map Allocation.scalar = some view.basis.space.scalar ∧
  view.loan.layout.logicalRows = view.basis.space.dimension ∧ view.loan.layout.logicalColumns = 1

instance (resources : Storage.State) (view : VectorView) : Decidable (view.Live resources) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def MapView.Compatible (view : MapView) : Prop :=
  view.source.space.type = view.target.space.type ∧
  view.source.space.base = view.target.space.base ∧
  view.source.space.coefficient = view.target.space.coefficient ∧
  view.source.space.setting = view.target.space.setting

instance (view : MapView) : Decidable view.Compatible :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Retain the complete loan snapshot, including physical layout and ancestry.
Writes change the payload/version, not its endpoint type. Releasing, reborrowing
or transposing a handle cannot silently reuse an obsolete interpretation. -/
def MapView.Live (resources : Storage.State) (view : MapView) : Prop :=
  resources.loan? view.loan.name = some view.loan ∧
  resources.suspended view.loan.name = false ∧
  (resources.allocation? view.loan.allocation).map Allocation.scalar = some view.source.space.scalar ∧
  view.loan.layout.logicalRows = view.target.space.dimension ∧
  view.loan.layout.logicalColumns = view.source.space.dimension

instance (resources : Storage.State) (view : MapView) : Decidable (view.Live resources) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- An owned coordinate interpretation retains the allocation and its exact
layout. It is metadata, not a second owner or an outstanding loan. -/
structure OwnedMap where
  source : Basis
  target : Basis
  owner : Symbol
  allocation : Nat
  layout : Layout
  deriving Repr, BEq, DecidableEq, Inhabited

def OwnedMap.Compatible (view : OwnedMap) : Prop :=
  view.source.space.type = view.target.space.type ∧
  view.source.space.base = view.target.space.base ∧
  view.source.space.coefficient = view.target.space.coefficient ∧
  view.source.space.setting = view.target.space.setting

instance (view : OwnedMap) : Decidable view.Compatible :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def OwnedMap.Live (resources : Storage.State) (view : OwnedMap) : Prop :=
  ∃ allocation ∈ resources.owner? view.owner,
    allocation.identity = view.allocation ∧ allocation.scalar = view.source.space.scalar ∧
    checkLayout allocation.scalar allocation.capacity view.layout = true ∧
    view.layout.logicalRows = view.target.space.dimension ∧
    view.layout.logicalColumns = view.source.space.dimension

instance (resources : Storage.State) (view : OwnedMap) : Decidable (view.Live resources) :=
  inferInstanceAs (Decidable (∃ allocation ∈ resources.owner? view.owner, _))

def OwnedMap.Initialized (resources : Storage.State) (view : OwnedMap) : Prop :=
  (resources.owner? view.owner).any (fun allocation =>
    allocation.initialization.covers allocation.scalar view.layout) = true

instance (resources : Storage.State) (view : OwnedMap) : Decidable (view.Initialized resources) :=
  inferInstanceAs (Decidable (_ = _))

inductive Value where
  | space (value : Space)
  | basis (value : Basis)
  | map (value : MapView)
  | ownedMap (value : OwnedMap)
  | involution (value : Involution)
  | metric (value : Metric)
  | vector (value : VectorView)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Values := List (Symbol × Value)

def value? (values : Values) (name : Symbol) : Option Value :=
  (values.find? (·.1 == name)).map Prod.snd

def spaceOriginValid (values : Values) (name : Symbol) (space : Space) : Bool :=
  match space.origin with
  | .primal => true
  | .dual parent => match value? values parent with
    | some (.space original) => parent < name && space == {original with brand := name, origin := .dual parent}
    | _ => false
  | .conjugate parent selected => match value? values parent, value? values selected with
    | some (.space original), some (.involution involution) => parent < name && selected < name &&
        involution == Involution.ofSpace original &&
        space == {original with brand := name, origin := .conjugate parent selected}
    | _, _ => false

def basisOriginValid (values : Values) (name : Symbol) (basis : Basis) : Bool :=
  match basis.parent with
  | none => true
  | some parent => match value? values parent with
    | some (.basis original) => parent < name && (match basis.space.origin with
      | .dual space | .conjugate space _ => space == original.space.brand
      | .primal => false)
    | _ => false

def MapView.childOf (view parent : MapView) (transpose : Bool) : Bool :=
  view.loan.allocation == parent.loan.allocation && view.loan.parent == some parent.loan.name &&
  view.loan.layout == (if transpose then parent.loan.layout.transpose else parent.loan.layout)

def adjointContract (values : Values) (original : MapView) (source target : Symbol) : Prop :=
  match value? values source, value? values target with
  | some (.metric source), some (.metric target) => source.basis = original.source ∧
      target.basis = original.target ∧ source.involution = target.involution ∧
      source.orthonormal = true ∧ target.orthonormal = true
  | _, _ => False

instance (values : Values) (original : MapView) (source target : Symbol) :
    Decidable (adjointContract values original source target) := by
  unfold adjointContract
  cases value? values source with
  | none => infer_instance
  | some source => cases source <;> cases value? values target with
    | none => infer_instance
    | some target => cases target <;> infer_instance

def mapOriginValid (values : Values) (name : Symbol) (view : MapView) : Bool :=
  let parent (id : Symbol) (test : MapView → Bool) :=
    id < name && match value? values id with | some (.map original) => test original | _ => false
  match view.origin with
  | .direct => !view.conjugate
  | .reborrow id => parent id fun original => view.childOf original false &&
      view.source == original.source && view.target == original.target && view.conjugate == original.conjugate
  | .dual id => parent id fun original => view.childOf original true && view.loan.access == .read &&
      view.source.parent == some original.target.brand && view.target.parent == some original.source.brand &&
      view.source.space.origin == .dual original.target.space.brand &&
      view.target.space.origin == .dual original.source.space.brand && view.conjugate == original.conjugate
  | .conjugate id selected => parent id fun original => view.childOf original false && view.loan.access == .read &&
      selected < name && (match value? values selected with
        | some (.involution involution) => involution == Involution.ofSpace original.source.space
        | _ => false) &&
      view.source.parent == some original.source.brand && view.target.parent == some original.target.brand &&
      view.source.space.origin == .conjugate original.source.space.brand selected &&
      view.target.space.origin == .conjugate original.target.space.brand selected && view.conjugate == !original.conjugate
  | .adjoint id sourceMetric targetMetric => parent id fun original =>
      view.childOf original true && view.loan.access == .read && sourceMetric < name && targetMetric < name &&
      view.source == original.target && view.target == original.source && view.conjugate == !original.conjugate &&
      decide (adjointContract values original sourceMetric targetMetric)

def vectorOriginValid (values : Values) (name : Symbol) (view : VectorView) : Bool :=
  let parent (id : Symbol) (test : VectorView → Bool) :=
    id < name && match value? values id with
      | some (.vector original) =>
        view.loan.allocation == original.loan.allocation && view.loan.parent == some original.loan.name &&
        view.loan.layout == original.loan.layout && test original
      | _ => false
  match view.origin with
  | .direct => !view.conjugate
  | .reborrow id => parent id fun original => view.basis == original.basis && view.conjugate == original.conjugate
  | .conjugate id selected => parent id fun original => selected < name && view.loan.access == .read &&
      view.basis.parent == some original.basis.brand &&
      view.basis.space.origin == .conjugate original.basis.space.brand selected &&
      view.conjugate == !original.conjugate && (match value? values selected with
        | some (.involution sigma) => sigma == Involution.ofSpace original.basis.space
        | _ => false)

/-- A forged basis cannot invent a space, and a forged map cannot invent bases.
Stored maps may outlive a loan, but every use rechecks Live against real state. -/
def Value.Valid (env : Environment) (values : Values) (name : Symbol) : Value → Prop
  | .space spc => spc.brand = name ∧ spc.Valid env ∧ spaceOriginValid values name spc = true
  | .basis bas => bas.brand = name ∧
      value? values bas.space.brand = some (.space bas.space) ∧ basisOriginValid values name bas = true
  | .map view => view.Compatible ∧
      value? values view.source.brand = some (.basis view.source) ∧
      value? values view.target.brand = some (.basis view.target) ∧ mapOriginValid values name view = true
  | .ownedMap view => view.Compatible ∧
      value? values view.source.brand = some (.basis view.source) ∧
      value? values view.target.brand = some (.basis view.target)
  | .involution sigma => values.any (fun entry => entry.1 < name && match entry.2 with
      | .space original => sigma == Involution.ofSpace original | _ => false) = true
  | .metric form => value? values form.basis.brand = some (.basis form.basis) ∧
      value? values form.selected = some (.involution form.involution) ∧
      form.involution = Involution.ofSpace form.basis.space ∧ form.nondegenerate = true
  | .vector view => value? values view.basis.brand = some (.basis view.basis) ∧
      vectorOriginValid values name view = true

instance (env : Environment) (values : Values) (name : Symbol) (value : Value) :
    Decidable (value.Valid env values name) := by
  cases value <;> unfold Value.Valid <;> infer_instance

def Valid (env : Environment) (values : Values) : Prop :=
  env.Valid ∧ values.length ≤ 4096 ∧ (values.map Prod.fst).Nodup ∧
  ∀ entry ∈ values, entry.2.Valid env values entry.1

instance (env : Environment) (values : Values) : Decidable (Valid env values) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive Transform (Name : Type := Symbol) where
  | dual (source target : Name)
  | conjugate (source target involution : Name)
  | adjoint (sourceMetric targetMetric : Name)
  deriving Repr, BEq, DecidableEq, Inhabited

def Transform.transpose : Transform Name → Bool
  | .dual .. | .adjoint .. => true
  | .conjugate .. => false

def Transform.conjugates : Transform Name → Bool
  | .dual .. => false
  | .conjugate .. | .adjoint .. => true

def Transform.origin (parent : Symbol) : Transform → MapOrigin
  | .dual .. => .dual parent
  | .conjugate _ _ involution => .conjugate parent involution
  | .adjoint source target => .adjoint parent source target

def Transform.metricContract (values : Values) (original : MapView) : Transform → Prop
  | .adjoint source target => adjointContract values original source target
  | _ => True

instance (values : Values) (original : MapView) (operation : Transform) :
    Decidable (operation.metricContract values original) := by
  cases operation <;> unfold Transform.metricContract <;> infer_instance

inductive Evaluation (Name : Type := Symbol) where
  | dual
  | hermitian (metric : Name)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Operation where
  | space (name : Symbol) (implementation : DeclId) (dimension : Nat)
  | basis (name space : Symbol)
  | involution (name space : Symbol)
  | dualSpace (name parent : Symbol)
  | conjugateSpace (name parent involution : Symbol)
  | derivedBasis (name parent space : Symbol)
  | metric (name basis involution : Symbol) (gram : Gram)
  | transform (name parent : Symbol) (operation : Transform)
  | vector (name loan basis : Symbol)
  | conjugateVector (name parent basis involution : Symbol)
  | evaluate (left right output : Symbol) (operation : Evaluation) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  | map (name loan source target : Symbol)
  | ownedMap (name owner : Symbol) (layout : Layout) (source target : Symbol)
  | ownedView (name loan owner : Symbol)
  | borrowOwned (name owner : Symbol) (access : Access)
  | gemm (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  deriving Repr, BEq, Inhabited

private def reject (message : String) : Except Error α :=
  .error ⟨"E_NUMERICAL_TYPE", message⟩

def insert (env : Environment) (values : Values) (name : Symbol) (value : Value) : Except Error Values := do
  if (value? values name).isSome then reject "numerical value identity is already bound"
  let result := (name, value) :: values
  if Valid env result then return result
  else reject "invalid numerical declaration, identity or value provenance"

def constructSpace (env : Environment) (name : Symbol) (implementation : DeclId) (dimension : Nat) :
    Except Error Space := do
  let some (.implementation marker (.linearDescriptor base coefficient) []) := lookup env implementation
    | reject "space requires a concrete linear representation declaration"
  let some (_, setting, _) := scalarBaseProfile env base
    | reject "linear representation has no geometric scalar base"
  return ⟨⟨implementation, marker⟩, name, base, coefficient, setting, dimension, .primal⟩

def construct (env : Environment) (resources : Storage.State) (values : Values) : Operation → Except Error Values
  | .space name implementation dimension => do
    insert env values name (.space (← constructSpace env name implementation dimension))
  | .basis name space => do
    let some (.space space) := value? values space | reject "basis requires a local linear space"
    insert env values name (.basis ⟨space, name, none⟩)
  | .involution name space => do
    let some (.space space) := value? values space | reject "involution requires a linear space profile"
    insert env values name (.involution (Involution.ofSpace space))
  | .dualSpace name parent => do
    let some (.space space) := value? values parent | reject "dual requires a linear space"
    insert env values name (.space {space with brand := name, origin := .dual parent})
  | .conjugateSpace name parent selected => do
    let some (.space space) := value? values parent | reject "conjugate requires a linear space"
    insert env values name (.space {space with brand := name, origin := .conjugate parent selected})
  | .derivedBasis name parent space => do
    let some (.space space) := value? values space | reject "derived basis requires a derived linear space"
    insert env values name (.basis ⟨space, name, some parent⟩)
  | .metric name basis selected gram => do
    let some (.basis basis) := value? values basis | reject "metric requires an explicit coordinate basis"
    let some (.involution involution) := value? values selected | reject "metric requires an explicit admitted involution"
    insert env values name (.metric ⟨basis, involution, selected, gram⟩)
  | .vector name loan basis => do
    let some (.basis basis) := value? values basis | reject "vector requires an explicit basis"
    let some loan := resources.loan? loan | reject "vector requires a live resource loan"
    let view : VectorView := ⟨basis, loan, false, .direct⟩
    unless view.Live resources do reject "vector requires a live column with the basis dimension and scalar"
    insert env values name (.vector view)
  | .map name loan source target => do
    let some (.basis source) := value? values source | reject "map source requires an explicit basis"
    let some (.basis target) := value? values target | reject "map target requires an explicit basis"
    let some loan := resources.loan? loan | reject "map view requires a live resource loan"
    let view : MapView := ⟨source, target, loan, false, .direct⟩
    unless view.Live resources do reject "map scalar, dimensions or loan state differs from its bases"
    insert env values name (.map view)
  | .ownedMap name owner layout source target => do
    let some (.basis source) := value? values source | reject "owned map source requires an explicit basis"
    let some (.basis target) := value? values target | reject "owned map target requires an explicit basis"
    let some allocation := resources.owner? owner | reject "owned map requires a live owner"
    let view : OwnedMap := ⟨source, target, owner, allocation.identity, layout⟩
    unless view.Live resources do reject "owned map scalar, dimensions or layout differs from its allocation and bases"
    insert env values name (.ownedMap view)
  | .ownedView name loan owner => do
    let some (.ownedMap owned) := value? values owner | reject "owned view requires an owned map"
    let some loan := resources.loan? loan | reject "owned view requires a live loan"
    unless owned.Live resources && loan.allocation == owned.allocation && loan.layout == owned.layout do
      reject "owned view must retain its live allocation and exact coordinate layout"
    let view : MapView := ⟨owned.source, owned.target, loan, false, .direct⟩
    unless view.Live resources do reject "owned view requires an active compatible loan"
    insert env values name (.map view)
  | .gemm .. | .borrowOwned .. | .transform .. | .conjugateVector .. | .evaluate .. =>
    reject "numerical resource operations must pass the composed check"

structure CheckedTransform (env : Environment) (resources : Storage.State) (values : Values)
    (name parent child : Symbol) (operation : Transform) where
  valuesValid : Valid env values
  original : MapView
  fromParent : value? values parent = some (.map original)
  originalLive : original.Live resources
  result : MapView
  after : Storage.State
  borrowed : checkAction resources (.borrow child (.loan original.loan.name)
    (if operation.transpose then original.loan.layout.transpose else original.loan.layout) .read) = .ok after
  resultLoan : after.loan? child = some result.loan
  resultName : result.loan.name = child
  resultOrigin : result.origin = operation.origin parent
  resultFlags : result.conjugate = (if operation.conjugates then !original.conjugate else original.conjugate)
  metricEvidence : operation.metricContract values original
  coordinates : result.loan.layout = (if operation.transpose then original.loan.layout.transpose else original.loan.layout) ∧
    result.loan.allocation = original.loan.allocation ∧ result.loan.parent = some original.loan.name ∧ result.loan.access = .read
  output : Values
  inserted : insert env values name (.map result) = .ok output
  outputValid : Valid env output
  fromOutput : value? output name = some (.map result)
  resultLive : result.Live after

def checkTransform (env : Environment) (resources : Storage.State) (values : Values)
    (name parent child : Symbol) (operation : Transform) :
    Except Error (CheckedTransform env resources values name parent child operation) := do
  if valuesValid : Valid env values then
    match fromParent : value? values parent with
    | some (.map original) =>
      if originalLive : original.Live resources then
        let metricEvidence ← if evidence : operation.metricContract values original then pure (PLift.up evidence)
          else reject "adjoint requires matching declared metrics and orthonormal bases; non-orthonormal metrics require explicit Gram realization"
        let (source, target) ← match operation with
          | .dual source target | .conjugate source target _ => do
            let some (.basis source) := value? values source | reject "transform requires an explicit source basis"
            let some (.basis target) := value? values target | reject "transform requires an explicit target basis"
            pure (source, target)
          | .adjoint source target => do
            let some (.metric source) := value? values source | reject "adjoint requires the source metric"
            let some (.metric target) := value? values target | reject "adjoint requires the target metric"
            unless source.orthonormal && target.orthonormal do
              reject "direct adjoint requires orthonormal bases for the declared metrics; explicit Gram realization is required"
            pure (original.target, original.source)
        let layout := if operation.transpose then original.loan.layout.transpose else original.loan.layout
        match borrowed : checkAction resources (.borrow child (.loan original.loan.name) layout .read) with
        | .error diagnostic => .error diagnostic
        | .ok after =>
          match resultLoan : after.loan? child with
          | none => reject "transform lost its checked child loan"
          | some loan =>
            let conjugate := if operation.conjugates then !original.conjugate else original.conjugate
            let result : MapView := ⟨source, target, loan, conjugate, operation.origin parent⟩
            match inserted : insert env values name (.map result) with
            | .error diagnostic => .error diagnostic
            | .ok output =>
              if outputValid : Valid env output then
                if fromOutput : value? output name = some (.map result) then
                  if resultLive : result.Live after then
                    if resultName : result.loan.name = child then
                      if coordinates : result.loan.layout = layout ∧ result.loan.allocation = original.loan.allocation ∧
                          result.loan.parent = some original.loan.name ∧ result.loan.access = .read then
                        return ⟨valuesValid, original, fromParent, originalLive, result, after,
                          borrowed, resultLoan, resultName, rfl, rfl, metricEvidence.down, coordinates, output, inserted,
                          outputValid, fromOutput, resultLive⟩
                      else reject "transform changed its checked coordinates or read permission"
                    else reject "transform child identity changed"
                  else reject "transformed endpoint dimensions differ from its actual loan"
                else reject "transform lost its result"
              else reject "transform output provenance is invalid"
      else reject "transform requires a live, unsuspended map"
    | _ => reject "transform requires an explicitly typed map"
  else reject "transform input provenance is invalid"

/-- Resolved dependent input contracts. Symbols refer to earlier arguments,
not newly generated objects. Dimensions remain explicit static contracts. -/
inductive Input where
  | space (implementation : DeclId) (dimension : Nat)
  | basis (space : Symbol)
  | map (source target : Symbol)
  | ownedMap (source target : Symbol)
  | involution (space : Symbol)
  | dualSpace (parent : Symbol)
  | conjugateSpace (parent involution : Symbol)
  | derivedBasis (parent space : Symbol)
  | metric (basis involution : Symbol) (orthonormal : Bool)
  | vector (basis : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

def Input.Accepts (resources : Storage.State) (values : Values) : Input → Value → Prop
  | .vector basisId, .vector view => value? values basisId = some (.basis view.basis) ∧ view.Live resources
  | .space implementation dimension, .space spc =>
    spc.type.domain = implementation ∧ spc.dimension = dimension
  | .basis spaceId, .basis bas => value? values spaceId = some (.space bas.space)
  | .map source target, .map view =>
    value? values source = some (.basis view.source) ∧
    value? values target = some (.basis view.target) ∧ view.Live resources
  | .ownedMap source target, .ownedMap view =>
    value? values source = some (.basis view.source) ∧
    value? values target = some (.basis view.target) ∧ view.Live resources ∧ view.Initialized resources
  | .involution spaceId, .involution sigma =>
    (value? values spaceId).any (fun value => match value with
      | .space spc => sigma == Involution.ofSpace spc | _ => false) = true
  | .dualSpace parent, .space spc => spc.origin = .dual parent
  | .conjugateSpace parent selected, .space spc => spc.origin = .conjugate parent selected
  | .derivedBasis parent spaceId, .basis bas => bas.parent = some parent ∧
    value? values spaceId = some (.space bas.space)
  | .metric basisId selected orthonormal, .metric form =>
    value? values basisId = some (.basis form.basis) ∧
    value? values selected = some (.involution form.involution) ∧
    (orthonormal = true → form.orthonormal = true)
  | _, _ => False

instance (resources : Storage.State) (values : Values) (input : Input) (value : Value) :
    Decidable (input.Accepts resources values value) := by
  cases input <;> cases value <;> unfold Input.Accepts <;> infer_instance

structure CheckedInput (env : Environment) (resources : Storage.State) (values : Values)
    (input : Input) (actual : Symbol) where
  valuesValid : Valid env values
  resourcesValid : auditState resources = true
  value : Value
  fromActual : value? values actual = some value
  accepts : input.Accepts resources values value

/-- Check all actuals against the original caller state. Reborrowing one read
input must not make a second compatible use of that same caller map stale. The
resource checker independently checks the subsequently created sibling loans. -/
def checkInput (env : Environment) (resources : Storage.State) (values : Values)
    (input : Input) (actual : Symbol) : Except Error (CheckedInput env resources values input actual) := do
  if resourcesValid : auditState resources then
    if valuesValid : Valid env values then
      match fromActual : value? values actual with
      | none => reject "numerical argument is absent or has a resource-only type"
      | some value =>
        if accepts : input.Accepts resources values value then
          return ⟨valuesValid, resourcesValid, value, fromActual, accepts⟩
        else reject "numerical argument violates its nominal, shape or live-loan contract"
    else reject "invalid numerical argument provenance"
  else reject "invalid numerical argument resource state"

structure Product where
  left : MapView
  right : MapView
  output : MapView
  alpha : Option Coefficient := none
  beta : Option Coefficient := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A : V → W, B : U → V, output : U → W. Equality includes the nominal
objects and basis identities, not merely their dimensions or scalar kinds. -/
def Product.Composable (product : Product) : Prop :=
  product.left.source = product.right.target ∧
  product.output.source = product.right.source ∧
  product.output.target = product.left.target

instance (product : Product) : Decidable product.Composable :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Product.request (product : Product) (mode : GemmMode) (policy : NumericalPolicy) : Gemm :=
  ⟨product.left.loan.name, product.right.loan.name, product.output.loan.name,
    product.left.conjugate, product.right.conjugate, mode, policy,
    product.alpha, product.beta⟩

structure CheckedProduct (env : Environment) (resources : Storage.State) (values : Values)
    (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
    (alpha beta : Option Coefficient := none) where
  valuesValid : Valid env values
  resourcesValid : auditState resources = true
  product : Product
  leftFrom : value? values left = some (.map product.left)
  rightFrom : value? values right = some (.map product.right)
  outputFrom : value? values output = some (.map product.output)
  composable : product.Composable
  leftLive : product.left.Live resources
  rightLive : product.right.Live resources
  outputLive : product.output.Live resources
  outputDirect : product.output.conjugate = false
  storage : CheckedGemm resources (product.request mode policy)
  storageAccepted : checkGemm resources (product.request mode policy) = .ok storage
  coefficients : product.alpha = alpha ∧ product.beta = beta

def checkProduct (env : Environment) (resources : Storage.State) (values : Values)
    (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
    (alpha beta : Option Coefficient := none) :
    Except Error (CheckedProduct env resources values left right output mode policy alpha beta) := do
  if resourcesValid : auditState resources then
    if valid : Valid env values then
      match leftFrom : value? values left, rightFrom : value? values right, outputFrom : value? values output with
      | some (.map a), some (.map b), some (.map c) =>
        let product : Product := ⟨a, b, c, alpha, beta⟩
        if composable : product.Composable then
          if leftLive : a.Live resources then
            if rightLive : b.Live resources then
              if outputLive : c.Live resources then
                if outputDirect : c.conjugate = false then
                  match storageAccepted : checkGemm resources (product.request mode policy) with
                  | .error diagnostic => .error diagnostic
                  | .ok storage => return ⟨valid, resourcesValid, product, leftFrom, rightFrom, outputFrom,
                      composable, leftLive, rightLive, outputLive, outputDirect, storage, storageAccepted, ⟨rfl, rfl⟩⟩
                else reject "GEMM output cannot be a lazy conjugated view"
              else reject "output map no longer matches its resource loan"
            else reject "right map no longer matches its resource loan"
          else reject "left map no longer matches its resource loan"
        else reject "GEMM requires the exact middle and outer objects and bases"
      | _, _, _ => reject "GEMM operands must be explicit typed map views"
    else reject "invalid numerical environment or value provenance"
  else reject "invalid numerical resource state"

end VastitasKernel.Storage.Numerical
