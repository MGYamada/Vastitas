import VastitasKernel.IndexedAudit
import VastitasKernel.Storage

/-! Nominal numerical values for the resource function compiler. Constructors
reconstruct profiles from the common indexed environment; dimensions are not
object identities. A map is an explicit interpretation of a live buffer in two
bases, not evidence of field laws or a theorem about its floating-point payload.
This internal component does not introduce a public wire format. -/
namespace VastitasKernel.Storage.Numerical
open Indexed

structure Space where
  type : ObjectType
  brand : Symbol
  base : DeclId
  coefficient : CoefficientKind
  setting : GeometricSetting
  dimension : Nat
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
  deriving Repr, BEq, DecidableEq, Inhabited

structure MapView where
  source : Basis
  target : Basis
  loan : Loan
  deriving Repr, BEq, DecidableEq, Inhabited

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
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Values := List (Symbol × Value)

def value? (values : Values) (name : Symbol) : Option Value :=
  (values.find? (·.1 == name)).map Prod.snd

/-- A forged basis cannot invent a space, and a forged map cannot invent bases.
Stored maps may outlive a loan, but every use rechecks Live against real state. -/
def Value.Valid (env : Environment) (values : Values) (name : Symbol) : Value → Prop
  | .space spc => spc.brand = name ∧ spc.Valid env
  | .basis bas => bas.brand = name ∧
      value? values bas.space.brand = some (.space bas.space)
  | .map view => view.Compatible ∧
      value? values view.source.brand = some (.basis view.source) ∧
      value? values view.target.brand = some (.basis view.target)
  | .ownedMap view => view.Compatible ∧
      value? values view.source.brand = some (.basis view.source) ∧
      value? values view.target.brand = some (.basis view.target)

instance (env : Environment) (values : Values) (name : Symbol) (value : Value) :
    Decidable (value.Valid env values name) := by
  cases value <;> unfold Value.Valid <;> infer_instance

def Valid (env : Environment) (values : Values) : Prop :=
  env.Valid ∧ values.length ≤ 4096 ∧ (values.map Prod.fst).Nodup ∧
  ∀ entry ∈ values, entry.2.Valid env values entry.1

instance (env : Environment) (values : Values) : Decidable (Valid env values) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

inductive Operation where
  | space (name : Symbol) (implementation : DeclId) (dimension : Nat)
  | basis (name space : Symbol)
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
  return ⟨⟨implementation, marker⟩, name, base, coefficient, setting, dimension⟩

def construct (env : Environment) (resources : Storage.State) (values : Values) : Operation → Except Error Values
  | .space name implementation dimension => do
    insert env values name (.space (← constructSpace env name implementation dimension))
  | .basis name space => do
    let some (.space space) := value? values space | reject "basis requires a local linear space"
    insert env values name (.basis ⟨space, name⟩)
  | .map name loan source target => do
    let some (.basis source) := value? values source | reject "map source requires an explicit basis"
    let some (.basis target) := value? values target | reject "map target requires an explicit basis"
    let some loan := resources.loan? loan | reject "map view requires a live resource loan"
    let view : MapView := ⟨source, target, loan⟩
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
    let view : MapView := ⟨owned.source, owned.target, loan⟩
    unless view.Live resources do reject "owned view requires an active compatible loan"
    insert env values name (.map view)
  | .gemm .. | .borrowOwned .. => reject "numerical resource operations must pass the composed check"

/-- Resolved dependent input contracts. Symbols refer to earlier arguments,
not newly generated objects. Dimensions remain explicit static contracts. -/
inductive Input where
  | space (implementation : DeclId) (dimension : Nat)
  | basis (space : Symbol)
  | map (source target : Symbol)
  | ownedMap (source target : Symbol)
  deriving Repr, BEq, DecidableEq, Inhabited

def Input.Accepts (resources : Storage.State) (values : Values) : Input → Value → Prop
  | .space implementation dimension, .space spc =>
    spc.type.domain = implementation ∧ spc.dimension = dimension
  | .basis spaceId, .basis bas => value? values spaceId = some (.space bas.space)
  | .map source target, .map view =>
    value? values source = some (.basis view.source) ∧
    value? values target = some (.basis view.target) ∧ view.Live resources
  | .ownedMap source target, .ownedMap view =>
    value? values source = some (.basis view.source) ∧
    value? values target = some (.basis view.target) ∧ view.Live resources ∧ view.Initialized resources
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
  ⟨product.left.loan.name, product.right.loan.name, product.output.loan.name, false, false, mode, policy,
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
                match storageAccepted : checkGemm resources (product.request mode policy) with
                | .error diagnostic => .error diagnostic
                | .ok storage => return ⟨valid, resourcesValid, product, leftFrom, rightFrom, outputFrom,
                    composable, leftLive, rightLive, outputLive, storage, storageAccepted, ⟨rfl, rfl⟩⟩
              else reject "output map no longer matches its resource loan"
            else reject "right map no longer matches its resource loan"
          else reject "left map no longer matches its resource loan"
        else reject "GEMM requires the exact middle and outer objects and bases"
      | _, _, _ => reject "GEMM operands must be explicit typed map views"
    else reject "invalid numerical environment or value provenance"
  else reject "invalid numerical resource state"

end VastitasKernel.Storage.Numerical
