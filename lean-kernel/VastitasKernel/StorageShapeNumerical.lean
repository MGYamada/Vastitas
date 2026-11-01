import VastitasKernel.StorageShapes
import VastitasKernel.StorageNumerical

/-! Nominal numerical values over symbolic extents. Profile authority and
generative identities are static; dimensions are immutable scalar references.
The interpretation is the existing numerical Space/Basis/MapView, and each
product carries the exact symbolic resource transition for its GEMM. -/
namespace VastitasKernel.Storage.Shapes.Numerical
open Indexed

structure Space where
  type : ObjectType
  brand : Symbol
  base : DeclId
  coefficient : CoefficientKind
  setting : GeometricSetting
  dimension : Extent
  deriving Repr, BEq, DecidableEq, Inhabited

def Space.scalar (space : Space) : Scalar :=
  match space.coefficient with | .real => .f64 | .complex => .complexF64

def Space.eval (values : Valuation) (space : Space) : Storage.Numerical.Space :=
  ⟨space.type, space.brand, space.base, space.coefficient, space.setting,
    space.dimension.eval values, .primal⟩

/-- Exactly the declaration/profile portion of the actual Space.Valid check.
No representative dimension is used to certify a runtime shape. -/
def Space.Valid (environment : Environment) (space : Space) : Prop :=
  lookup environment space.type.domain = some (.implementation space.type.marker
    (.linearDescriptor space.base space.coefficient) []) ∧
  space.type.Valid environment ∧
  (scalarBaseProfile environment space.base).map (fun profile => profile.2.1) = some space.setting

instance (environment : Environment) (space : Space) : Decidable (space.Valid environment) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Basis where
  space : Space
  brand : Symbol
  deriving Repr, BEq, DecidableEq, Inhabited

def Basis.eval (values : Valuation) (basis : Basis) : Storage.Numerical.Basis :=
  ⟨basis.space.eval values, basis.brand, none⟩

structure Map where
  source : Basis
  target : Basis
  loan : Shapes.Loan
  layout : Shapes.Layout
  origin : Option Symbol := none
  deriving Repr, BEq, DecidableEq, Inhabited

def Map.eval (values : Valuation) (view : Map) : Storage.Numerical.MapView :=
  ⟨view.source.eval values, view.target.eval values, view.loan.eval values,
    false, match view.origin with | none => .direct | some parent => .reborrow parent⟩

def Map.Compatible (view : Map) : Prop :=
  view.source.space.type = view.target.space.type ∧
  view.source.space.base = view.target.space.base ∧
  view.source.space.coefficient = view.target.space.coefficient ∧
  view.source.space.setting = view.target.space.setting

instance (view : Map) : Decidable view.Compatible :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Map.Live (frame : Frame) (view : Map) : Prop :=
  frame.loan? view.loan.name = some view.loan ∧
  frame.suspended view.loan.name = false ∧
  (frame.allocation? view.loan.allocation).map Allocation.scalar = some view.source.space.scalar ∧
  (frame.allocation? view.loan.allocation).map Allocation.layout = some view.layout

instance (frame : Frame) (view : Map) : Decidable (view.Live frame) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Map.guards (view : Map) : List Guard :=
  [.equal view.layout.logicalRows view.target.space.dimension,
   .equal view.layout.logicalColumns view.source.space.dimension]

inductive Value where
  | space (value : Space)
  | basis (value : Basis)
  | map (value : Map)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Values := List (Symbol × Value)

def value? (values : Values) (name : Symbol) : Option Value :=
  (values.find? (·.1 == name)).map Prod.snd

def Value.eval (values : Valuation) : Value → Storage.Numerical.Value
  | .space spc => .space (spc.eval values)
  | .basis bas => .basis (bas.eval values)
  | .map view => .map (view.eval values)

def interpret (valuation : Valuation) (values : Values) : Storage.Numerical.Values :=
  values.map fun (name, value) => (name, value.eval valuation)

def originValid (values : Values) (name : Symbol) (view : Map) : Bool :=
  match view.origin with
  | none => true
  | some parent => parent < name && match value? values parent with
    | some (.map original) =>
      view.source == original.source && view.target == original.target &&
      view.loan.allocation == original.loan.allocation && view.loan.parent == some original.loan.name &&
      view.layout == original.layout
    | _ => false

def Value.Valid (environment : Environment) (values : Values) (name : Symbol) : Value → Prop
  | .space spc => spc.brand = name ∧ spc.Valid environment
  | .basis bas => bas.brand = name ∧
    value? values bas.space.brand = some (.space bas.space)
  | .map view => view.loan.layout = view.layout ∧ view.Compatible ∧
    value? values view.source.brand = some (.basis view.source) ∧
    value? values view.target.brand = some (.basis view.target) ∧ originValid values name view = true

instance (environment : Environment) (values : Values) (name : Symbol) (value : Value) :
    Decidable (value.Valid environment values name) := by
  cases value <;> unfold Value.Valid <;> infer_instance

def Valid (environment : Environment) (values : Values) : Prop :=
  environment.Valid ∧ values.length ≤ 4096 ∧ (values.map Prod.fst).Nodup ∧
  ∀ entry ∈ values, entry.2.Valid environment values entry.1

instance (environment : Environment) (values : Values) : Decidable (Valid environment values) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def guards (values : Values) : List Guard := values.flatMap fun (_, value) => match value with
  | .space space => [.bound space.dimension dimensionLimit]
  | .basis _ => []
  | .map view => view.guards

private def reject (message : String) : Except Error α :=
  .error ⟨"E_RUNTIME_NUMERICAL", message⟩

def insert (environment : Environment) (values : Values) (name : Symbol) (value : Value) :
    Except Error Values := do
  if (value? values name).isSome then reject "runtime numerical name is already bound"
  let result := (name, value) :: values
  if Valid environment result then return result
  else reject "invalid runtime numerical profile, identity or provenance"

inductive Operation where
  | space (name : Symbol) (implementation : DeclId) (dimension : Extent)
  | basis (name space : Symbol)
  | map (name loan source target : Symbol)
  | gemm (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : Option Coefficient := none)
  deriving Repr, BEq, DecidableEq, Inhabited

def construct (environment : Environment) (frame : Frame) (values : Values) :
    Operation → Except Error Values
  | .space name implementation dimension => do
    let some (.implementation marker (.linearDescriptor base coefficient) []) := lookup environment implementation
      | reject "runtime space requires a concrete linear representation declaration"
    let some (_, setting, _) := scalarBaseProfile environment base
      | reject "runtime space has no scalar base profile"
    insert environment values name (.space ⟨⟨implementation, marker⟩, name, base, coefficient, setting, dimension⟩)
  | .basis name source => do
    let some (.space space) := value? values source | reject "runtime basis requires a runtime space"
    insert environment values name (.basis ⟨space, name⟩)
  | .map name loan source target => do
    let some (.basis source) := value? values source | reject "runtime map source requires a runtime basis"
    let some (.basis target) := value? values target | reject "runtime map target requires a runtime basis"
    let some loan := frame.loan? loan | reject "runtime map requires a runtime loan"
    let some allocation := frame.allocation? loan.allocation | reject "runtime map allocation is absent"
    let view : Map := ⟨source, target, loan, allocation.layout, none⟩
    unless view.Live frame do reject "runtime map scalar or loan snapshot differs"
    insert environment values name (.map view)
  | .gemm .. => reject "runtime GEMM requires the composed product checker"

structure Product where
  left : Map
  right : Map
  output : Map
  alpha : Option Coefficient := none
  beta : Option Coefficient := none
  deriving Repr, BEq, DecidableEq, Inhabited

def Product.Composable (product : Product) : Prop :=
  product.left.source = product.right.target ∧
  product.output.source = product.right.source ∧
  product.output.target = product.left.target

instance (product : Product) : Decidable product.Composable :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Product.request (product : Product) (mode : GemmMode) (policy : NumericalPolicy) : Gemm :=
  ⟨product.left.loan.name, product.right.loan.name, product.output.loan.name,
    false, false, mode, policy, product.alpha, product.beta⟩

structure CheckedProduct (environment : Environment) (frame : Frame) (values : Values)
    (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
    (alpha beta : Option Coefficient := none) where
  valuesValid : Valid environment values
  product : Product
  leftFrom : value? values left = some (.map product.left)
  rightFrom : value? values right = some (.map product.right)
  outputFrom : value? values output = some (.map product.output)
  composable : product.Composable
  leftLive : product.left.Live frame
  rightLive : product.right.Live frame
  outputLive : product.output.Live frame
  storage : CheckedStep frame (.gemm (product.request mode policy))
  accepted : checkStep frame (.gemm (product.request mode policy)) = .ok storage
  coefficients : product.alpha = alpha ∧ product.beta = beta

def checkProduct (environment : Environment) (frame : Frame) (values : Values)
    (left right output : Symbol) (mode : GemmMode) (policy : NumericalPolicy)
    (alpha beta : Option Coefficient := none) :
    Except Error (CheckedProduct environment frame values left right output mode policy alpha beta) := do
  if valid : Valid environment values then
    match leftFrom : value? values left, rightFrom : value? values right, outputFrom : value? values output with
    | some (.map a), some (.map b), some (.map c) =>
      let product : Product := ⟨a, b, c, alpha, beta⟩
      if composable : product.Composable then
        if leftLive : a.Live frame then
          if rightLive : b.Live frame then
            if outputLive : c.Live frame then
              match accepted : checkStep frame (.gemm (product.request mode policy)) with
              | .error problem => .error problem
              | .ok storage => return ⟨valid, product, leftFrom, rightFrom, outputFrom, composable,
                  leftLive, rightLive, outputLive, storage, accepted, ⟨rfl, rfl⟩⟩
            else reject "runtime destination map is no longer live"
          else reject "runtime right map is no longer live"
        else reject "runtime left map is no longer live"
      else reject "runtime GEMM requires exact nominal objects and bases"
    | _, _, _ => reject "runtime GEMM requires runtime map values"
  else reject "invalid runtime numerical environment"

end VastitasKernel.Storage.Shapes.Numerical
