import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.ResourceSource

/-! Experimental, deliberately partial admission model for #350. Nothing in
Main imports this module. These adapters reuse the existing Core/resource
checks; they neither accept public source nor add a Domain Checker. -/
namespace VastitasKernel.UniverseAdmission
open Indexed.Core Storage

/-- A closed compile-time code family, not first-class object-level `Type`. -/
inductive RuntimeTy where
  | scalar (type : PureType)
  | tensorShape (shape : Shapes.Layout)
  | ownedMap (source target : Numerical.Basis)

def ScalarEl : PureType → Type
  | .nat => Nat
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .pair .nat => Nat × Nat
  | .pair .int => Int × Int

/-- The owned-map interpretation describes finite *bit-pattern coordinates*.
It is neither RR/CC nor a claim about the contents of a native allocation.
Shape interpretation is mathematical metadata, including invalid layouts. -/
def El : RuntimeTy → Type
  | .scalar type => ScalarEl type
  | .tensorShape shape => {meaning : Shapes.Valuation → Storage.Layout // meaning = shape.eval}
  | .ownedMap source target =>
      Fin target.space.dimension → Fin source.space.dimension →
        { value : Literal // value.scalar = source.space.scalar }

def scalarValue : (type : PureType) → ScalarEl type → Semantics.Value
  | .nat, value => .natural value
  | .int, value => .integer value
  | .bool, value => .boolean value
  | .unit, _ => .unit
  | .pair .nat, value => .pairNat value.1 value.2
  | .pair .int, value => .pairInt value.1 value.2

/-- Only this small computational profile has pure arrows in the first model.
There is intentionally no constructor taking an arbitrary Lean function.
Ownership transitions use the existing indexed receipts below, not pure arrows. -/
inductive CoreHom : RuntimeTy → RuntimeTy → Type where
  | identity (type : PureType) : CoreHom (.scalar type) (.scalar type)
  | natToInt : CoreHom (.scalar .nat) (.scalar .int)
  | booleanNot : CoreHom (.scalar .bool) (.scalar .bool)
  | nonnegative : CoreHom (.scalar .int) (.scalar .bool)

def denote : CoreHom a b → El a → El b
  | .identity _, value => value
  | .natToInt, value => Int.ofNat value
  | .booleanNot, value => !value
  | .nonnegative, value => @decide ((0 : Int) ≤ value) (Int.decLe 0 value)

def CoreHom.input : CoreHom a b → PureType
  | .identity type => type
  | .natToInt => .nat
  | .booleanNot => .bool
  | .nonnegative => .int

def CoreHom.output : CoreHom a b → PureType
  | .identity type => type
  | .natToInt => .int
  | .booleanNot => .bool
  | .nonnegative => .bool

def parameter (type : PureType) : Indexed.Core.Term := .variable 0 ⟨.pure type, none⟩

def CoreHom.term : CoreHom a b → Indexed.Core.Term
  | .identity type => parameter type
  | .natToInt => .natToInt (parameter .nat)
  | .booleanNot => .unary .not (parameter .bool) ⟨.pure .bool, none⟩
  | .nonnegative => .binary .ge (parameter .int) (.integer 0) ⟨.pure .bool, none⟩

/-- A meta-level type parameter is specialized before the existing Core audit.
This is a finite example, not the source specializer's staging theorem. -/
def CoreHom.module (operation : CoreHom a b) : Module :=
  let owner : Namespace.Owner := ⟨⟨⟨"/universe-model", "universe-model", "0"⟩, []⟩, "operation"⟩
  ⟨⟨[], [], []⟩,
    [⟨0, owner, [⟨0, ⟨.pure operation.input, none⟩⟩],
      .pure operation.output, operation.term, {}⟩], none⟩

def stage (operation : CoreHom a b) : Except Diagnostic (Typing.CheckedModule false) :=
  Typing.checkModule operation.module false

/-- Syntactic, fail-closed meta bridge. No normalization, arbitrary `Type u`,
function spaces, aliases, or reflection of RuntimeTy into itself is supported.
Returning a code is not source acceptance or representation evidence. -/
def scalarCode? : Lean.Expr → Option RuntimeTy
  | .const ``Nat [] => some (.scalar .nat)
  | .const ``Int [] => some (.scalar .int)
  | .const ``Bool [] => some (.scalar .bool)
  | .const ``Unit [] => some (.scalar .unit)
  | _ => none

/-- Only literal syntax crosses this tiny value bridge. In particular it never
evaluates a Lean function, a proof, `Classical.choice`, or a quoted type. -/
def literalCore? : Lean.Expr → Option Indexed.Core.Term
  | .lit (.natVal value) => some (.natural value)
  | .const ``Bool.true [] => some (.boolean true)
  | .const ``Bool.false [] => some (.boolean false)
  | .const ``Unit.unit [] => some .unit
  | _ => none

inductive Target where
  | leanLP64

structure Context where
  environment : Indexed.Environment := []
  numerical : Numerical.Values := []
  resources : Storage.State := {}
  slots : Shapes.Slots := []

/-- Projection of the actual protocol-8 execution certificate, not reconstructed
source acceptance. Intermediate map transfers also retain their own receipts. -/
def Context.ofExecution {functions : List Functions.Function} {entry : Nat}
    {environment : Indexed.Environment} {signatures : List ValueFlow.Signature}
    (execution : ResourceSource.Execution functions entry environment signatures) : Context :=
  ⟨environment, execution.checked.context.numerical,
    execution.checked.context.resources, execution.checked.context.scalarSlots⟩

/-- Explicit representation request, separate from the mathematical code. -/
inductive Representation where
  | scalar
  | tensorShape (scalar : Storage.Scalar) (elements : Shapes.Extent)
  | ownedMap (name : Symbol)

/-- These are the existing component predicates, not a new logical authority.
A shape is only *conditionally* representable: runtime layout guards still have
to hold. Owned-map admission preserves exact nominal bases and actual storage. -/
def layoutable (target : Target) (context : Context) (type : RuntimeTy)
    (representation : Representation) : Bool :=
  match target with
  | .leanLP64 => match type, representation with
    | .scalar _, .scalar => true
    | .tensorShape shape, .tensorShape scalar elements =>
        (Shapes.check context.slots {} [.allocate 0 scalar elements shape]).isOk
    | .ownedMap source target, .ownedMap name =>
        decide (Numerical.Valid context.environment context.numerical) &&
        auditState context.resources &&
        match Numerical.value? context.numerical name with
        | some (.ownedMap view) =>
            decide (view.source = source ∧ view.target = target ∧
              view.Live context.resources ∧ view.Initialized context.resources)
        | _ => false
    | _, _ => false

def Layoutable (target : Target) (context : Context) (type : RuntimeTy)
    (representation : Representation) : Prop :=
  layoutable target context type representation = true

structure Admitted (target : Target) (context : Context) (type : RuntimeTy)
    (request : Option Representation) where
  representation : Representation
  supplied : request = some representation
  layout : Layoutable target context type representation

def admit (target : Target) (context : Context) (type : RuntimeTy)
    (request : Option Representation) : Except String (Admitted target context type request) :=
  match request with
  | none => .error "missing representation evidence"
  | some representation =>
      if layout : layoutable target context type representation = true then
        .ok ⟨representation, rfl, layout⟩
      else .error "representation is outside the admitted component profile"

/-- Physical realization is a second step. A symbolic acceptance certificate
alone is not a statically known layout and is not native memory safety. -/
structure RealizedShape (values : Shapes.Valuation) (scalar : Storage.Scalar)
    (elements : Shapes.Extent) (shape : Shapes.Layout) where
  layout : Storage.Layout
  exact : layout = shape.eval values
  physical : checkLayout scalar (elements.eval values * scalar.width) layout = true

def realizeShape
    (_admitted : Admitted target context (.tensorShape shape) (some (.tensorShape scalar elements)))
    (values : Shapes.Valuation) : Except String (RealizedShape values scalar elements shape) :=
  if physical : checkLayout scalar (elements.eval values * scalar.width) (shape.eval values) = true then
    .ok ⟨shape.eval values, rfl, physical⟩
  else .error "runtime shape guard failed"

/-- State-indexed moves remain the production ownership checker's transitions.
This alias does not turn an owned buffer into an unrestricted pure function. -/
abbrev OwnedTransfer := Functions.OwnedMapTransfer

end VastitasKernel.UniverseAdmission
