import VastitasKernel.IndexedValidity

set_option autoImplicit false

/-! The operand association of a primitive as data (#622).

A `Shape` says what a primitive's operands look like, which of their indices
must agree, and what the result type is. `IndexedPrimitives` derives the
association contract, result inference and the operand count from it,
`IndexedCore` the argument hints, and `IndexedSourceDiagnostics` the role
table that explains a rejected call. One shape therefore cannot disagree with
itself across those tables.

Operands and their indices are named by position. `Slot.var` and
`Slot.fixed` carry the field names and reasons that diagnostics print, so the
messages stay the ones each primitive documents. -/
namespace VastitasKernel.Indexed

/-- An index of an operand: index `slot` of the application at `operand`. -/
structure Position where
  operand : Nat
  slot : Nat
  deriving Repr, Inhabited, DecidableEq

/-- One index of an indexed operand. `field` names it in diagnostics. -/
inductive Slot where
  /-- Any object reference. -/
  | var (field : String)
  /-- Exactly `ref`; a mismatch is reported with `reason`. -/
  | fixed (ref : ObjectRef) (field reason : String)
  /-- An index the primitive does not read. -/
  | any
  deriving Repr, Inhabited, DecidableEq

/-- One operand. `role` names it in diagnostics. -/
inductive Operand where
  /-- A dimension literal. -/
  | natural
  /-- An object whose type must refine `expected`. -/
  | object (role : String) (expected : ObjectType)
  /-- An application of `family` whose indices have the given shape. -/
  | indexed (role : String) (family : DeclId) (slots : List Slot)
  /-- Any application of `family`, read as a whole. -/
  | application (role : String) (family : DeclId)
  deriving Repr, Inhabited, DecidableEq

/-- A side condition on the operands. The role table lists the requirements
that explain each one's failure, in the order the shape lists them. -/
inductive Relation where
  /-- The reference at `second` is the reference at `first`. -/
  | sameRef (first second : Position)
  /-- The applications at the two operands are equal; `fields` name their indices. -/
  | sameApplication (first second : Nat) (fields : List String)
  /-- The reference at `position` is the one the environment gives. -/
  | fixedFrom (position : Position) (lookup : Environment → Option ObjectRef) (reason : String)
  /-- The reference at `position` is a global smooth object of this dimension. -/
  | pointDimension (position : Position) (dimension : Nat)
  /-- The object operand's type refines the operand's expected type. -/
  | refines (operand : Nat)
  /-- The result's brand is fresh. -/
  | freshBrand

/-- One index of a result application. -/
inductive TemplateSlot where
  | index (position : Position)
  | objectRef (operand : Nat)
  | fixed (ref : ObjectRef)
  deriving Repr, Inhabited, DecidableEq

/-- The result type, built from the operands. -/
inductive ResultTemplate where
  | natural
  | boolean
  | integerPair
  /-- A fresh object of the implementation's type. -/
  | freshObject (implementation : DeclId)
  /-- The declared global object. -/
  | globalObject (id : DeclId)
  | indexed (family : DeclId) (slots : List TemplateSlot)
  /-- The application at the operand, unchanged. -/
  | application (operand : Nat)
  | constant (application : Application)
  /-- No call is well formed: evidence bindings. -/
  | uncallable
  deriving Repr, Inhabited, DecidableEq

/-- When the role table reports the operands' families: `shaped`, once every
operand has the shape's index pattern, so that a wrongly shaped operand is a
shape mismatch and not a role failure; `early`, as soon as every operand is of
the expected kind, before its index pattern is checked. An `application`
operand has no index pattern, so the two agree on it. -/
inductive FamilyPrecedence where
  | shaped
  | early
  deriving Repr, Inhabited, DecidableEq

structure Shape where
  operands : List Operand
  /-- A variadic tail of integers, with its count. -/
  tail : Option (Environment → Nat) := none
  relations : List Relation := []
  result : ResultTemplate
  /-- When the role table reports the operands' families. -/
  families : FamilyPrecedence := .shaped

/-- The shape of an evidence binding, which no call can use. -/
def Shape.uncallable : Shape := { operands := [], result := .uncallable }

/-- Whether a call allocates: its result is a fresh object, bound to the
result's brand in the logical world. -/
def Shape.allocates (shape : Shape) : Bool := shape.result matches .freshObject _

/-- The indexed operands a result template reads. Inference checks their
index shape and leaves every other indexed operand to the association; an
object operand's reference is read whatever its type, so it needs no check. -/
def ResultTemplate.reads : ResultTemplate → List Nat
  | .indexed _ slots => slots.filterMap fun | .index position => some position.operand | _ => none
  | .application operand => [operand]
  | _ => []

end VastitasKernel.Indexed
