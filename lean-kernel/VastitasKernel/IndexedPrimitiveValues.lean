import VastitasKernel.IndexedSmoothContracts
import VastitasKernel.IndexedRuntime

set_option autoImplicit false

/-! The values of the closed primitive registry (#622).

The logical values the Core semantics computes (`Value`), the erased runtime
values of generated programs (`PrimitiveRuntimeValue`), the erasure between
them and the value builders of the variadic primitives live here so that each
registry entry can carry its own evaluators. They are the definitions of
`IndexedSemantics`, moved as they were; that module keeps the typing of values
against worlds and the term evaluator. Implementation IDs are logical tags
erased before native execution; they are not dispatch keys or runtime equality
tests. Other value shapes are not registry operands; the erased values are not
a dynamic fallback for unsupported indexed families. -/
namespace VastitasKernel.Indexed.Core.Semantics

structure Object where
  implementation : DeclId
  descriptor : IndexedRuntime.Object
  deriving Repr, DecidableEq

def globalObject (env : Indexed.Environment) (id : DeclId) : Option Object := do
  let implementation ← (Indexed.lookup env id).bind Declaration.objectImplementation?
  pure ⟨implementation, IndexedRuntime.baseObject⟩

structure Point where
  target : Object
  source : Object
  deriving Repr, DecidableEq

def Point.erase (point : Point) : IndexedRuntime.Point :=
  ⟨point.target.descriptor, point.source.descriptor⟩

structure Morphism where
  source : Object
  target : Object
  deriving Repr, DecidableEq

def Morphism.erase (map : Morphism) : IndexedRuntime.Morphism :=
  ⟨map.source.descriptor, map.target.descriptor⟩

inductive IndexedValue where
  | token
  | point (value : Point)
  | morphism (value : Morphism)
  /-- A morphism over a base between presented objects: its exact pullback map. -/
  | relative (value : AlgebraRuntime.Map)
  /-- A smooth map between smooth objects: the program that checked Core builds. -/
  | smooth (value : SmoothRuntime.Program)
  /-- A vector or covector at a point of a smooth object, or the failure value
  `none`. The variance is the variance of its family. -/
  | fiber (variance : Variance) (value : SmoothRuntime.FiberValue)
  /-- The saved forward values of a smooth program at a point. -/
  | tape (value : SmoothRuntime.Tape)
  deriving Repr, DecidableEq

inductive Value where
  | natural (value : Nat)
  | integer (value : Int)
  | boolean (value : Bool)
  | unit
  | pairNat (first second : Nat)
  | pairInt (first second : Int)
  | object (value : Object)
  | indexed (value : IndexedValue)
  | package (witness : Object) (fields : List IndexedValue)
  deriving Repr, DecidableEq

def Value.integer? : Value → Option Int
  | .integer value => some value
  | _ => none

def intPointValue (values : List Value) : Option Value := do
  let coordinates ← values.mapM Value.integer?
  pure (.indexed (.relative (AlgebraRuntime.Map.intPoint coordinates)))

def smoothPointValue (values : List Value) : Option Value := do
  let coordinates ← values.mapM Value.integer?
  pure (.indexed (.smooth (SmoothRuntime.intPoint coordinates)))

/-- A fiber of `family` at `point` from integer components. Its variance is
the declared variance of `family`. -/
def fiberVectorValue (env : Indexed.Environment) (family : DeclId) (point : SmoothRuntime.Program)
    (values : List Value) : Option Value := do
  let variance ← fiberVariance? env family
  let components ← values.mapM Value.integer?
  pure (.indexed (.fiber variance (SmoothRuntime.vector point components)))

/-- The closed registry's erased operands/results use the actual runtime
structures linked into generated programs. Other value shapes are not registry
operands; this is not a dynamic fallback for unsupported indexed families. -/
inductive PrimitiveRuntimeValue where
  | natural (value : Nat)
  | object (value : IndexedRuntime.Object)
  | point (value : IndexedRuntime.Point)
  | morphism (value : IndexedRuntime.Morphism)
  | relative (value : AlgebraRuntime.Map)
  | smooth (value : SmoothRuntime.Program)
  | fiber (value : SmoothRuntime.FiberValue)
  | tape (value : SmoothRuntime.Tape)
  | boolean (value : Bool)
  | integer (value : Int)
  | pairInt (first second : Int)
  deriving Repr, DecidableEq

def erasePrimitiveValue : Value → Option PrimitiveRuntimeValue
  | .natural value => some (.natural value)
  | .boolean value => some (.boolean value)
  | .integer value => some (.integer value)
  | .pairInt first second => some (.pairInt first second)
  | .indexed (.relative map) => some (.relative map)
  | .object object => some (.object object.descriptor)
  | .indexed (.point point) => some (.point point.erase)
  | .indexed (.morphism map) => some (.morphism map.erase)
  | .indexed (.smooth program) => some (.smooth program)
  | .indexed (.fiber _ value) => some (.fiber value)
  | .indexed (.tape tape) => some (.tape tape)
  | _ => none

def PrimitiveRuntimeValue.integer? : PrimitiveRuntimeValue → Option Int
  | .integer value => some value
  | _ => none

def intPointRuntime (values : List PrimitiveRuntimeValue) : Option PrimitiveRuntimeValue := do
  let coordinates ← values.mapM PrimitiveRuntimeValue.integer?
  pure (.relative (AlgebraRuntime.Map.intPoint coordinates))

def smoothPointRuntime (values : List PrimitiveRuntimeValue) : Option PrimitiveRuntimeValue := do
  let coordinates ← values.mapM PrimitiveRuntimeValue.integer?
  pure (.smooth (SmoothRuntime.intPoint coordinates))

def fiberVectorRuntime (point : SmoothRuntime.Program) (values : List PrimitiveRuntimeValue) :
    Option PrimitiveRuntimeValue := do
  let components ← values.mapM PrimitiveRuntimeValue.integer?
  pure (.fiber (SmoothRuntime.vector point components))

end VastitasKernel.Indexed.Core.Semantics
