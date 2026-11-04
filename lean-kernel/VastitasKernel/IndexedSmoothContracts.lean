import VastitasKernel.Indexed
import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Validity contracts of the closed smooth primitive bindings (Stage 3).

A smooth family `Smooth(X, Y)` is sealed: its two indices are declared smooth
objects (`canonical`), and its runtime value is a `SmoothRuntime.Program`. A
declared smooth map is checked against the dimensions of its objects. The
primitives build programs (`compose`), compare their denotations (`same`),
collapse a program to one map (`composite`) and build rational points from
runtime integers (`int_point`). None of them depends on a base chain, a
presented algebra or a descriptor capability. -/
namespace VastitasKernel.Indexed

/-- The family is declared with the sealed `smooth` representation. -/
def isSmoothFamily (env : Environment) (family : DeclId) : Bool :=
  match lookup env family with
  | some (.family contract) => contract.representation == .smooth
  | _ => false

/-- The dimensions of the two declared smooth objects of an application. -/
def smoothEndpoints? (env : Environment) (application : Application) : Option (Nat × Nat) :=
  match application.indices with
  | [.object (.global source), .object (.global target)] =>
    match smoothDimension? env source, smoothDimension? env target with
    | some n, some m => some (n, m)
    | _, _ => none
  | _ => none

/-- A declared smooth map `X → Y`: the application is a valid smooth family
application and the map is a well-formed map `ℝⁿ → ℝᵐ` with canonical images
and no relations. -/
def smoothConstantValid (env : Environment) (application : Application) (map : AlgebraRuntime.Map) : Bool :=
  isSmoothFamily env application.family && validApplication env application &&
  match smoothEndpoints? env application with
  | some (n, m) => SmoothRuntime.wellFormed n m map
  | none => false

/-- The dimension of a declared smooth object, and `0` for anything else. -/
def smoothArity (env : Environment) (id : DeclId) : Nat := (smoothDimension? env id).getD 0

/-- A rational point `point → object` from runtime integers: `object` is a
smooth object and `point` is a 0-dimensional smooth object. -/
def smoothIntPointValid (env : Environment) (family object point : DeclId) : Bool :=
  isSmoothFamily env family && (smoothDimension? env object).isSome && smoothDimension? env point == some 0 &&
    validApplication env ⟨family, [.object (.global point), .object (.global object)]⟩

end VastitasKernel.Indexed
