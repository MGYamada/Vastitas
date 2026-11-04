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

/-! ## Fibers and tapes

A fiber family `Tangent(X)` or `Cotangent(X)` is sealed: its one index is a
declared smooth object, and its runtime value is a vector or covector at a
point of `X`, or the failure value. A tape family `Tape(X, Y)` is sealed in the
same way; only `linearize` builds a tape. The contracts below name the
families of each operand, so the variance of every fiber operand is fixed by
the binding: a `Tangent` where a `Cotangent` is required fails the operand
association. Points are smooth maps `P → X` from a 0-dimensional object `P`;
the association checks `P`. No contract consults a metric, a base chain or a
descriptor capability. -/

/-- The variance of a family declared with the sealed `fiber` representation. -/
def fiberVariance? (env : Environment) (family : DeclId) : Option Variance :=
  match lookup env family with
  | some (.family contract) => match contract.representation with
    | .fiber variance => some variance
    | _ => none
  | _ => none

/-- The family is declared with the sealed `tape` representation. -/
def isTapeFamily (env : Environment) (family : DeclId) : Bool :=
  match lookup env family with
  | some (.family contract) => contract.representation == .tape
  | _ => false

/-- `fiber_vector(F, S, X)`: a fiber of the family `F` over the smooth object
`X`, from a point of `X` in the smooth family `S` and `dim X` integers. -/
def fiberVectorValid (env : Environment) (family smooth object : DeclId) : Bool :=
  (fiberVariance? env family).isSome && isSmoothFamily env smooth && (smoothDimension? env object).isSome &&
    validApplication env ⟨family, [.object (.global object)]⟩

/-- `fiber_at(F, S)`: whether a fiber of `F` lies over a point in `S`. -/
def fiberAtValid (env : Environment) (family smooth : DeclId) : Bool :=
  (fiberVariance? env family).isSome && isSmoothFamily env smooth

/-- `fiber_equal(F)`: equality of two fibers of `F` over one object. -/
def fiberEqualValid (env : Environment) (family : DeclId) : Bool :=
  (fiberVariance? env family).isSome

/-- `fiber_component(F, X, c)`: the component of a fiber of `F` over `X` at
the coordinate with index `coordinate`. -/
def fiberComponentValid (env : Environment) (family object : DeclId) (coordinate : Nat) : Bool :=
  (fiberVariance? env family).isSome && decide (coordinate < smoothArity env object) &&
    validApplication env ⟨family, [.object (.global object)]⟩

/-- `fiber_pairing(C, T)`: the metric-free pairing of a covector of `C` with a
vector of `T` over one object. -/
def fiberPairingValid (env : Environment) (cotangent tangent : DeclId) : Bool :=
  fiberVariance? env cotangent == some .cotangent && fiberVariance? env tangent == some .tangent

/-- `cotangent_pullback(S, C, mode)`: the pullback of a covector of `C` along a
map in `S`. -/
def cotangentPullbackValid (env : Environment) (smooth cotangent : DeclId) : Bool :=
  isSmoothFamily env smooth && fiberVariance? env cotangent == some .cotangent

/-- `differential(S, C, L)`: the differential of a function `X → L` in `S`,
where `L` is a 1-dimensional smooth object. -/
def differentialValid (env : Environment) (smooth cotangent line : DeclId) : Bool :=
  isSmoothFamily env smooth && fiberVariance? env cotangent == some .cotangent &&
    smoothDimension? env line == some 1

/-- `linearize(S, T)`: the tape of a map in `S` at a point. -/
def linearizeValid (env : Environment) (smooth tape : DeclId) : Bool :=
  isSmoothFamily env smooth && isTapeFamily env tape

/-- `cotangent_backward(T, C)`: the reverse pass of a tape of `T` on a covector of `C`. -/
def cotangentBackwardValid (env : Environment) (tape cotangent : DeclId) : Bool :=
  isTapeFamily env tape && fiberVariance? env cotangent == some .cotangent

end VastitasKernel.Indexed
