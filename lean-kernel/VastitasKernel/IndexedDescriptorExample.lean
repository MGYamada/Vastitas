import VastitasKernel.IndexedPrimitiveFamilies

set_option autoImplicit false

/-! A primitive outside the registry (#622): its definitions, with no check.

`directionalDerivative` is a hypothetical primitive: the derivative of a
smooth function `f : X → L` at a point `p` of `X` along a tangent vector `v`
at `p`, as the reduced fraction `⟨df_p, v⟩`, which today takes `differential`
and then `fiber_pairing`. It is one `PrimitiveDescriptor` value built from the
data its binding would carry, outside `PrimitiveBinding.contract`: the
registry gains no constructor and no table names it. Its evaluators and its
lowering apply `SmoothRuntime.differential` and `SmoothRuntime.pairing`, which
generated programs already link, so the demo adds no runtime code.

The wire form is a `PrimitiveFamily` value, `directionalDerivativeFamily`,
also outside the registry (`families`). `directional_derivative` takes the
paths of its smooth family, its tangent family and its line, as
`differential` takes `map_family`, `cotangent` and `line`. `buildDescriptor`
makes the descriptor from the resolved arguments of the wire form.

This module holds definitions only, with no `#eval` and no `run_cmd`. The
kernel regression `IndexedDescriptorRegression` runs its checks on them, and
the oracle module `VastitasOracle.IndexedDescriptorDemo` proves their facts.
Both import this module, so the oracle depends on no regression. The
definitions keep the regression's namespace. -/
namespace VastitasKernel.Indexed.DescriptorRegression

/-- `directional_derivative(S, T, L)`: `⟨df_p, v⟩` for a function `f : X → L`
in the smooth family `S`, a point `p` of `X` and a vector `v` of the tangent
family `T` at `p`. `L` is a 1-dimensional smooth object. The validity contract
is written as its two forms with their agreement; a registry entry whose
contract is one executable check writes `PrimitiveDescriptor.ofBool`. -/
def directionalDerivative (smooth tangent line : DeclId) : PrimitiveDescriptor where
  shape :=
    { operands := [.indexed "function" smooth
          [.var "source", .fixed (.global line) "target" "the primitive's declared line"],
        .indexed "point" smooth [.var "source", .var "target"],
        .indexed "vector" tangent [.var "object"]],
      -- The point lies in the function's source, so does the vector, and the
      -- point is from a 0-dimensional object.
      relations := [.sameRef ⟨0, 0⟩ ⟨1, 1⟩, .sameRef ⟨0, 0⟩ ⟨2, 0⟩, .pointDimension ⟨1, 0⟩ 0],
      result := .integerPair }
  validProp env := isSmoothFamily env smooth = true ∧ smoothDimension? env line = some 1 ∧
    fiberVariance? env tangent = some .tangent
  validBool env := isSmoothFamily env smooth && smoothDimension? env line == some 1 &&
    fiberVariance? env tangent == some .tangent
  valid_iff env := by simp [Bool.and_eq_true, and_assoc]
  eval := fun _ values => match values with
    | [.indexed (.smooth function), .indexed (.smooth point), .indexed (.fiber _ vector)] =>
        let (numerator, denominator) :=
          SmoothRuntime.pairing (SmoothRuntime.differential function point) vector
        some (.pairInt numerator denominator)
    | _ => none
  evalRuntime := fun values => match values with
    | [.smooth function, .smooth point, .fiber vector] =>
        let (numerator, denominator) :=
          SmoothRuntime.pairing (SmoothRuntime.differential function point) vector
        some (.pairInt numerator denominator)
    | _ => none
  -- The text of the erased evaluator's expression; it shares no literal.
  render := fun _ args => match args with
    | [function, point, vector] =>
        .ok (Lowering.application (Lowering.smooth "pairing")
          [Lowering.application (Lowering.smooth "differential") [function, point], vector])
    | _ => Lowering.arityMismatch

/-- The descriptor that the resolved arguments of the wire form make, in wire
order: the step `PrimitiveFamily.build` takes for a registry family, with the
descriptor in place of a binding. -/
def buildDescriptor : List ResolvedArgument → Except String PrimitiveDescriptor
  | [.declaration smooth, .declaration tangent, .declaration line] => pure (directionalDerivative smooth tangent line)
  | _ => throw "the arguments of `directional_derivative` do not match its wire fields"

/-- The wire form of the demo, outside `families`: protocol 9 only, three
paths. `build` rejects every argument list, because `PrimitiveBinding` has no
constructor for the demo; it reports a list that `buildDescriptor` rejects
as a registry family does. -/
def directionalDerivativeFamily : PrimitiveFamily where
  op := "directional_derivative"
  algebraic := true
  fields := [⟨"map_family", .path⟩, ⟨"tangent", .path⟩, ⟨"line", .path⟩]
  build arguments := do
    let _ ← buildDescriptor arguments
    throw "`directional_derivative` has no `PrimitiveBinding` constructor"

end VastitasKernel.Indexed.DescriptorRegression
