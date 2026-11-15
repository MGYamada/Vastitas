import VastitasKernel.IndexedSpectralContracts
import VastitasKernel.IndexedPrimitiveDescriptors

set_option autoImplicit false

/-! The registry entries of the spectral bindings (Stage 5, #806).

`PrimitiveBinding.contract` (`IndexedPrimitiveRegistry`) takes the entry of
each spectral binding from here, one definition per constructor, named as the
constructor and built from the binding's own data. Each entry is a `simp`
lemma, so that the proofs that case on every binding see the entry through
`PrimitiveBinding.contract`.

The contracts are those of `IndexedSpectralContracts`.

- A spectral invariant is an ordinary declared smooth map: its entry is the
  entry of `smoothConstant` with the contract `spectralInvariantValid`. It
  evaluates with no operands to its map as one program node, shares the map
  (`map_k`), and states the derivative rule `morphism map`, so a reverse pass
  pulls a covector back along it by the Jacobian table of its map, as along
  any declared map.
- The observations take a point `p : Smooth<Pt, X>` of the object `X` of
  their spectrum or branch (`Relation.pointDimension`), and the branch
  observations a value `t : Smooth<Pt, Line>` from the same object `Pt`
  (`Relation.sameRef`), into the binding's declared line. `annihilates`,
  `on_branch` and the projector's off-branch failure are run-time values, not
  rejections: no observation computes or orders eigenvalues, and none checks
  an identity at run time. `branch_differential` returns a covector of its
  cotangent family over `X`.

The evaluators read the embedded data only, never the environment, and both
apply the operations of `SpectralRuntime` that generated programs link: the
logical evaluator to the operand values of the Core semantics, the erased one
to their runtime structures. The lowering names the polynomials and matrices
that a call reads as literals that a generated module declares once
(`SharedLiteral.poly`, `SharedLiteral.rows`): the endomorphism's rows and an
element for the module action, and `g`, `χ` and the adjugate for a branch.
The observations state the derivative rule `none`: the eigenvalue of a branch
is an operand, not a `Smooth` value, so no reverse pass opens them. -/
namespace VastitasKernel.Indexed.SpectralRegistry
open VastitasKernel.Indexed.Lowering (application spectral renderMap renderPolynomial renderRows arityMismatch)

/-- A point of the object `object` in the smooth family `smooth`: a smooth
map from a 0-dimensional object to `object`. -/
private abbrev pointOperand (smooth object : DeclId) (reason : String) : Operand :=
  .indexed "point" smooth [.var "source", .fixed (.global object) "target" reason]

/-- A value in the line `line` from the same object as the point. -/
private abbrev valueOperand (smooth line : DeclId) : Operand :=
  .indexed "value" smooth [.var "source", .fixed (.global line) "target" "the primitive's declared line"]

/-- The relations of a point and a value: one 0-dimensional source. -/
private abbrev branchRelations : List Relation := [.sameRef ⟨0, 0⟩ ⟨1, 0⟩, .pointDimension ⟨0, 0⟩ 0]

/-- The entry of `spectralInvariant`: the declared smooth map `map` of type
`application`, `tr(Hᵏ)` or a coefficient of `χ`. -/
@[simp] def spectralInvariant (smoothType : Application) (map : AlgebraRuntime.Map) (invariant : SpectralInvariant) :
    PrimitiveDescriptor :=
  .ofBool { operands := [], result := .constant smoothType }
    (fun env => spectralInvariantValid env smoothType map invariant)
    (fun _ values => match values with
      | [] => some (.indexed (.smooth (.primitive map)))
      | _ => none)
    (fun values => match values with
      | [] => some (.smooth (.primitive map))
      | _ => none)
    (fun ctx args => match args with
      | [] => .ok (application (Lowering.smooth "Program.primitive") [renderMap ctx map])
      | _ => arityMismatch)
    (.morphism map)
    (literals := [.map map])

/-- The entry of `annihilates`: whether `element(H(p)) = 0` at a point `p` of
the spectrum's object. -/
@[simp] def annihilates (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly) :
    PrimitiveDescriptor :=
  .ofBool
    { operands := [pointOperand smooth spectrum.object "the spectrum's object"],
      relations := [.pointDimension ⟨0, 0⟩ 0], result := .boolean }
    (fun env => annihilatesValid env smooth spectrum element)
    (fun _ values => match values with
      | [.indexed (.smooth point)] =>
        some (.boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element point))
      | _ => none)
    (fun values => match values with
      | [.smooth point] => some (.boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element point))
      | _ => none)
    (fun ctx args => match args with
      | [point] =>
        .ok (application (spectral "annihilates")
          [renderRows ctx spectrum.endomorphism.rows, renderPolynomial ctx element, point])
      | _ => arityMismatch)
    .none
    (literals := [.rows spectrum.endomorphism.rows, .poly element])

/-- The entry of `actionEntry`: the entry in row `row` and column `column` of
`element(H(p))` at a point `p` of the spectrum's object. -/
@[simp] def actionEntry (smooth : DeclId) (spectrum : SpectrumRef) (element : AlgebraRuntime.Poly)
    (row column : Nat) : PrimitiveDescriptor :=
  .ofBool
    { operands := [pointOperand smooth spectrum.object "the spectrum's object"],
      relations := [.pointDimension ⟨0, 0⟩ 0], result := .integerPair }
    (fun env => actionEntryValid env smooth spectrum element row column)
    (fun _ values => match values with
      | [.indexed (.smooth point)] =>
        let (numerator, denominator) := SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun values => match values with
      | [.smooth point] =>
        let (numerator, denominator) := SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun ctx args => match args with
      | [point] =>
        .ok (application (spectral "actionEntry")
          [renderRows ctx spectrum.endomorphism.rows, renderPolynomial ctx element, point, toString row,
            toString column])
      | _ => arityMismatch)
    .none
    (literals := [.rows spectrum.endomorphism.rows, .poly element])

/-- The entry of `onBranch`: whether a point `p` and a value `t` lie on the
branch: `g(p) ≠ 0` and `χ(p, t) = 0`. -/
@[simp] def onBranch (smooth line : DeclId) (branch : BranchRef) : PrimitiveDescriptor :=
  .ofBool
    { operands := [pointOperand smooth branch.object "the branch's object", valueOperand smooth line],
      relations := branchRelations, result := .boolean }
    (fun env => onBranchValid env smooth line branch)
    (fun _ values => match values with
      | [.indexed (.smooth point), .indexed (.smooth value)] =>
        some (.boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic point value))
      | _ => none)
    (fun values => match values with
      | [.smooth point, .smooth value] =>
        some (.boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic point value))
      | _ => none)
    (fun ctx args => match args with
      | [point, value] =>
        .ok (application (spectral "onBranch")
          [renderPolynomial ctx branch.localize, renderPolynomial ctx branch.spectrum.characteristic, point, value])
      | _ => arityMismatch)
    .none
    (literals := [.poly branch.localize, .poly branch.spectrum.characteristic])

/-- The entry of `branchDifferential`: the differential at `p` of the
eigenvalue of the branch through `(p, t)`, a covector over the branch's
object, or the failure value off the branch. -/
@[simp] def branchDifferential (smooth cotangent line : DeclId) (branch : BranchRef) : PrimitiveDescriptor :=
  .ofBool
    { operands := [pointOperand smooth branch.object "the branch's object", valueOperand smooth line],
      relations := branchRelations, result := .indexed cotangent [.fixed (.global branch.object)] }
    (fun env => branchDifferentialValid env smooth cotangent line branch)
    (fun _ values => match values with
      | [.indexed (.smooth point), .indexed (.smooth value)] =>
        some (.indexed (.fiber .cotangent
          (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic point value)))
      | _ => none)
    (fun values => match values with
      | [.smooth point, .smooth value] =>
        some (.fiber (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic point value))
      | _ => none)
    (fun ctx args => match args with
      | [point, value] =>
        .ok (application (spectral "branchDifferential")
          [renderPolynomial ctx branch.localize, renderPolynomial ctx branch.spectrum.characteristic, point, value])
      | _ => arityMismatch)
    .none
    (literals := [.poly branch.localize, .poly branch.spectrum.characteristic])

/-- The entry of `branchProjector`: the entry in row `row` and column
`column` of the eigenprojector `adj(tI − H(p)) / χ′(p, t)` of the branch at
`(p, t)`, or `(0, 0)` off the branch. -/
@[simp] def branchProjector (smooth line : DeclId) (branch : BranchRef) (row column : Nat) : PrimitiveDescriptor :=
  .ofBool
    { operands := [pointOperand smooth branch.object "the branch's object", valueOperand smooth line],
      relations := branchRelations, result := .integerPair }
    (fun env => branchProjectorValid env smooth line branch row column)
    (fun _ values => match values with
      | [.indexed (.smooth point), .indexed (.smooth value)] =>
        let (numerator, denominator) := SpectralRuntime.projectorEntry branch.localize
          branch.spectrum.characteristic branch.spectrum.adjugate point value row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun values => match values with
      | [.smooth point, .smooth value] =>
        let (numerator, denominator) := SpectralRuntime.projectorEntry branch.localize
          branch.spectrum.characteristic branch.spectrum.adjugate point value row column
        some (.pairInt numerator denominator)
      | _ => none)
    (fun ctx args => match args with
      | [point, value] =>
        .ok (application (spectral "projectorEntry")
          [renderPolynomial ctx branch.localize, renderPolynomial ctx branch.spectrum.characteristic,
            renderRows ctx branch.spectrum.adjugate, point, value, toString row, toString column])
      | _ => arityMismatch)
    .none
    (literals := [.poly branch.localize, .poly branch.spectrum.characteristic, .rows branch.spectrum.adjugate])

end VastitasKernel.Indexed.SpectralRegistry
