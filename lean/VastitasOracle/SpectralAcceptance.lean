import VastitasOracle.FrameCore
import VastitasOracle.SmoothJacobian
import VastitasOracle.SpectralCore
import VastitasOracle.SpectralDeclarations
import VastitasOracle.SpectralRuntime
import VastitasOracle.SpectralWeakening

set_option autoImplicit false

/-! **Stage 5 acceptance in the oracle** (#806): one corollary per tracker
condition that the oracle carries, about accepted declarations, bindings and
Core. Mathlib-free.

*Accepted* means, as in `FrameAcceptance`: the environment is valid
(`Environment.Valid`), a binding is valid in it, and a Core term type-checks
(`Typing.HasType`) with leaf operands that evaluate to values of their
checked types. A binding embeds its endomorphism, spectrum or branch as its
declaration (`SpectralCore.DeclaredBranch` and the others), and the valid
environment makes the embedded data pass the kernel's checks
(`DeclaredBranch.checked`). Each row composes a Core-level or declaration-
level theorem with a runtime or algebra theorem.

| Row | Theorem | Composes |
| --- | --- | --- |
| C1 fields and modules | `c1_fields_and_modules` | `SpectralDeclarations.checkFreeModule_sound`, `endomorphism_sound`, `spectrum_sound` |
| C2 spectral pair | `c2_spectral_pair` | `SpectralDeclarations.spectrum_sound`, `SpectralValid.characteristic_eq_det`, `adjugate_eq`, `adjugateTrace_at`, `jacobi_at`; `SpectralRuntime.annihilates_char` |
| C3 scalar against Jordan | `c3_scalar_jordan` | `SpectralRuntime.Examples.scalar_jordan_regression` |
| C4 invariants as smooth maps | `c4_invariants`, `c4_stage5_invariants` | `SpectralCore.spectralInvariant_tracePower_at`, `spectralInvariant_charCoefficient_at`, `spectralInvariant_valid_sound`; the images by `decide +kernel` |
| C5 roadmap gradient | `s4_trace_square_gradient`, `c5_roadmap_gradient` | `SpectralCore.spectralInvariant_valid_sound`, `DeclaredEndo.arity`; `SpectralDeclarations.Examples.trace_square_ok`; `SmoothReverse.core_differential` |
| C6 reverse Core of an invariant | `c6_reverse_core_invariant` | `SpectralCore.compiled_invariant_step`, `spectralInvariant_tracePower_at`; `SmoothJacobian.spectralInvariant_reverse` |
| C8 gap certificate | `c8_gap_certificate` | `SpectralDeclarations.branch_sound`, `SpectralValid.unit_at`, `Examples.unit_gap_no_witness`, `origin_off_chart`; `jordan_no_witness`, `perturbed_witness_rejected` |
| C9 branch points and ⊥ | `c9_branch_points` | `SpectralRuntime.branch_some_iff`, `off_chart_bottom`; the points by `decide +kernel` |
| C10 branch derivative | `c10_branch_derivative`, `Stage5.branch_differentials` | `SpectralCore.core_spectral_branch_differential`, `DeclaredBranch.checked`; `SpectralRuntime.branchDifferential_implicit`, `branchDifferential_hellmann_feynman` |
| C11 eigenprojector | `c11_eigenprojector`, `Stage5.projectors` | `SpectralCore.core_spectral_branch_projector`, `DeclaredBranch.checked`; `SpectralRuntime.projector_idempotent`, `projector_trace_one`, `projector_eigen`, `projector_commutes` |
| C12 degenerate cases | `c12_degenerate` | `SpectralRuntime.Examples.zero_accepted`; `Examples.origin_off_chart`; the rank-1 and rank-4 cases by `decide +kernel` |
| C13 weakening | `c13_weakening` | `SpectralWeakening.spectral_weakening_binding`, `spectral_weakening_entry`, `stage4_bindings_spectral_free`, `spectral_bindings_metric_free`, `spectral_bindings_frame_free`; `SpectralCore.spectral_bindings_environment_free` |

**Proved for all inputs, decided per input.** Every statement that
quantifies over environments, bindings, Core terms, points or rings is proved
for all of them. The Stage 5 values (`H = rows((x, y), (y, −x))`, its
certificate and gap certificate, the points `((3, 4), ±5)` and `((1, 0), ±1)`,
the projectors and the differentials at them, and the rank-1, rank-4 and
Jordan examples) are decided by `decide +kernel`; the gradients of `tr(H²)`,
`c0` and `tr(H)` are then proved at every rational point.

**Not stated here.** C7 (Daleckii–Krein) is a bridge statement; C14–C20 are
wire, fixture, limit, library, native, CI and review conditions, which tests
and scripts carry. The `.stderr` texts of the rejections, and that the
elaboration produces these declarations from the example source, are tested.
That `ringDet` is the determinant and the branch exists as a function (the
implicit function theorem) are bridge statements or planned. -/
namespace VastitasOracle.SpectralAcceptance

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.AlgebraRuntime (Poly Map)
open VastitasKernel.SmoothRuntime (Program Fiber coordinates differential sharp cot intPoint matVec dot evalAt
  partialDerivative monomialValue npow)
open VastitasKernel.SpectralRuntime (onBranch slopeAt branchPoint branchDifferential projectorMatrix projectorEntry
  annihilates)
open VastitasOracle.SmoothCalculus (RatHom evalIn)
open VastitasOracle.SpectralAlgebra (MatrixArity ringTrace ringPow evalMatrix ringSum ringDet ringCharMatrix
  ringMatMul ringScalar squareOf_spec)
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid polyEntry)
open VastitasOracle.SpectralCore (DeclaredEndo DeclaredSpectrum DeclaredBranch)
open VastitasOracle.SpectralRuntime (scaleMatrix projectorAt)

universe u

/-! ## C1 and C2: declarations -/

/-- **C1 Fields and modules.** In a valid environment a free module has
`1 ≤ n ≤ spectralRank` distinct basis names over a declared smooth object; an
endomorphism has `n × n` canonical polynomial rows in the coordinates of its
object, for the rank `n` of its free module on the same object, symmetric when
declared so; and a spectrum's fiber name is a new identifier: no coordinate
of its object and no basis vector of the free module of its endomorphism. -/
theorem c1_fields_and_modules {env : Indexed.Environment} (valid : env.Valid) :
    (∀ {id family object : DeclId} {basis : List String},
      lookup env id = some (.freeModule family object basis) →
        (smoothDimension? env object).isSome = true ∧ 1 ≤ basis.length ∧ basis.length ≤ Limits.spectralRank ∧
          basis.Nodup) ∧
    (∀ {id family object module : DeclId} {rows : PolyMatrix} {symmetric : Bool},
      lookup env id = some (.endomorphism family object module rows symmetric) →
        ∃ m basis, smoothDimension? env object = some m ∧
          (∃ moduleFamily, freeModuleData? env module = some (moduleFamily, object, basis)) ∧
          rows.length = basis.length ∧ rows.length ≤ Limits.spectralRank ∧
          SpectralDeclarations.squareOf rows.length m rows = true ∧
          (symmetric = true → ∀ i j, polyEntry rows i j = polyEntry rows j i)) ∧
    (∀ {id family object endomorphism : DeclId} {fiber : String} {certificate : SpectralCertificate},
      lookup env id = some (.spectrum family object endomorphism fiber certificate) →
        ∃ coordinates basis, smoothCoordinates? env object = some coordinates ∧
          (∃ endomorphismFamily module rows symmetric moduleFamily moduleObject,
            endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, symmetric) ∧
            freeModuleData? env module = some (moduleFamily, moduleObject, basis)) ∧
          SpectralDeclarations.isIdentifier fiber = true ∧ fiber ∉ coordinates ∧ fiber ∉ basis) := by
  refine ⟨fun found => ?_, fun found => ?_, fun found => ?_⟩
  · obtain ⟨-, -, hobject, hbasis⟩ :=
      VastitasOracle.SpectralDeclarations.checkFreeModule_sound
        (VastitasOracle.SpectralDeclarations.valid_of_lookup valid found)
    exact ⟨hobject, hbasis⟩
  · obtain ⟨-, -, implementation, coordinates, moduleFamily, basis, hobject, hmodule, hrank, hsquare, hsym⟩ :=
      VastitasOracle.SpectralDeclarations.endomorphism_sound valid found
    have hlength := (squareOf_spec hsquare).1
    rw [← hlength] at hrank hsquare
    exact ⟨coordinates.length, basis, SpectralCore.smoothDimension_of_lookup hobject, ⟨moduleFamily, hmodule⟩,
      hlength, hrank, hsquare, hsym⟩
  · obtain ⟨-, -, implementation, coordinates, hobject, hidentifier, hfiber, endomorphismFamily, module, rows,
      symmetric, hend, ⟨moduleFamily, moduleObject, basis, hmodule, hbasis⟩, -⟩ :=
      VastitasOracle.SpectralDeclarations.spectrum_sound valid found
    exact ⟨coordinates, basis, by simp [smoothCoordinates?, hobject],
      ⟨endomorphismFamily, module, rows, symmetric, moduleFamily, moduleObject, hend, hmodule⟩, hidentifier, hfiber,
      hbasis⟩

/-- **C2 The spectral pair.** In a valid environment the certificate of a
declared spectrum, which the kernel computes and checks and never reads from
the wire, is valid for the rows `H` of its endomorphism, and at every point
`(x, t)` of every ring that receives `ℚ`: `χ(x, t) = det(tI − H(x))` by the
cofactor recursion, `(tI − H(x))·adj(x, t) = χ(x, t)·I`, `tr adj = χ′` and
`∂ᵢχ + tr(adj·∂ᵢH) = 0`; and `χ` annihilates every fiber (Cayley–Hamilton). -/
theorem c2_spectral_pair {R : Type u} [Lean.Grind.CommRing R] {env : Indexed.Environment} (valid : env.Valid)
    {id family object endomorphism : DeclId} {fiber : String} {certificate : SpectralCertificate}
    (found : lookup env id = some (.spectrum family object endomorphism fiber certificate)) :
    ∃ m rows, smoothDimension? env object = some m ∧
      (∃ endomorphismFamily module symmetric,
        endomorphismData? env endomorphism = some (endomorphismFamily, object, module, rows, symmetric)) ∧
      SpectralValid m rows certificate ∧
      (∀ (ι : RatHom R) (x : List R), x.length = m → ∀ t : R,
        evalIn ι certificate.characteristic (x ++ [t]) = ringDet rows.length (ringCharMatrix t (evalMatrix ι rows x)) ∧
        ringMatMul rows.length (ringCharMatrix t (evalMatrix ι rows x))
            (evalMatrix ι certificate.adjugate (x ++ [t])) =
          ringScalar rows.length (evalIn ι certificate.characteristic (x ++ [t]))) ∧
      (∀ (ι : RatHom R) (z : List R), ringTrace (evalMatrix ι certificate.adjugate z) =
        evalIn ι (partialDerivative m certificate.characteristic) z) ∧
      (∀ (ι : RatHom R) (z : List R) (i : Nat), i < m →
        evalIn ι (partialDerivative i certificate.characteristic) z +
          ringTrace (ringMatMul rows.length (evalMatrix ι certificate.adjugate z)
            (evalMatrix ι (SpectralDeclarations.derivativeMatrix i rows) z)) = 0) ∧
      (∀ point, annihilates rows certificate.characteristic point = true) := by
  obtain ⟨-, -, implementation, coordinates, hobject, -, -, endomorphismFamily, module, rows, symmetric, hend, -,
      hv⟩ :=
    VastitasOracle.SpectralDeclarations.spectrum_sound valid found
  exact ⟨coordinates.length, rows, SpectralCore.smoothDimension_of_lookup hobject,
    ⟨endomorphismFamily, module, symmetric, hend⟩, hv,
    fun ι x hx t => ⟨hv.characteristic_eq_det ι hx t, hv.adjugate_eq ι hx t⟩,
    fun ι z => hv.adjugateTrace_at ι z, fun ι z i hi => hv.jacobi_at ι z hi,
    VastitasOracle.SpectralRuntime.annihilates_char hv⟩

/-! ## C3: the scalar matrix against the Jordan block -/

/-- **C3 Scalar against Jordan.** `2I` and `J`, and `0` and `N`, have accepted
certificates with the same `χ` and trace powers but different module actions;
`χ` annihilates both and is never reduced. -/
theorem c3_scalar_jordan :
    let scalar := VastitasOracle.SpectralRuntime.Examples.scalar
    let jordan := VastitasOracle.SpectralRuntime.Examples.jordan
    let zero := VastitasOracle.SpectralRuntime.Examples.zero
    let nilpotent := VastitasOracle.SpectralRuntime.Examples.nilpotent
    let certificateOf := VastitasOracle.SpectralRuntime.Examples.certificateOf
    let origin := VastitasOracle.SpectralRuntime.Examples.origin
    let tMinusTwo := VastitasOracle.SpectralRuntime.Examples.tMinusTwo
    let tVar := VastitasOracle.SpectralRuntime.Examples.tVar
    SpectralValid 0 scalar (certificateOf scalar) ∧ SpectralValid 0 jordan (certificateOf jordan) ∧
      (certificateOf scalar).characteristic = (certificateOf jordan).characteristic ∧
      (∀ k, (SpectralDeclarations.tracePowerImage 0 scalar k).toOption =
        (SpectralDeclarations.tracePowerImage 0 jordan k).toOption) ∧
      (∀ point, annihilates scalar (certificateOf scalar).characteristic point = true) ∧
      (∀ point, annihilates jordan (certificateOf jordan).characteristic point = true) ∧
      (certificateOf scalar).characteristic ≠ tMinusTwo ∧
      annihilates scalar tMinusTwo origin = true ∧ annihilates jordan tMinusTwo origin = false ∧
      VastitasKernel.SpectralRuntime.actionEntry scalar tMinusTwo origin 0 1 = (0, 1) ∧
      VastitasKernel.SpectralRuntime.actionEntry jordan tMinusTwo origin 0 1 = (1, 1) ∧
      SpectralValid 0 zero (certificateOf zero) ∧ SpectralValid 0 nilpotent (certificateOf nilpotent) ∧
      (certificateOf zero).characteristic = (certificateOf nilpotent).characteristic ∧
      (∀ k, (SpectralDeclarations.tracePowerImage 0 zero k).toOption =
        (SpectralDeclarations.tracePowerImage 0 nilpotent k).toOption) ∧
      annihilates zero tVar origin = true ∧ annihilates nilpotent tVar origin = false :=
  VastitasOracle.SpectralRuntime.Examples.scalar_jordan_regression

/-! ## The differential of a declared map at a rational point -/

theorem differential_primitive {map : Map} (h : map.images.length = 1) (point : Program) :
    differential (.primitive map) point = some ⟨coordinates point, cot map (coordinates point) [1]⟩ := by
  rw [VastitasOracle.SmoothRuntime.differential_eq_pullback, VastitasOracle.SmoothRuntime.pullback_spec,
    ite_eq_left ⟨rfl, by simp [VastitasKernel.SmoothRuntime.Program.outputArity, h]⟩]
  rfl

theorem cot_two {map : Map} {image : Poly} (harity : map.arity = 2) (himages : map.images = [image])
    (x : List Rat) :
    cot map x [1] = [evalAt (partialDerivative 0 image) x, evalAt (partialDerivative 1 image) x] := by
  show (List.range map.arity).map
      (fun j => dot [1] (map.images.map fun image => evalAt (partialDerivative j image) x)) = _
  rw [harity, himages]
  show [1 * evalAt (partialDerivative 0 image) x + 0, 1 * evalAt (partialDerivative 1 image) x + 0] = _
  simp only [Rat.one_mul, Rat.add_zero]

/-- The differential of a map `ℝ² → ℝ` with one image, at a point with the
coordinates `(a, b)`: its two partial derivatives there, over that point. -/
theorem differential_two {map : Map} {image : Poly} (harity : map.arity = 2) (himages : map.images = [image])
    {point : Program} {a b : Rat} (hp : coordinates point = [a, b]) :
    differential (.primitive map) point =
      some ⟨[a, b], [evalAt (partialDerivative 0 image) [a, b], evalAt (partialDerivative 1 image) [a, b]]⟩ := by
  rw [differential_primitive (by rw [himages]; rfl) point, cot_two harity himages, hp]

theorem npow_one' (v : Rat) : npow v 1 = v := by
  show npow v 0 * v = v
  rw [show npow v 0 = 1 from rfl, Rat.one_mul]

theorem evalAt_first (c a b : Rat) : evalAt [⟨[1, 0], c⟩] [a, b] = c * a := by
  show c * (npow a 1 * (npow b 0 * 1)) + 0 = c * a
  rw [npow_one', show npow b 0 = 1 from rfl]
  grind

theorem evalAt_second (c a b : Rat) : evalAt [⟨[0, 1], c⟩] [a, b] = c * b := by
  show c * (npow a 0 * (npow b 1 * 1)) + 0 = c * b
  rw [npow_one', show npow a 0 = 1 from rfl]
  grind

/-- The Gram inverse of the dimensionless Euclidean chart: the identity. -/
def euclidean : VastitasKernel.SmoothRuntime.Matrix := [[1, 0], [0, 1]]

theorem sharp_euclidean (point : List Rat) (a b : Rat) :
    sharp euclidean (some ⟨point, [a, b]⟩) = some ⟨point, [a, b]⟩ := by
  show some (⟨point, [1 * a + (0 * b + 0), 0 * a + (1 * b + 0)]⟩ : Fiber) = some (⟨point, [a, b]⟩ : Fiber)
  simp only [Rat.one_mul, Rat.zero_mul, Rat.add_zero, Rat.zero_add]

/-! ## C4 and C5: invariants and the roadmap gradient -/

/-- **C4 Invariants as smooth maps (general).** In a valid environment an
accepted `trace_power(H, k)` is a declared smooth map `X → Line` with the one
image `tr(H(x)ᵏ)` of the declared field at every point of every ring, and an
accepted `char_coefficient(S, i)` the coefficient of `tⁱ` in the declared
`χ(x, t) = Σₖ χₖ(x) tᵏ`. So `differential`, `pullback` and `sharp` apply to
them as to any declared map. -/
theorem c4_invariants {R : Type u} [Lean.Grind.CommRing R] {env : Indexed.Environment} (envValid : env.Valid) :
    (∀ {application : Application} {map : Map} {endo : EndoRef} {power : Nat},
      spectralInvariantValid env application map (.tracePower endo power) = true →
        DeclaredEndo env endo ∧ ∃ m image, smoothDimension? env endo.object = some m ∧ map.arity = m ∧
          map.images = [image] ∧ 1 ≤ power ∧ power ≤ Limits.spectralPower ∧
          ∀ (ι : RatHom R) (x : List R),
            evalIn ι image x = ringTrace (ringPow endo.rows.length (evalMatrix ι endo.rows x) power)) ∧
    (∀ {application : Application} {map : Map} {spectrum : SpectrumRef} {index : Nat},
      spectralInvariantValid env application map (.charCoefficient spectrum index) = true →
        DeclaredSpectrum env spectrum ∧ ∃ m image, smoothDimension? env spectrum.object = some m ∧ map.arity = m ∧
          map.images = [image] ∧ index ≤ spectrum.rank ∧
          image = SpectralDeclarations.charCoefficient spectrum.characteristic index ∧
          ∀ (ι : RatHom R) (x : List R), x.length = m → ∀ t : R,
            evalIn ι spectrum.characteristic (x ++ [t]) =
              ringSum (VastitasKernel.SpectralRuntime.degT spectrum.characteristic + 1)
                (fun k => evalIn ι (SpectralDeclarations.charCoefficient spectrum.characteristic k) x * t ^ k)) :=
  ⟨fun valid => SpectralCore.spectralInvariant_tracePower_at envValid valid,
    fun valid => SpectralCore.spectralInvariant_charCoefficient_at envValid valid⟩

namespace Stage5

open VastitasOracle.SpectralDeclarations.Examples

theorem trace_one_toOption : (SpectralDeclarations.tracePowerImage 2 rows 1).toOption = some [] := by
  decide +kernel

/-- `tr(H) = 0`. -/
theorem trace_one : SpectralDeclarations.tracePowerImage 2 rows 1 = .ok [] :=
  SpectralCore.toOption_eq_some trace_one_toOption

theorem coefficient_zero_toOption :
    (SpectralDeclarations.charCoefficientImage 2 characteristic 0).toOption = some (Poly.scale (-1) localize) := by
  decide +kernel

/-- `c0 = −x² − y²`, the coefficient of `t⁰` in `χ = t² − x² − y²`. -/
theorem coefficient_zero :
    SpectralDeclarations.charCoefficientImage 2 characteristic 0 = .ok (Poly.scale (-1) localize) :=
  SpectralCore.toOption_eq_some coefficient_zero_toOption

/-- **Newton's identity** for `n = 2`: `c0 = −½ tr(H²)`. -/
theorem newton : Poly.scale (-1) localize = Poly.scale (-1 / 2) (Poly.scale 2 localize) := by
  decide +kernel

theorem partial_trace_square :
    partialDerivative 0 (Poly.scale 2 localize) = [⟨[1, 0], 4⟩] ∧
      partialDerivative 1 (Poly.scale 2 localize) = [⟨[0, 1], 4⟩] := by
  decide +kernel

theorem partial_coefficient_zero :
    partialDerivative 0 (Poly.scale (-1) localize) = [⟨[1, 0], -2⟩] ∧
      partialDerivative 1 (Poly.scale (-1) localize) = [⟨[0, 1], -2⟩] := by
  decide +kernel

theorem x_mem : (⟨[1, 0], 1⟩ : VastitasKernel.AlgebraRuntime.Term) ∈ x := by decide +kernel

/-- A declared endomorphism with the Stage 5 rows lies on a 2-dimensional
object: its rows have arity `2`. -/
theorem stage5_dimension {env : Indexed.Environment} (envValid : env.Valid) {endo : EndoRef}
    (declared : DeclaredEndo env endo) (hrows : endo.rows = rows) {m : Nat}
    (hm : smoothDimension? env endo.object = some m) : m = 2 := by
  have harity := declared.arity envValid hm
  rw [hrows] at harity
  have h := harity [x, y] (by simp [rows]) x (by simp) ⟨[1, 0], 1⟩ x_mem
  simp only [List.length_cons, List.length_nil] at h
  omega

end Stage5

/-- **C5 The roadmap gradient.** For the Stage 5 field
`H = rows((x, y), (y, −x))` an accepted `trace_power(H, 2)` has the one image
`2x² + 2y²`, and at every rational point `p = (a, b)` its differential, and
its Euclidean gradient through `sharp` with the identity Gram inverse of the
dimensionless chart, is `(4a, 4b)`. -/
theorem s4_trace_square_gradient {env : Indexed.Environment} (envValid : env.Valid) {application : Application}
    {map : Map} {endo : EndoRef} (hrows : endo.rows = SpectralDeclarations.Examples.rows)
    (valid : spectralInvariantValid env application map (.tracePower endo 2) = true) :
    map.arity = 2 ∧ map.images = [Poly.scale 2 SpectralDeclarations.Examples.localize] ∧
      ∀ (point : Program) (a b : Rat), coordinates point = [a, b] →
        differential (.primitive map) point = some ⟨[a, b], [4 * a, 4 * b]⟩ ∧
        sharp euclidean (differential (.primitive map) point) = some ⟨[a, b], [4 * a, 4 * b]⟩ := by
  obtain ⟨declared, -, m, -, image, -, hm, -, harity, -, himages, -, hok, -⟩ :=
    SpectralCore.spectralInvariant_valid_sound valid
  have h2 := Stage5.stage5_dimension envValid declared hrows hm
  subst h2
  have himage : image = Poly.scale 2 SpectralDeclarations.Examples.localize := by
    have h : SpectralDeclarations.tracePowerImage 2 endo.rows 2 = .ok image := hok
    rw [hrows, SpectralDeclarations.Examples.trace_square_ok] at h
    cases h
    rfl
  subst himage
  refine ⟨harity, himages, fun point a b hp => ?_⟩
  have hd : differential (.primitive map) point = some ⟨[a, b], [4 * a, 4 * b]⟩ := by
    rw [differential_two harity himages hp, Stage5.partial_trace_square.1, Stage5.partial_trace_square.2,
      evalAt_first, evalAt_second]
  exact ⟨hd, by rw [hd, sharp_euclidean]⟩

/-- **C5 on accepted Core.** An accepted `differential(f, p)` node whose
function operand evaluates to an accepted `trace_power(H, 2)` of the Stage 5
field evaluates, at a point with the coordinates `(a, b)`, to the covector
`(4a, 4b)` over `(a, b)`. -/
theorem c5_roadmap_gradient {module : Module} {functions : Core.Typing.Signatures} {ctx : Core.Typing.Context}
    {world : World} {fuel : Nat} {values : Values} {id : DeclId} {function point : Core.Term} {result : Result}
    {smooth cotangent line : DeclId} {operands : List ValueType} {output : ValueType} {pointValue : Value}
    {application : Application} {map : Map} {endo : EndoRef}
    (envValid : module.declarations.indexed.Valid) (hrows : endo.rows = SpectralDeclarations.Examples.rows)
    (valid : spectralInvariantValid module.declarations.indexed application map (.tracePower endo 2) = true)
    (found : module.declarations.primitive? id = some (.differential smooth cotangent line))
    (input : ([function, point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [function, point] result))
    (functionEval : eval module fuel values function = some (.indexed (.smooth (.primitive map))))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world
      [.indexed (.smooth (.primitive map)), pointValue] operands) :
    ∃ x, pointValue = .indexed (.smooth x) ∧ ∀ a b : Rat, coordinates x = [a, b] →
      eval module (fuel + 1) values (.primitive id [function, point] result) =
        some (.indexed (.fiber .cotangent (some ⟨[a, b], [4 * a, 4 * b]⟩))) := by
  obtain ⟨φ, x, hφ, rfl, evaluated, -, -⟩ :=
    SmoothReverse.core_differential found input outputType accepted functionEval pointEval typed
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at hφ
  subst hφ
  obtain ⟨-, -, gradient⟩ := s4_trace_square_gradient envValid hrows valid
  exact ⟨x, rfl, fun a b hp => by rw [evaluated, (gradient x a b hp).1]⟩

/-- **C4 for the Stage 5 field.** `tr(H²) = 2x² + 2y²` (the image of
`ref2 = pullback(t -> 2*x^2 + 2*y^2)`, so `same_smooth(tr2, ref2)`),
`c0 = −x² − y² = −½ tr(H²)` (Newton's identity) and `tr(H) = 0`; at every
rational point `(a, b)` the differentials are `(4a, 4b)`, `(−2a, −2b)` (so
`grad c0 = −½ grad tr2`) and `(0, 0)`: the zero covector over the point, not
the failure value. -/
theorem c4_stage5_invariants {env : Indexed.Environment} (envValid : env.Valid) :
    SpectralDeclarations.tracePowerImage 2 SpectralDeclarations.Examples.rows 2 =
        .ok (Poly.scale 2 SpectralDeclarations.Examples.localize) ∧
      SpectralDeclarations.charCoefficientImage 2 SpectralDeclarations.Examples.characteristic 0 =
        .ok (Poly.scale (-1) SpectralDeclarations.Examples.localize) ∧
      Poly.scale (-1) SpectralDeclarations.Examples.localize =
        Poly.scale (-1 / 2) (Poly.scale 2 SpectralDeclarations.Examples.localize) ∧
      SpectralDeclarations.tracePowerImage 2 SpectralDeclarations.Examples.rows 1 = .ok [] ∧
      (∀ {application : Application} {map : Map} {spectrum : SpectrumRef},
        spectrum.characteristic = SpectralDeclarations.Examples.characteristic →
        spectrum.endomorphism.rows = SpectralDeclarations.Examples.rows →
        spectralInvariantValid env application map (.charCoefficient spectrum 0) = true →
        ∀ (point : Program) (a b : Rat), coordinates point = [a, b] →
          differential (.primitive map) point = some ⟨[a, b], [-2 * a, -2 * b]⟩) ∧
      (∀ {application : Application} {map : Map} {endo : EndoRef},
        endo.rows = SpectralDeclarations.Examples.rows →
        spectralInvariantValid env application map (.tracePower endo 1) = true →
        ∀ (point : Program) (a b : Rat), coordinates point = [a, b] →
          differential (.primitive map) point = some ⟨[a, b], [0, 0]⟩) := by
  refine ⟨SpectralDeclarations.Examples.trace_square_ok, Stage5.coefficient_zero, Stage5.newton, Stage5.trace_one,
    fun {application map spectrum} hchar hrows valid point a b hp => ?_,
    fun {application map endo} hrows valid point a b hp => ?_⟩
  · obtain ⟨declared, -, m, -, image, -, hm, -, harity, -, himages, -, hok, -⟩ :=
      SpectralCore.spectralInvariant_valid_sound valid
    have hdeclared : DeclaredSpectrum env spectrum := declared
    have h2 := Stage5.stage5_dimension envValid hdeclared.1 hrows hm
    subst h2
    have himage : image = Poly.scale (-1) SpectralDeclarations.Examples.localize := by
      have h : SpectralDeclarations.charCoefficientImage _ _ 0 = .ok image := hok
      have hlength : SpectralDeclarations.Examples.rows.length = 2 := rfl
      rw [hchar, hrows, hlength, Stage5.coefficient_zero] at h
      cases h
      rfl
    subst himage
    rw [differential_two harity himages hp, Stage5.partial_coefficient_zero.1, Stage5.partial_coefficient_zero.2,
      evalAt_first, evalAt_second]
  · obtain ⟨declared, -, m, -, image, -, hm, -, harity, -, himages, -, hok, -⟩ :=
      SpectralCore.spectralInvariant_valid_sound valid
    have h2 := Stage5.stage5_dimension envValid declared hrows hm
    subst h2
    have himage : image = [] := by
      have h : SpectralDeclarations.tracePowerImage 2 endo.rows 1 = .ok image := hok
      rw [hrows, Stage5.trace_one] at h
      cases h
      rfl
    subst himage
    rw [differential_two harity himages hp]
    rfl

/-! ## C6: the reverse Core of an invariant -/

/-- **C6 The reverse Core of an invariant.** A spectral invariant's derivative
rule is `morphism` with its own map (`SmoothJacobian.spectralInvariant_reverse`
is its `registry_reverse_sound` case). So in a compiled module a declared
reverse step along an accepted `trace_power(H, k)` is the Stage 3 binding
`cotangentJacobian` of the invariant's map, whose one image is `tr(H(x)ᵏ)`
of the declared field at every point of every ring: no new reverse rule. -/
theorem c6_reverse_core_invariant {R : Type u} [Lean.Grind.CommRing R] {requireMain : Bool}
    {source : Core.Typing.CheckedModule requireMain} (compiled : Reverse.Compiled source) {entry : Reverse.Entry}
    (member : entry ∈ compiled.entries) {step : Reverse.Step} (stepMember : step ∈ entry.site.steps)
    {morphism : DeclId} {stepApplication : Application} {stepMap : Map}
    (kind : step.kind = .declared morphism stepApplication stepMap) {application : Application} {map : Map}
    {endo : EndoRef} {power : Nat}
    (found : compiled.core.module.declarations.primitive? morphism =
      some (.spectralInvariant application map (.tracePower endo power))) :
    SmoothJacobian.ReverseSound (PrimitiveBinding.spectralInvariant application map (.tracePower endo power)).contract ∧
      stepMap = map ∧
      Reverse.stepBinding entry.site step.kind = .cotangentJacobian entry.site.cotangent stepApplication map ∧
      ∃ m image, smoothDimension? compiled.core.module.declarations.indexed endo.object = some m ∧ map.arity = m ∧
        map.images = [image] ∧
        ∀ (ι : RatHom R) (x : List R),
          evalIn ι image x = ringTrace (ringPow endo.rows.length (evalMatrix ι endo.rows x) power) := by
  have declarationsValid := compiled.core.typed.declarations
  have bindingValid := FrameCore.binding_valid declarationsValid found
  have valid : spectralInvariantValid compiled.core.module.declarations.indexed application map
      (.tracePower endo power) = true := bindingValid
  obtain ⟨hmap, hbinding⟩ := SpectralCore.compiled_invariant_step compiled member stepMember kind found
  obtain ⟨-, m, image, hm, harity, himages, -, -, meaning⟩ :=
    SpectralCore.spectralInvariant_tracePower_at (R := R) declarationsValid.indexed valid
  exact ⟨SmoothJacobian.spectralInvariant_reverse application map _, hmap, hbinding, m, image, hm, harity, himages,
    meaning⟩

/-! ## C8: the gap certificate -/

theorem evalAt_ne_zero_of_canonical_zero {g : Poly} (hc : Poly.canonical 0 g = true) (hne : g ≠ [])
    (x : List Rat) : evalAt g x ≠ 0 := by
  match g, hc, hne with
  | [], _, hne => exact absurd rfl hne
  | [t], hc, _ =>
    simp only [Poly.canonical, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨hlength, hcoefficient⟩ := hc
    have hmonomial : t.monomial = [] := List.eq_nil_of_length_eq_zero hlength
    have hmv : monomialValue [] x = 1 := by cases x <;> rfl
    show t.coefficient * monomialValue t.monomial x + 0 ≠ 0
    rw [hmonomial, hmv, Rat.mul_one, Rat.add_zero]
    exact hcoefficient
  | s :: t :: rest, hc, _ =>
    simp only [Poly.canonical, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hs, -⟩, hgt⟩, ht⟩ := hc
    have hts : (Poly.canonical 0 (t :: rest)) = true := ht
    have htlength : t.monomial.length = 0 := by
      cases rest with
      | nil =>
        simp only [Poly.canonical, Bool.and_eq_true, beq_iff_eq] at hts
        exact hts.1
      | cons r rest =>
        simp only [Poly.canonical, Bool.and_eq_true, beq_iff_eq] at hts
        exact hts.1.1.1
    rw [List.eq_nil_of_length_eq_zero hs, List.eq_nil_of_length_eq_zero htlength] at hgt
    exact absurd hgt (by decide)

namespace Stage5

open VastitasOracle.SpectralRuntime.Examples (jordan certificateOf jordan_accepted)

theorem jordan_valid : SpectralValid 0 jordan (certificateOf jordan) :=
  VastitasOracle.SpectralDeclarations.checkCertificate_sound
    (VastitasOracle.FrameDeclarations.isOk_ok jordan_accepted.2)

/-- **The Jordan block has no simple branch.** Over `Pt` its `χ = (t − 2)²`
has the double root `2`, so no localization, witness, exponent and quotient
pass the gap check: an accepted localization is a nonzero constant, and it
would make `χ′(2) = 0` a unit. -/
theorem jordan_no_witness (g W Q : Poly) (e : Nat) :
    SpectralDeclarations.checkWitness 0 2 (certificateOf jordan).characteristic g W e Q ≠ .ok () := by
  intro h
  have hw := VastitasOracle.SpectralDeclarations.checkWitness_sound h
  have hχ : evalAt (certificateOf jordan).characteristic [2] = 0 := by decide +kernel
  have hslope : evalAt (partialDerivative 0 (certificateOf jordan).characteristic) [2] = 0 := by decide +kernel
  have hg : evalAt g [2] ≠ 0 :=
    evalAt_ne_zero_of_canonical_zero hw.localizeCanonical hw.localizeNonzero [2]
  exact jordan_valid.derivative_ne_zero hw hg hχ hslope

/-- The Stage 5 witness perturbed by `10⁻²⁰`. -/
def perturbed : Poly := Poly.scale (1 / 2 + 1 / 10 ^ 20) SpectralDeclarations.Examples.t3

/-- **A perturbed witness is rejected.** For `g = x² + y²` and `e = 1` no
quotient passes the gap check with `W = (1/2 + 10⁻²⁰)·t`: at the branch point
`(3, 4, 5)` the gap identity would give `W·χ′ − g = 2·10⁻²⁰·25 ≠ 0 = Q·χ`. -/
theorem perturbed_witness_rejected (Q : Poly) :
    SpectralDeclarations.checkWitness 2 2 SpectralDeclarations.Examples.characteristic
      SpectralDeclarations.Examples.localize perturbed 1 Q ≠ .ok () := by
  intro h
  have hw := VastitasOracle.SpectralDeclarations.checkWitness_sound h
  have hgap := hw.gap_at SpectralDeclarations.Examples.stage5_valid.characteristic_arity RatHom.id [3, 4, 5]
  have hχ : evalIn RatHom.id SpectralDeclarations.Examples.characteristic [3, 4, 5] = 0 := by decide +kernel
  have hlhs : evalIn RatHom.id perturbed [3, 4, 5] *
        evalIn RatHom.id (partialDerivative 2 SpectralDeclarations.Examples.characteristic) [3, 4, 5] -
      evalIn RatHom.id SpectralDeclarations.Examples.localize [3, 4, 5] ^ 1 ≠ 0 := by
    decide +kernel
  rw [hχ] at hgap
  exact hlhs (by rw [hgap]; grind)

end Stage5

/-- **C8 The gap certificate.** In a valid environment a declared branch has
a finite chart (`g ≠ 0`, `g` a canonical polynomial in the coordinates only,
so not in `t`), a reduced witness (`deg_t W < n`) and a kernel-computed
quotient with `W·χ′ − gᵉ = Q·χ`, which makes `χ′` a unit wherever `χ = 0` and
`g` is a unit, in every ring. For the Stage 5 field the unit localization has
no witness, the origin is off every chart, and the witness perturbed by
`10⁻²⁰` is rejected; the Jordan block has no witness for any localization. -/
theorem c8_gap_certificate {R : Type u} [Lean.Grind.CommRing R] {env : Indexed.Environment} (valid : env.Valid) :
    (∀ {id family object spectrum : DeclId} {localize witness quotient : Poly} {exponent : Nat},
      lookup env id = some (.branch family object spectrum localize witness exponent quotient) →
        ∃ m rows certificate, smoothDimension? env object = some m ∧ SpectralValid m rows certificate ∧
          WitnessValid m rows.length certificate.characteristic localize witness exponent quotient ∧
          localize ≠ [] ∧ Poly.canonical m localize = true ∧
          VastitasKernel.SpectralRuntime.degT witness < rows.length ∧
          ∀ (ι : RatHom R) (z : List R), evalIn ι certificate.characteristic z = 0 → ∀ u : R,
            evalIn ι localize z * u = 1 →
              evalIn ι (partialDerivative m certificate.characteristic) z * (evalIn ι witness z * u ^ exponent) = 1) ∧
    (∀ W Q e, SpectralDeclarations.checkWitness 2 2 SpectralDeclarations.Examples.characteristic (Poly.one 2) W e Q ≠
      .ok ()) ∧
    (∀ {g W Q : Poly} {e : Nat},
      SpectralDeclarations.checkWitness 2 2 SpectralDeclarations.Examples.characteristic g W e Q = .ok () →
        evalAt g [0, 0] = 0) ∧
    (∀ Q, SpectralDeclarations.checkWitness 2 2 SpectralDeclarations.Examples.characteristic
      SpectralDeclarations.Examples.localize Stage5.perturbed 1 Q ≠ .ok ()) ∧
    (∀ g W Q e, SpectralDeclarations.checkWitness 0 2
      (VastitasOracle.SpectralRuntime.Examples.certificateOf VastitasOracle.SpectralRuntime.Examples.jordan).characteristic
        g W e Q ≠ .ok ()) := by
  refine ⟨fun found => ?_, SpectralDeclarations.Examples.unit_gap_no_witness,
    fun h => SpectralDeclarations.Examples.origin_off_chart h, Stage5.perturbed_witness_rejected,
    Stage5.jordan_no_witness⟩
  obtain ⟨-, -, implementation, coordinates, spectrumFamily, endomorphism, fiber, certificate, hobject, -,
    endomorphismFamily, module, rows, symmetric, -, hv, hw⟩ :=
    VastitasOracle.SpectralDeclarations.branch_sound valid found
  exact ⟨coordinates.length, rows, certificate, SpectralCore.smoothDimension_of_lookup hobject, hv, hw,
    hw.localizeNonzero, hw.localizeCanonical, hw.reduced, fun ι z hχ u hg => hv.unit_at hw ι z hχ hg⟩

/-! ## C9–C11: branch observations -/

namespace Stage5

open VastitasOracle.SpectralDeclarations.Examples (localize characteristic adjugate)

/-- `on_branch` at `((3, 4), ±5)` and `((1, 0), ±1)` is true, at `((3, 4), 4)`
false, and at the origin with `t = 0` false although `χ(0, 0, 0) = 0`. -/
theorem branch_points :
    onBranch localize characteristic (intPoint [3, 4]) (intPoint [5]) = true ∧
      onBranch localize characteristic (intPoint [3, 4]) (intPoint [-5]) = true ∧
      onBranch localize characteristic (intPoint [1, 0]) (intPoint [1]) = true ∧
      onBranch localize characteristic (intPoint [1, 0]) (intPoint [-1]) = true ∧
      onBranch localize characteristic (intPoint [3, 4]) (intPoint [4]) = false ∧
      onBranch localize characteristic (intPoint [0, 0]) (intPoint [0]) = false ∧
      evalAt characteristic [0, 0, 0] = 0 := by
  decide +kernel

/-- `dλ = (3/5, 4/5)` at `((3, 4), 5)` and `(−3/5, −4/5)` at `((3, 4), −5)`;
both are unit covectors in the Euclidean chart. -/
theorem branch_differentials :
    branchDifferential localize characteristic (intPoint [3, 4]) (intPoint [5]) = some ⟨[3, 4], [3 / 5, 4 / 5]⟩ ∧
      branchDifferential localize characteristic (intPoint [3, 4]) (intPoint [-5]) =
        some ⟨[3, 4], [-3 / 5, -4 / 5]⟩ ∧
      dot [3 / 5, 4 / 5] [3 / 5, 4 / 5] = 1 ∧ dot [-3 / 5, -4 / 5] [-3 / 5, -4 / 5] = 1 := by
  decide +kernel

/-- The two eigenprojectors at `p = (3, 4)`: `P₊ = (1/5)[[4, 2], [2, 1]]` for
`t = 5` and `P₋ = (1/5)[[1, −2], [−2, 4]]` for `t = −5`. They are symmetric,
`P₊ + P₋ = I` and `5P₊ − 5P₋ = H(p)`. -/
theorem projectors :
    projectorMatrix localize characteristic adjugate (intPoint [3, 4]) (intPoint [5]) =
        some [[4 / 5, 2 / 5], [2 / 5, 1 / 5]] ∧
      projectorMatrix localize characteristic adjugate (intPoint [3, 4]) (intPoint [-5]) =
        some [[1 / 5, -2 / 5], [-2 / 5, 4 / 5]] ∧
      ([[4 / 5, 2 / 5], [2 / 5, 1 / 5]].zipWith (List.zipWith (· + ·)) [[1 / 5, -2 / 5], [-2 / 5, 4 / 5]] :
        List (List Rat)) = [[1, 0], [0, 1]] ∧
      ([[4 / 5, 2 / 5], [2 / 5, 1 / 5]].zipWith (List.zipWith (fun a b => 5 * a - 5 * b))
          [[1 / 5, -2 / 5], [-2 / 5, 4 / 5]] : List (List Rat)) =
        VastitasKernel.FrameRuntime.matrixAt SpectralDeclarations.Examples.rows [3, 4] := by
  decide +kernel

end Stage5

/-- **C9 Branch points and ⊥.** The branch observations are defined exactly
where `g(p) ≠ 0` and `χ(p, t) = 0`; off the chart the differential and the
projector are the failure value and every entry `(0, 0)`. For the Stage 5
branch the listed points are on the branch or off it as stated. -/
theorem c9_branch_points :
    (∀ (localize characteristic : Poly) (adjugate : PolyMatrix) (point value : Program),
      ((branchDifferential localize characteristic point value).isSome = true ↔
        evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0) ∧
      ((projectorMatrix localize characteristic adjugate point value).isSome = true ↔
        evalAt localize (coordinates point) ≠ 0 ∧ evalAt characteristic (branchPoint point value) = 0) ∧
      (onBranch localize characteristic point value = false →
        branchDifferential localize characteristic point value = none ∧
        projectorMatrix localize characteristic adjugate point value = none ∧
        ∀ row column, projectorEntry localize characteristic adjugate point value row column = (0, 0))) ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [3, 4]) (intPoint [5]) = true ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [3, 4]) (intPoint [-5]) = true ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [1, 0]) (intPoint [1]) = true ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [1, 0]) (intPoint [-1]) = true ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [3, 4]) (intPoint [4]) = false ∧
    onBranch SpectralDeclarations.Examples.localize SpectralDeclarations.Examples.characteristic
        (intPoint [0, 0]) (intPoint [0]) = false ∧
    evalAt SpectralDeclarations.Examples.characteristic [0, 0, 0] = 0 := by
  refine ⟨fun localize characteristic adjugate point value => ?_, Stage5.branch_points⟩
  obtain ⟨hd, hp⟩ := VastitasOracle.SpectralRuntime.branch_some_iff (localize := localize)
    (characteristic := characteristic) (adjugate := adjugate) (point := point) (value := value)
  refine ⟨hd, hp, fun h => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := VastitasOracle.SpectralRuntime.off_chart_bottom (adjugate := adjugate) h
  exact ⟨h1, h2, h3⟩

section Accepted

variable {module : Module} {functions : Core.Typing.Signatures} {ctx : Core.Typing.Context} {world : World}
  {fuel : Nat} {values : Values} {id : DeclId} {result : Result} {operands : List ValueType}
  {output : ValueType}

/-- **C10 The branch derivative on accepted Core.** In a valid environment an
accepted `branch_differential(p, t, branch = B)` evaluates to the runtime
branch differential of the declared data of `B`. Off the chart it is the
failure value; on the branch it lies over `p`, has one component per
coordinate, satisfies the implicit-function form `cᵢ·χ′(p, t) = −∂ᵢχ(p, t)`,
and is Hellmann–Feynman `cᵢ = tr(P·∂ᵢH(p))` with the eigenprojector `P`. -/
theorem c10_branch_derivative {point valueTerm : Core.Term} {smooth cotangent line : DeclId} {branch : BranchRef}
    {pointValue valueValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.branchDifferential smooth cotangent line branch))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue] operands) :
    ∃ m x v, pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧
      (coordinates x).length = m ∧ (coordinates v).length = 1 ∧
      eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
        some (.indexed (.fiber .cotangent
          (branchDifferential branch.localize branch.spectrum.characteristic x v))) ∧
      (onBranch branch.localize branch.spectrum.characteristic x v = false →
        branchDifferential branch.localize branch.spectrum.characteristic x v = none) ∧
      (onBranch branch.localize branch.spectrum.characteristic x v = true →
        ∃ fiber P, branchDifferential branch.localize branch.spectrum.characteristic x v = some fiber ∧
          projectorMatrix branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v = some P ∧
          fiber.point = coordinates x ∧ fiber.components.length = m ∧
          ∀ i < m,
            fiber.components.getD i 0 * slopeAt branch.spectrum.characteristic x v =
              -evalAt (partialDerivative i branch.spectrum.characteristic) (branchPoint x v) ∧
            fiber.components.getD i 0 =
              ringTrace (VastitasKernel.FrameRuntime.matrixProduct branch.spectrum.endomorphism.rows.length P
                (VastitasKernel.FrameRuntime.matrixAt
                  (SpectralDeclarations.derivativeMatrix i branch.spectrum.endomorphism.rows) (coordinates x)))) := by
  obtain ⟨declared, -, m, x, v, hm, rfl, rfl, hx, hv, evaluated, -⟩ :=
    SpectralCore.core_spectral_branch_differential found input outputType accepted pointEval valueEval typed
  obtain ⟨m', idempotence, quotient, hm', hvalid, hw⟩ := declared.checked envValid
  rw [hm] at hm'
  cases hm'
  refine ⟨m, x, v, rfl, rfl, hx, hv, evaluated, fun hoff => (VastitasOracle.SpectralRuntime.off_chart_bottom
    (adjugate := branch.spectrum.adjugate) hoff).1, fun hon => ?_⟩
  have hd := VastitasOracle.SpectralRuntime.branchDifferential_of_onBranch hon
  have hP := VastitasOracle.SpectralRuntime.projectorMatrix_of_onBranch (adjugate := branch.spectrum.adjugate) hon
  refine ⟨_, _, hd, hP, ?_⟩
  obtain ⟨hpoint, hlength, himplicit⟩ :=
    VastitasOracle.SpectralRuntime.branchDifferential_implicit (certificate :=
      ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) hvalid hw hx hd
  exact ⟨hpoint, hlength, fun i hi => ⟨himplicit i hi,
    VastitasOracle.SpectralRuntime.branchDifferential_hellmann_feynman (certificate :=
      ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) hvalid hw hx hd hP hi⟩⟩

/-- **C11 The eigenprojector on accepted Core.** In a valid environment an
accepted `branch_projector(p, t, branch = B, eᵢ, eⱼ)` evaluates to an entry,
in range, of the runtime eigenprojector `P` of the declared data of `B`: off
the chart `(0, 0)`; on the branch the entry `(i, j)` of `P`, which satisfies
`P·P = P`, `tr P = 1`, `H(p)·P = P·t` and `P·H(p) = P·t`, so `P` commutes
with `H(p)`. -/
theorem c11_eigenprojector {point valueTerm : Core.Term} {smooth line : DeclId} {branch : BranchRef}
    {row column : Nat} {pointValue valueValue : Value} (envValid : module.declarations.indexed.Valid)
    (found : module.declarations.primitive? id = some (.branchProjector smooth line branch row column))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue] operands) :
    row < branch.spectrum.rank ∧ column < branch.spectrum.rank ∧
      ∃ x v t, pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧ coordinates v = [t] ∧
        eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
          some (.pairInt
            (projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v row column).1
            (projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v row column).2) ∧
        (onBranch branch.localize branch.spectrum.characteristic x v = false →
          projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v row column = (0, 0)) ∧
        (onBranch branch.localize branch.spectrum.characteristic x v = true →
          ∃ P, projectorMatrix branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v = some P ∧
            projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate x v row column =
              VastitasKernel.SpectralRuntime.matrixEntry P row column ∧
            VastitasKernel.FrameRuntime.matrixProduct branch.spectrum.endomorphism.rows.length P P = P ∧
            ringTrace P = 1 ∧
            VastitasKernel.FrameRuntime.matrixProduct branch.spectrum.endomorphism.rows.length
              (VastitasKernel.FrameRuntime.matrixAt branch.spectrum.endomorphism.rows (coordinates x)) P =
                scaleMatrix t P ∧
            VastitasKernel.FrameRuntime.matrixProduct branch.spectrum.endomorphism.rows.length P
              (VastitasKernel.FrameRuntime.matrixAt branch.spectrum.endomorphism.rows (coordinates x)) =
                scaleMatrix t P) := by
  obtain ⟨declared, -, hrow, hcolumn, m, x, v, hm, rfl, rfl, hx, hv, evaluated⟩ :=
    SpectralCore.core_spectral_branch_projector found input outputType accepted pointEval valueEval typed
  obtain ⟨m', idempotence, quotient, hm', hvalid, hw⟩ := declared.checked envValid
  rw [hm] at hm'
  cases hm'
  obtain ⟨t, ht⟩ : ∃ t, coordinates v = [t] := by
    cases hcv : coordinates v with
    | nil => rw [hcv] at hv; cases hv
    | cons t rest =>
      cases rest with
      | nil => exact ⟨t, rfl⟩
      | cons _ _ => rw [hcv] at hv; simp at hv
  refine ⟨hrow, hcolumn, x, v, t, rfl, rfl, ht, evaluated, fun hoff => ?_, fun hon => ?_⟩
  · exact (VastitasOracle.SpectralRuntime.off_chart_bottom (adjugate := branch.spectrum.adjugate) hoff).2.2.1 row
      column
  · have hP := VastitasOracle.SpectralRuntime.projectorMatrix_of_onBranch (adjugate := branch.spectrum.adjugate) hon
    have certificate : SpectralValid m branch.spectrum.endomorphism.rows
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩ := hvalid
    refine ⟨_, hP, by simp [projectorEntry, hP], ?_, ?_, ?_, ?_⟩
    · exact VastitasOracle.SpectralRuntime.projector_idempotent (certificate :=
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) certificate hw hx hP
    · exact VastitasOracle.SpectralRuntime.projector_trace_one (certificate :=
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) certificate hw hx hP
    · exact VastitasOracle.SpectralRuntime.projector_eigen (certificate :=
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) certificate hw hx ht hP
    · exact VastitasOracle.SpectralRuntime.projector_commutes (certificate :=
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩) certificate hw hx ht hP

end Accepted

/-! ## C12: degenerate cases -/

namespace Stage5

/-- `H = [[x]]` on `Plane`: rank 1, `χ = t − x`, `χ′ = 1`. -/
def rankOne : PolyMatrix := [[SpectralDeclarations.Examples.x]]

/-- `diag(1, 2, 3, 4)` over `Pt`, at the rank limit, and `diag(1, …, 5)` past it. -/
def diagonal4 : PolyMatrix :=
  [[Poly.const 0 1, [], [], []], [[], Poly.const 0 2, [], []], [[], [], Poly.const 0 3, []],
    [[], [], [], Poly.const 0 4]]

def diagonal5 : PolyMatrix :=
  [[Poly.const 0 1, [], [], [], []], [[], Poly.const 0 2, [], [], []], [[], [], Poly.const 0 3, [], []],
    [[], [], [], Poly.const 0 4, []], [[], [], [], [], Poly.const 0 5]]

open VastitasOracle.SpectralRuntime.Examples (certificateOf zero zero_accepted)

/-- The certificate that the elaboration computes over `Plane`. -/
def certificateOnPlane (rows : PolyMatrix) : SpectralCertificate :=
  ((AlgebraBasis.run (SpectralDeclarations.certify 2 rows)).toOption).getD default

theorem rankOne_accepted :
    (SpectralDeclarations.checkRows 2 1 rankOne true).isOk = true ∧
      (SpectralDeclarations.checkCertificate 2 rankOne (certificateOnPlane rankOne)).isOk = true ∧
      (SpectralDeclarations.checkWitness 2 1 (certificateOnPlane rankOne).characteristic (Poly.one 2) (Poly.one 3) 1
        []).isOk = true := by
  decide +kernel

theorem rank_limit :
    Limits.spectralRank = 4 ∧ (SpectralDeclarations.checkRows 0 4 diagonal4 true).isOk = true ∧
      (SpectralDeclarations.checkCertificate 0 diagonal4 (certificateOf diagonal4)).isOk = true ∧
      (SpectralDeclarations.checkRows 0 5 diagonal5 true).isOk = false := by
  decide +kernel

end Stage5

/-- **C12 Degenerate cases.** `H = 0` over `Pt` has an accepted certificate;
the rank-1 field `[[x]]` on `Plane` has the gap certificate `W = 1`, `g = 1`
(a chart without a hole); the origin is off every chart of the Stage 5
spectrum; and `n = 4 = spectralRank` is accepted while `n = 5` is rejected. -/
theorem c12_degenerate :
    SpectralValid 0 VastitasOracle.SpectralRuntime.Examples.zero
        (VastitasOracle.SpectralRuntime.Examples.certificateOf VastitasOracle.SpectralRuntime.Examples.zero) ∧
      (SpectralDeclarations.checkWitness 2 1 (Stage5.certificateOnPlane Stage5.rankOne).characteristic
        (Poly.one 2) (Poly.one 3) 1 []).isOk = true ∧
      (∀ {g W Q : Poly} {e : Nat},
        SpectralDeclarations.checkWitness 2 2 SpectralDeclarations.Examples.characteristic g W e Q = .ok () →
          evalAt g [0, 0] = 0) ∧
      Limits.spectralRank = 4 ∧
      SpectralValid 0 Stage5.diagonal4
        (VastitasOracle.SpectralRuntime.Examples.certificateOf Stage5.diagonal4) ∧
      (SpectralDeclarations.checkRows 0 5 Stage5.diagonal5 true).isOk = false :=
  ⟨VastitasOracle.SpectralDeclarations.checkCertificate_sound
      (VastitasOracle.FrameDeclarations.isOk_ok VastitasOracle.SpectralRuntime.Examples.zero_accepted.2),
    Stage5.rankOne_accepted.2.2, fun h => SpectralDeclarations.Examples.origin_off_chart h, Stage5.rank_limit.1,
    VastitasOracle.SpectralDeclarations.checkCertificate_sound
      (VastitasOracle.FrameDeclarations.isOk_ok Stage5.rank_limit.2.2.1), Stage5.rank_limit.2.2.2⟩

/-! ## C13: weakening -/

/-- **C13 Weakening.** Spectral declarations inserted at any position of an
environment with unique ids change neither the validity nor the value of any
binding of Stages 1–4, nor the validity of any declaration of Stages 1–4; the
spectral bindings are `MetricFree`, unchanged by metric declarations, by frame
declarations (when they name no frame) and by nature declarations, and they
evaluate the same in every environment. -/
theorem c13_weakening {pre extra post : Environment} (unique : ((pre ++ extra ++ post).map Entry.id).Nodup) :
    ((∀ entry ∈ extra, SpectralWeakening.SpectralDeclaration entry.declaration) →
      (∀ {binding : PrimitiveBinding}, ¬ SpectralWeakening.SpectralBinding binding →
        validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        (binding.Valid (pre ++ extra ++ post) ↔ binding.Valid (pre ++ post)) ∧
        ∀ values, evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) ∧
      (∀ (ranks : List (DeclId × Nat)) {entry : Entry}, SpectralWeakening.NamesNoSpectral entry.declaration →
        validEntry (pre ++ extra ++ post) ranks entry = validEntry (pre ++ post) ranks entry ∧
        (entry.Valid (pre ++ extra ++ post) ranks ↔ entry.Valid (pre ++ post) ranks))) ∧
    ((∀ entry ∈ extra, SmoothMetricWeakening.MetricDeclaration entry.declaration) →
      ∀ {binding : PrimitiveBinding}, SpectralWeakening.SpectralBinding binding → ∀ values,
        SmoothMetricWeakening.MetricFree binding ∧
        validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) ∧
    ((∀ entry ∈ extra, FrameWeakening.FrameDeclaration entry.declaration) →
      ∀ {binding : PrimitiveBinding}, FrameWeakening.bindingFrames binding = [] → ∀ values,
        validPrimitiveBinding (pre ++ extra ++ post) binding = validPrimitiveBinding (pre ++ post) binding ∧
        evalPrimitive (pre ++ extra ++ post) binding values = evalPrimitive (pre ++ post) binding values) ∧
    (∀ (env env' : Indexed.Environment) (values : List Value) {binding : PrimitiveBinding},
      SpectralWeakening.SpectralBinding binding → evalPrimitive env binding values = evalPrimitive env' binding values) := by
  refine ⟨fun spectral => ⟨fun {binding} other => SpectralWeakening.stage4_bindings_spectral_free spectral unique other,
      fun ranks {entry} other => SpectralWeakening.spectral_weakening_entry spectral unique ranks other⟩,
    fun metric {binding} spectralBinding values => ?_, fun frames {binding} noFrames values => ?_,
    fun env env' values {binding} spectralBinding => ?_⟩
  · obtain ⟨free, valid, -, evaluated⟩ :=
      SpectralWeakening.spectral_bindings_metric_free metric unique spectralBinding values
    exact ⟨free, valid, evaluated⟩
  · obtain ⟨valid, -, evaluated⟩ := SpectralWeakening.spectral_bindings_frame_free frames unique noFrames
    exact ⟨valid, evaluated values⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := SpectralCore.spectral_bindings_environment_free env env' values
    cases binding <;> first | exact (spectralBinding : False).elim | skip
    all_goals first | exact h1 _ _ _ | exact h2 _ _ _ | exact h3 _ _ _ _ _ | exact h4 _ _ _ | exact h5 _ _ _ _ |
      exact h6 _ _ _ _ _

end VastitasOracle.SpectralAcceptance
