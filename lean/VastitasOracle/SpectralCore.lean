import VastitasOracle.SpectralPrimitives
import VastitasOracle.SpectralRuntime
import VastitasOracle.SmoothReverse
import VastitasOracle.SmoothReverseCompiled

set_option autoImplicit false

/-! The spectral bindings on the program value that checked Core builds
(Stage 5, #806).

**Embedded declarations.** A spectral binding embeds the declarations it reads
as an `EndoRef`, a `SpectrumRef` or a `BranchRef`. Its validity, which
acceptance includes, compares every embedded copy with its declaration, down
the chain branch → spectrum → endomorphism (`IndexedSpectralContracts`), so the
embedded rows, `χ`, adjugate, localization, witness and exponent are the
declared ones (`DeclaredEndo`, `DeclaredSpectrum`, `DeclaredBranch`), and two
bindings that name one declaration read the same data (`*.unique`). In a valid
environment those declarations passed the kernel's checks, so the embedded
data satisfies the certificate identities (`DeclaredSpectrum.checked`:
`SpectralValid`) and the gap certificate (`DeclaredBranch.checked`:
`WitnessValid`), whose meaning is stated in `SpectralDeclarations` and
`SpectralRuntime`.

**Invariants** (`spectralInvariant_valid_sound`, `spectralInvariant_tracePower_at`,
`spectralInvariant_charCoefficient_at`, `core_spectral_invariant`): an accepted
`trace_power(H, k)` or `char_coefficient(S, i)` is a declared smooth map
`X → Line` with the one image `tr(H(x)ᵏ)`, or the coefficient of `tⁱ` in `χ`,
of the declared field, at every point of every ring; its Core node evaluates
to that map as one program node. Its derivative rule is `morphism` with that
map (`spectralInvariant_rule`), so a compiled reverse step along it is the
Stage 3 `cotangentJacobian` of that map (`compiled_invariant_step`).

**Observations** (`core_spectral_annihilates`, `core_spectral_action_entry`,
`core_spectral_on_branch`, `core_spectral_branch_differential`,
`core_spectral_branch_projector`): an accepted call evaluates, one unit of fuel
later, to the `SpectralRuntime` operation of its binding applied to the
program values of its operands and to the embedded, declared data; the point
has the coordinates of the spectrum's object and the value one coordinate.

`spectral_runtime_operations` states that the erased evaluator, which
generated programs link, applies the same operations, and
`spectral_bindings_environment_free` that every spectral binding evaluates the
same in every environment.

These theorems state which runtime value checked Core computes; what the
values mean is stated about the `SpectralRuntime` functions in
`VastitasOracle.SpectralRuntime`. Everything here holds for all inputs. -/
namespace VastitasOracle.SpectralCore

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasOracle.SmoothCalculus (RatHom evalIn)
open VastitasOracle.SpectralAlgebra (MatrixArity ringTrace ringPow evalMatrix ringSum squareOf_spec)
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid InvariantMeaning invariantImage polyEntry)

universe u

/-! ## Embedded declarations -/

/-- The embedded endomorphism is its declaration. -/
def DeclaredEndo (env : Indexed.Environment) (endo : EndoRef) : Prop :=
  ∃ family, endomorphismData? env endo.endomorphism = some (family, endo.object, endo.module, endo.rows, endo.symmetric)

/-- The embedded spectrum is its declaration: its endomorphism is declared,
and the spectrum declaration names that endomorphism on its object, with a
certificate whose `χ` and adjugate are the embedded ones. -/
def DeclaredSpectrum (env : Indexed.Environment) (spectrum : SpectrumRef) : Prop :=
  DeclaredEndo env spectrum.endomorphism ∧
    ∃ family fiber certificate, spectrumData? env spectrum.spectrum =
        some (family, spectrum.endomorphism.object, spectrum.endomorphism.endomorphism, fiber, certificate) ∧
      certificate.characteristic = spectrum.characteristic ∧ certificate.adjugate = spectrum.adjugate

/-- The embedded branch is its declaration: its spectrum is declared, and the
branch declaration names that spectrum on its object, with the embedded
localization, witness and exponent. -/
def DeclaredBranch (env : Indexed.Environment) (branch : BranchRef) : Prop :=
  DeclaredSpectrum env branch.spectrum ∧
    ∃ family quotient, branchData? env branch.branch =
      some (family, branch.spectrum.endomorphism.object, branch.spectrum.spectrum, branch.localize, branch.witness,
        branch.exponent, quotient)

/-- The embedded declaration of a spectral invariant is its declaration. -/
def InvariantDeclared (env : Indexed.Environment) : SpectralInvariant → Prop
  | .tracePower endomorphism _ => DeclaredEndo env endomorphism
  | .charCoefficient spectrum _ => DeclaredSpectrum env spectrum

theorem declaredEndo_of_endoDeclared {env : Indexed.Environment} {endo : EndoRef}
    (h : endoDeclared env endo = true) : DeclaredEndo env endo := by
  unfold endoDeclared at h
  cases hd : endomorphismData? env endo.endomorphism with
  | none => rw [hd] at h; cases h
  | some data =>
    obtain ⟨family, object, module, rows, symmetric⟩ := data
    rw [hd] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    exact ⟨family, hd⟩

theorem declaredSpectrum_of_spectrumDeclared {env : Indexed.Environment} {spectrum : SpectrumRef}
    (h : spectrumDeclared env spectrum = true) : DeclaredSpectrum env spectrum := by
  unfold spectrumDeclared at h
  cases hd : spectrumData? env spectrum.spectrum with
  | none => rw [hd] at h; cases h
  | some data =>
    obtain ⟨family, object, endomorphism, fiber, certificate⟩ := data
    rw [hd] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hobject, hendomorphism⟩, hcharacteristic⟩, hadjugate⟩, hdeclared⟩ := h
    subst hobject hendomorphism
    exact ⟨declaredEndo_of_endoDeclared hdeclared, family, fiber, certificate, hd, hcharacteristic, hadjugate⟩

theorem declaredBranch_of_branchDeclared {env : Indexed.Environment} {branch : BranchRef}
    (h : branchDeclared env branch = true) : DeclaredBranch env branch := by
  unfold branchDeclared at h
  cases hd : branchData? env branch.branch with
  | none => rw [hd] at h; cases h
  | some data =>
    obtain ⟨family, object, spectrum, localize, witness, exponent, quotient⟩ := data
    rw [hd] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hobject, hspectrum⟩, hlocalize⟩, hwitness⟩, hexponent⟩, hdeclared⟩ := h
    subst hobject hspectrum hlocalize hwitness hexponent
    exact ⟨declaredSpectrum_of_spectrumDeclared hdeclared, family, quotient, hd⟩

theorem invariantDeclared_of_declared {env : Indexed.Environment} {invariant : SpectralInvariant}
    (h : invariant.declared env = true) : InvariantDeclared env invariant := by
  cases invariant with
  | tracePower endomorphism power => exact declaredEndo_of_endoDeclared h
  | charCoefficient spectrum index => exact declaredSpectrum_of_spectrumDeclared h

theorem branchData_lookup {env : Indexed.Environment} {id : DeclId}
    {data : DeclId × DeclId × DeclId × AlgebraRuntime.Poly × AlgebraRuntime.Poly × Nat × AlgebraRuntime.Poly}
    (h : branchData? env id = some data) :
    lookup env id = some (.branch data.1 data.2.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2.1 data.2.2.2.2.2.1
      data.2.2.2.2.2.2) := by
  unfold branchData? at h
  split at h
  · rename_i found
    cases h
    exact found
  · cases h

theorem smoothDimension_of_lookup {env : Indexed.Environment} {object implementation : DeclId}
    {coordinates : List String} (h : lookup env object = some (.smoothAffine implementation coordinates)) :
    smoothDimension? env object = some coordinates.length := by
  simp [smoothDimension?, smoothCoordinates?, h]

/-- **The embedded rows are checked.** In a valid environment a declared
endomorphism has `n ≤ spectralRank` rows of `n` canonical polynomials in the
`m` coordinates of its object, symmetric when declared so. -/
theorem DeclaredEndo.checked {env : Indexed.Environment} (valid : env.Valid) {endo : EndoRef}
    (h : DeclaredEndo env endo) :
    ∃ m, smoothDimension? env endo.object = some m ∧ endo.rows.length ≤ Limits.spectralRank ∧
      SpectralDeclarations.squareOf endo.rows.length m endo.rows = true ∧
      (endo.symmetric = true → ∀ i j, polyEntry endo.rows i j = polyEntry endo.rows j i) := by
  obtain ⟨family, found⟩ := h
  obtain ⟨-, -, implementation, coordinates, moduleFamily, basis, hobject, -, hrank, hsquare, hsym⟩ :=
    VastitasOracle.SpectralDeclarations.endomorphism_sound valid
      (VastitasOracle.SpectralDeclarations.endomorphismData_lookup found)
  have hlength := (squareOf_spec hsquare).1
  rw [← hlength] at hrank hsquare
  exact ⟨coordinates.length, smoothDimension_of_lookup hobject, hrank, hsquare, hsym⟩

theorem DeclaredEndo.arity {env : Indexed.Environment} (valid : env.Valid) {endo : EndoRef}
    (h : DeclaredEndo env endo) {m : Nat} (hm : smoothDimension? env endo.object = some m) :
    MatrixArity m endo.rows := by
  obtain ⟨m', hm', -, hsquare, -⟩ := h.checked valid
  rw [hm] at hm'
  cases hm'
  exact (squareOf_spec hsquare).2.2

/-- **The embedded spectrum is checked.** In a valid environment the embedded
`χ` and adjugate of a declared spectrum, with the declared idempotence
quotient, are a valid certificate of the embedded rows. -/
theorem DeclaredSpectrum.checked {env : Indexed.Environment} (valid : env.Valid) {spectrum : SpectrumRef}
    (h : DeclaredSpectrum env spectrum) :
    ∃ m idempotence, smoothDimension? env spectrum.object = some m ∧
      SpectralValid m spectrum.endomorphism.rows ⟨spectrum.characteristic, spectrum.adjugate, idempotence⟩ := by
  obtain ⟨⟨endomorphismFamily, endomorphismFound⟩, family, fiber, certificate, found, hcharacteristic, hadjugate⟩ := h
  obtain ⟨-, -, implementation, coordinates, hobject, -, endomorphismFamily', module, rows, symmetric, hend, hv⟩ :=
    VastitasOracle.SpectralDeclarations.spectrum_sound valid
      (VastitasOracle.SpectralDeclarations.spectrumData_lookup found)
  rw [endomorphismFound] at hend
  simp only [Option.some.injEq, Prod.mk.injEq] at hend
  obtain ⟨-, -, -, hrows, -⟩ := hend
  subst hrows
  obtain ⟨characteristic, adjugate, idempotence⟩ := certificate
  simp only at hcharacteristic hadjugate
  subst hcharacteristic hadjugate
  exact ⟨coordinates.length, idempotence, smoothDimension_of_lookup hobject, hv⟩

theorem DeclaredSpectrum.spectrumData {env : Indexed.Environment} {spectrum : SpectrumRef}
    (h : DeclaredSpectrum env spectrum) :
    ∃ family fiber idempotence, spectrumData? env spectrum.spectrum =
      some (family, spectrum.endomorphism.object, spectrum.endomorphism.endomorphism, fiber,
        ⟨spectrum.characteristic, spectrum.adjugate, idempotence⟩) := by
  obtain ⟨-, family, fiber, certificate, found, hcharacteristic, hadjugate⟩ := h
  obtain ⟨characteristic, adjugate, idempotence⟩ := certificate
  simp only at hcharacteristic hadjugate
  subst hcharacteristic hadjugate
  exact ⟨family, fiber, idempotence, found⟩

/-- **The embedded branch is checked.** In a valid environment the embedded
data of a declared branch satisfies every hypothesis of the runtime theorems
of `SpectralRuntime`: the embedded `χ` and adjugate are a valid certificate
of the embedded rows, and the embedded localization, witness and exponent,
with the declared quotient, a valid gap certificate for that `χ`. -/
theorem DeclaredBranch.checked {env : Indexed.Environment} (valid : env.Valid) {branch : BranchRef}
    (h : DeclaredBranch env branch) :
    ∃ m idempotence quotient, smoothDimension? env branch.object = some m ∧
      SpectralValid m branch.spectrum.endomorphism.rows
        ⟨branch.spectrum.characteristic, branch.spectrum.adjugate, idempotence⟩ ∧
      WitnessValid m branch.spectrum.endomorphism.rows.length branch.spectrum.characteristic branch.localize
        branch.witness branch.exponent quotient := by
  obtain ⟨hs, family, quotient, found⟩ := h
  obtain ⟨m, idempotence, hm, hv⟩ := hs.checked valid
  obtain ⟨spectrumFamily, fiber, idempotence', spectrumFound⟩ := hs.spectrumData
  obtain ⟨endomorphismFamily, endomorphismFound⟩ := hs.1
  obtain ⟨-, -, implementation, coordinates, spectrumFamily', endomorphism, fiber', certificate, hobject, hsd,
    endomorphismFamily', module, rows, symmetric, hend, -, hw⟩ :=
    VastitasOracle.SpectralDeclarations.branch_sound valid (branchData_lookup found)
  rw [spectrumFound] at hsd
  simp only [Option.some.injEq, Prod.mk.injEq] at hsd
  obtain ⟨-, -, hendomorphism, -, hcertificate⟩ := hsd
  subst hendomorphism hcertificate
  rw [endomorphismFound] at hend
  simp only [Option.some.injEq, Prod.mk.injEq] at hend
  obtain ⟨-, -, -, hrows, -⟩ := hend
  subst hrows
  have hm' : smoothDimension? env branch.object = some coordinates.length := smoothDimension_of_lookup hobject
  have hm2 : smoothDimension? env branch.object = some m := hm
  rw [hm2] at hm'
  cases hm'
  exact ⟨coordinates.length, idempotence, quotient, hm2, hv, hw⟩

/-- **One declaration, one embedding.** Two embedded endomorphisms, spectra or
branches that name the same declaration are equal, so every binding of one
program that names it reads the same data. -/
theorem DeclaredEndo.unique {env : Indexed.Environment} {first second : EndoRef}
    (firstDeclared : DeclaredEndo env first) (secondDeclared : DeclaredEndo env second)
    (same : first.endomorphism = second.endomorphism) : first = second := by
  obtain ⟨_, firstData⟩ := firstDeclared
  obtain ⟨_, secondData⟩ := secondDeclared
  rw [same, secondData] at firstData
  simp only [Option.some.injEq, Prod.mk.injEq] at firstData
  obtain ⟨-, objectEq, moduleEq, rowsEq, symmetricEq⟩ := firstData
  cases first
  cases second
  simp_all

theorem DeclaredSpectrum.unique {env : Indexed.Environment} {first second : SpectrumRef}
    (firstDeclared : DeclaredSpectrum env first) (secondDeclared : DeclaredSpectrum env second)
    (same : first.spectrum = second.spectrum) : first = second := by
  obtain ⟨_, _, _, firstData⟩ := firstDeclared.spectrumData
  obtain ⟨_, _, _, secondData⟩ := secondDeclared.spectrumData
  rw [same, secondData] at firstData
  simp only [Option.some.injEq, Prod.mk.injEq, SpectralCertificate.mk.injEq] at firstData
  obtain ⟨-, -, endomorphismEq, -, characteristicEq, adjugateEq, -⟩ := firstData
  have endo := DeclaredEndo.unique firstDeclared.1 secondDeclared.1 endomorphismEq.symm
  cases first
  cases second
  simp_all

theorem DeclaredBranch.unique {env : Indexed.Environment} {first second : BranchRef}
    (firstDeclared : DeclaredBranch env first) (secondDeclared : DeclaredBranch env second)
    (same : first.branch = second.branch) : first = second := by
  obtain ⟨firstSpectrum, _, _, firstData⟩ := firstDeclared
  obtain ⟨secondSpectrum, _, _, secondData⟩ := secondDeclared
  rw [same, secondData] at firstData
  simp only [Option.some.injEq, Prod.mk.injEq] at firstData
  obtain ⟨-, -, spectrumEq, localizeEq, witnessEq, exponentEq, -⟩ := firstData
  have spectrum := DeclaredSpectrum.unique firstSpectrum secondSpectrum spectrumEq.symm
  cases first
  cases second
  simp_all

/-! ## Accepted invariants -/

theorem image?_eq (m : Nat) (invariant : SpectralInvariant) :
    invariant.image? m = (invariantImage m invariant).toOption := by
  cases invariant <;> rfl

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

/-- **What an accepted spectral invariant is.** The binding of a valid
`trace_power(H, k)` or `char_coefficient(S, i)` is a declared smooth map
`X → Line` from the object of its embedded declaration, which is its
declaration, with one canonical image: the invariant that its provenance
names (`InvariantMeaning`, `SpectralDeclarations.invariant_sound`). -/
theorem spectralInvariant_valid_sound {env : Indexed.Environment} {application : Application}
    {map : AlgebraRuntime.Map} {invariant : SpectralInvariant}
    (valid : spectralInvariantValid env application map invariant = true) :
    InvariantDeclared env invariant ∧ isSmoothFamily env application.family = true ∧
      ∃ m line image, application.indices = [.object (.global invariant.object), .object (.global line)] ∧
        smoothDimension? env invariant.object = some m ∧ smoothDimension? env line = some 1 ∧
        map.arity = m ∧ map.basis = [] ∧ map.images = [image] ∧ AlgebraRuntime.Poly.canonical m image = true ∧
        invariantImage m invariant = .ok image ∧ InvariantMeaning m invariant image := by
  unfold spectralInvariantValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨constant, source⟩, declared⟩, imageValid⟩ := valid
  unfold smoothConstantValid at constant
  simp only [Bool.and_eq_true] at constant
  obtain ⟨⟨smooth, _⟩, endpoints⟩ := constant
  cases hend : smoothEndpoints? env application with
  | none => simp [hend] at endpoints
  | some dimensions =>
    obtain ⟨n, k⟩ := dimensions
    simp only [hend] at endpoints
    obtain ⟨x, y, indices, hx, hy⟩ := SmoothPrimitives.endpoints_spec hend
    have hsource : x = invariant.object := by
      simp only [smoothSource?, indices, Option.some.injEq] at source
      exact source
    subst hsource
    simp only [SmoothRuntime.wellFormed, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true]
      at endpoints
    obtain ⟨⟨⟨harity, hbasis⟩, hlength⟩, hcanonical⟩ := endpoints
    cases himage : invariant.image? map.arity with
    | none => simp [himage] at imageValid
    | some image =>
      simp only [himage, beq_iff_eq] at imageValid
      rw [image?_eq] at himage
      have hok := toOption_eq_some himage
      rw [imageValid] at hlength hcanonical
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlength
      subst hlength
      rw [harity] at hok
      refine ⟨invariantDeclared_of_declared declared, smooth, n, y, image, indices, hx, hy, harity, hbasis,
        imageValid, ?_, hok, VastitasOracle.SpectralDeclarations.invariant_sound hok⟩
      exact harity ▸ hcanonical image (by simp)

/-- **An accepted trace power is `tr(H(x)ᵏ)` of the declared field** at every
point of every ring, in a valid environment: the map of a valid
`trace_power(H, k)` binding has the one image whose value is the trace of the
`k`-th power of the declared rows, `1 ≤ k ≤ spectralPower`. -/
theorem spectralInvariant_tracePower_at {R : Type u} [Lean.Grind.CommRing R] {env : Indexed.Environment}
    (envValid : env.Valid) {application : Application} {map : AlgebraRuntime.Map} {endo : EndoRef} {power : Nat}
    (valid : spectralInvariantValid env application map (.tracePower endo power) = true) :
    DeclaredEndo env endo ∧ ∃ m image, smoothDimension? env endo.object = some m ∧ map.arity = m ∧
      map.images = [image] ∧ 1 ≤ power ∧ power ≤ Limits.spectralPower ∧
      ∀ (ι : RatHom R) (x : List R), evalIn ι image x = ringTrace (ringPow endo.rows.length (evalMatrix ι endo.rows x) power) := by
  obtain ⟨declared, -, m, -, image, -, hm, -, harity, -, himages, -, hok, meaning⟩ :=
    spectralInvariant_valid_sound valid
  obtain ⟨hk, hpower, -, -⟩ := meaning
  exact ⟨declared, m, image, hm, harity, himages, hk, hpower, fun ι x =>
    VastitasOracle.SpectralDeclarations.tracePowerImage_at hok (declared.arity envValid hm) ι x⟩

/-- **An accepted coefficient is the coefficient of `tⁱ` in the declared `χ`**:
`χ(x, t) = Σₖ χₖ(x) tᵏ` at every point of every ring, with `χᵢ` the image,
`i ≤ n`, in a valid environment. -/
theorem spectralInvariant_charCoefficient_at {R : Type u} [Lean.Grind.CommRing R] {env : Indexed.Environment}
    (envValid : env.Valid) {application : Application} {map : AlgebraRuntime.Map} {spectrum : SpectrumRef}
    {index : Nat} (valid : spectralInvariantValid env application map (.charCoefficient spectrum index) = true) :
    DeclaredSpectrum env spectrum ∧ ∃ m image, smoothDimension? env spectrum.object = some m ∧ map.arity = m ∧
      map.images = [image] ∧ index ≤ spectrum.rank ∧
      image = SpectralDeclarations.charCoefficient spectrum.characteristic index ∧
      ∀ (ι : RatHom R) (x : List R), x.length = m → ∀ t : R,
        evalIn ι spectrum.characteristic (x ++ [t]) =
          ringSum (SpectralRuntime.degT spectrum.characteristic + 1)
            (fun k => evalIn ι (SpectralDeclarations.charCoefficient spectrum.characteristic k) x * t ^ k) := by
  obtain ⟨declared, -, m, -, image, -, hm, -, harity, -, himages, -, -, meaning⟩ :=
    spectralInvariant_valid_sound valid
  obtain ⟨hindex, himage⟩ := meaning
  obtain ⟨m', idempotence, hm', hv⟩ := declared.checked envValid
  have hm2 : smoothDimension? env spectrum.object = some m := hm
  rw [hm2] at hm'
  cases hm'
  exact ⟨declared, m, image, hm, harity, himages, hindex, himage, fun ι x hx t => hv.charCoefficient_at ι hx t⟩

/-! ## Inversion of the logical semantics -/

theorem spectralInvariant_inv {env : Indexed.Environment} {application : Application} {map : AlgebraRuntime.Map}
    {invariant : SpectralInvariant} {values : List Value} {value : Value}
    (h : evalPrimitive env (.spectralInvariant application map invariant) values = some value) :
    values = [] ∧ value = .indexed (.smooth (.primitive map)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
    PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · contradiction

theorem annihilates_inv {env : Indexed.Environment} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {values : List Value} {value : Value}
    (h : evalPrimitive env (.annihilates smooth spectrum element) values = some value) :
    ∃ point, values = [.indexed (.smooth point)] ∧
      value = .boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element point) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.annihilates, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, rfl, rfl⟩
  · contradiction

theorem actionEntry_inv {env : Indexed.Environment} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {row column : Nat} {values : List Value} {value : Value}
    (h : evalPrimitive env (.actionEntry smooth spectrum element row column) values = some value) :
    ∃ point, values = [.indexed (.smooth point)] ∧
      value = .pairInt (SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column).1
        (SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.actionEntry, PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, rfl, (Option.some.inj h).symm⟩
  · contradiction

theorem onBranch_inv {env : Indexed.Environment} {smooth line : DeclId} {branch : BranchRef}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.onBranch smooth line branch) values = some value) :
    ∃ point v, values = [.indexed (.smooth point), .indexed (.smooth v)] ∧
      value = .boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic point v) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.onBranch, PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem branchDifferential_inv {env : Indexed.Environment} {smooth cotangent line : DeclId} {branch : BranchRef}
    {values : List Value} {value : Value}
    (h : evalPrimitive env (.branchDifferential smooth cotangent line branch) values = some value) :
    ∃ point v, values = [.indexed (.smooth point), .indexed (.smooth v)] ∧
      value = .indexed (.fiber .cotangent
        (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic point v)) := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.branchDifferential,
    PrimitiveDescriptor.ofBool] at h
  split at h
  · cases h
    exact ⟨_, _, rfl, rfl⟩
  · contradiction

theorem branchProjector_inv {env : Indexed.Environment} {smooth line : DeclId} {branch : BranchRef}
    {row column : Nat} {values : List Value} {value : Value}
    (h : evalPrimitive env (.branchProjector smooth line branch row column) values = some value) :
    ∃ point v, values = [.indexed (.smooth point), .indexed (.smooth v)] ∧
      value = .pairInt
        (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
          point v row column).1
        (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
          point v row column).2 := by
  simp only [evalPrimitive, PrimitiveBinding.contract, SpectralRegistry.branchProjector,
    PrimitiveDescriptor.ofBool] at h
  split at h
  · exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
  · contradiction

/-- **The runtime operations.** The erased evaluator of each spectral binding,
which generated programs link, applies the `SpectralRuntime` operation of
the logical evaluator to the embedded data. -/
theorem spectral_runtime_operations :
    (∀ application map invariant,
      evalRuntimePrimitive (.spectralInvariant application map invariant) [] = some (.smooth (.primitive map))) ∧
    (∀ smooth (spectrum : SpectrumRef) element (point : SmoothRuntime.Program),
      evalRuntimePrimitive (.annihilates smooth spectrum element) [.smooth point] =
        some (.boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element point))) ∧
    (∀ smooth (spectrum : SpectrumRef) element row column (point : SmoothRuntime.Program),
      evalRuntimePrimitive (.actionEntry smooth spectrum element row column) [.smooth point] =
        some (.pairInt (SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column).1
          (SpectralRuntime.actionEntry spectrum.endomorphism.rows element point row column).2)) ∧
    (∀ smooth line (branch : BranchRef) (point v : SmoothRuntime.Program),
      evalRuntimePrimitive (.onBranch smooth line branch) [.smooth point, .smooth v] =
        some (.boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic point v))) ∧
    (∀ smooth cotangent line (branch : BranchRef) (point v : SmoothRuntime.Program),
      evalRuntimePrimitive (.branchDifferential smooth cotangent line branch) [.smooth point, .smooth v] =
        some (.fiber (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic point v))) ∧
    (∀ smooth line (branch : BranchRef) row column (point v : SmoothRuntime.Program),
      evalRuntimePrimitive (.branchProjector smooth line branch row column) [.smooth point, .smooth v] =
        some (.pairInt
          (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
            point v row column).1
          (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
            point v row column).2)) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

open VastitasOracle.SmoothReverse (environment_free) in
/-- **Spectral bindings read no declaration when they evaluate.** Every
spectral binding evaluates the same in every pair of environments: it reads
its embedded data, not the declarations. -/
theorem spectral_bindings_environment_free (env env' : Indexed.Environment) (values : List Value) :
    (∀ application map invariant, evalPrimitive env (.spectralInvariant application map invariant) values =
      evalPrimitive env' (.spectralInvariant application map invariant) values) ∧
    (∀ smooth spectrum element, evalPrimitive env (.annihilates smooth spectrum element) values =
      evalPrimitive env' (.annihilates smooth spectrum element) values) ∧
    (∀ smooth spectrum element row column, evalPrimitive env (.actionEntry smooth spectrum element row column) values =
      evalPrimitive env' (.actionEntry smooth spectrum element row column) values) ∧
    (∀ smooth line branch, evalPrimitive env (.onBranch smooth line branch) values =
      evalPrimitive env' (.onBranch smooth line branch) values) ∧
    (∀ smooth cotangent line branch, evalPrimitive env (.branchDifferential smooth cotangent line branch) values =
      evalPrimitive env' (.branchDifferential smooth cotangent line branch) values) ∧
    (∀ smooth line branch row column, evalPrimitive env (.branchProjector smooth line branch row column) values =
      evalPrimitive env' (.branchProjector smooth line branch row column) values) := by
  refine ⟨fun _ _ _ => environment_free ?_ env env' values, fun _ _ _ => environment_free ?_ env env' values,
    fun _ _ _ _ _ => environment_free ?_ env env' values, fun _ _ _ => environment_free ?_ env env' values,
    fun _ _ _ _ => environment_free ?_ env env' values, fun _ _ _ _ _ => environment_free ?_ env env' values⟩
  · intro _ _ _ _ h
    obtain ⟨rfl, rfl⟩ := spectralInvariant_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, rfl, rfl⟩ := annihilates_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, rfl, rfl⟩ := actionEntry_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := onBranch_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := branchDifferential_inv h
    rfl
  · intro _ _ _ _ h
    obtain ⟨_, _, rfl, rfl⟩ := branchProjector_inv h
    rfl

/-! ## The derivative rule of an invariant -/

/-- The derivative rule of a declared spectral invariant is `morphism` with
its own map. -/
theorem spectralInvariant_rule {env : Declarations} {id : DeclId} {application : Application}
    {map : AlgebraRuntime.Map} {invariant : SpectralInvariant}
    (found : env.primitive? id = some (.spectralInvariant application map invariant)) :
    Reverse.ruleOf env id = .morphism map := by
  simp [Reverse.ruleOf, found, PrimitiveBinding.contract, SpectralRegistry.spectralInvariant,
    PrimitiveDescriptor.ofBool]

/-- **A compiled reverse step along an invariant is the Stage 3
`cotangentJacobian` of the invariant's map.** In a compiled module, a declared
step of an entry whose morphism is a spectral invariant declaration has the
invariant's own map, and the step's declaration is the binding
`cotangentJacobian` of that map. -/
theorem compiled_invariant_step {requireMain : Bool} {source : Core.Typing.CheckedModule requireMain}
    (compiled : Reverse.Compiled source) {entry : Reverse.Entry} (member : entry ∈ compiled.entries)
    {step : Reverse.Step} (stepMember : step ∈ entry.site.steps) {morphism : DeclId} {stepApplication : Application}
    {stepMap : AlgebraRuntime.Map} (kind : step.kind = .declared morphism stepApplication stepMap)
    {application : Application} {map : AlgebraRuntime.Map} {invariant : SpectralInvariant}
    (found : compiled.core.module.declarations.primitive? morphism = some (.spectralInvariant application map invariant)) :
    stepMap = map ∧ Reverse.stepBinding entry.site step.kind = .cotangentJacobian entry.site.cotangent stepApplication map := by
  have morphisms := (SmoothReverseCompiled.entry_well_formed compiled member).morphisms step stepMember morphism
    stepApplication stepMap kind
  rw [spectralInvariant_rule found] at morphisms
  cases morphisms
  exact ⟨rfl, by rw [kind]; rfl⟩

/-! ## Accepted Core nodes

Each theorem below assumes an accepted Core node, operand terms that
evaluate, and typed operand values, as `SmoothReverse.core_cotangent_pullback`
does, and concludes with the embedded declaration, the operand values, the
node's value one unit of fuel later and the lengths of the operand points. -/

section Accepted

variable {module : Module} {functions : Core.Typing.Signatures} {ctx : Core.Typing.Context} {world : World}
  {fuel : Nat} {values : Values} {id : DeclId} {result : Result} {operands : List ValueType}
  {output : ValueType}

/-- **An invariant on accepted Core.** An accepted `trace_power(H, k)` or
`char_coefficient(S, i)` node evaluates to its declared map as one program
node, of the node's checked type `Smooth<X, Line>`. -/
theorem core_spectral_invariant {application : Application} {map : AlgebraRuntime.Map}
    {invariant : SpectralInvariant}
    (found : module.declarations.primitive? id = some (.spectralInvariant application map invariant))
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [] result)) :
    output = .indexed application ∧ spectralInvariantValid module.declarations.indexed application map invariant = true ∧
      eval module (fuel + 1) values (.primitive id [] result) = some (.indexed (.smooth (.primitive map))) ∧
      PrimitiveValueHasType module.declarations.indexed world (.indexed (.smooth (.primitive map))) output := by
  have input : (([] : List Core.Term).map Core.Term.result).mapM Result.primitiveType? = some [] := rfl
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [] result _ [] output found
    input outputType accepted
  have valid : spectralInvariantValid module.declarations.indexed application map invariant = true := rule.bindingValid
  have resultEq := SpectralPrimitives.spectralInvariant_association.mp rule.association
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    (world := world) found input outputType accepted rfl trivial (by intro _ h; cases h)
  obtain ⟨-, rfl⟩ := spectralInvariant_inv primitive
  exact ⟨resultEq.symm, valid, evaluated, valueTyped⟩

/-- **The module action on accepted Core.** An accepted
`annihilates(p, spectrum = S, element = f)` evaluates to
`SpectralRuntime.annihilates H f p` with the declared rows `H` of `S`'s
endomorphism; `f` is a canonical element of `A[t]`. -/
theorem core_spectral_annihilates {point : Core.Term} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {pointValue : Value}
    (found : module.declarations.primitive? id = some (.annihilates smooth spectrum element))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    DeclaredSpectrum module.declarations.indexed spectrum ∧ output = .boolean ∧
      ∃ m x, smoothDimension? module.declarations.indexed spectrum.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ (SmoothRuntime.coordinates x).length = m ∧
        AlgebraRuntime.Poly.canonical (m + 1) element = true ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.boolean (SpectralRuntime.annihilates spectrum.endomorphism.rows element x)) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point] result _ operands
    output found input outputType accepted
  have valid : annihilatesValid module.declarations.indexed smooth spectrum element = true := rule.bindingValid
  unfold annihilatesValid at valid
  simp only [Bool.and_eq_true] at valid
  obtain ⟨⟨hsmooth, hdeclared⟩, helement⟩ := valid
  obtain ⟨p, rfl⟩ := SpectralPrimitives.annihilates_shape rule.association
  obtain ⟨-, -, pointZero, resultEq⟩ := SpectralPrimitives.annihilates_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval]) typed (by intro _ h; cases h)
  obtain ⟨x, shapes, rfl⟩ := annihilates_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  obtain ⟨program, n, valueEq, hx, welltyped⟩ :=
    SmoothFibers.point_value (SmoothPrimitives.smooth_family hsmooth) pointZero typed.1
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at valueEq
  subst valueEq
  have hcanonical : AlgebraRuntime.Poly.canonical (n + 1) element = true := by
    unfold spectralElementValid at helement
    rw [hx] at helement
    exact helement
  exact ⟨declaredSpectrum_of_spectrumDeclared hdeclared, resultEq.symm, n, x, hx, rfl,
    SmoothFibers.coordinates_length welltyped, hcanonical, evaluated⟩

/-- **An entry of the module action on accepted Core.** An accepted
`action_entry(p, spectrum = S, element = f, eᵢ, eⱼ)` evaluates to the entry
`(i, j)` of `f(H(p))`, with `i, j` below the rank. -/
theorem core_spectral_action_entry {point : Core.Term} {smooth : DeclId} {spectrum : SpectrumRef}
    {element : AlgebraRuntime.Poly} {row column : Nat} {pointValue : Value}
    (found : module.declarations.primitive? id = some (.actionEntry smooth spectrum element row column))
    (input : ([point].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point] result))
    (pointEval : eval module fuel values point = some pointValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue] operands) :
    DeclaredSpectrum module.declarations.indexed spectrum ∧ output = .integerPair ∧
      row < spectrum.rank ∧ column < spectrum.rank ∧
      ∃ m x, smoothDimension? module.declarations.indexed spectrum.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ (SmoothRuntime.coordinates x).length = m ∧
        AlgebraRuntime.Poly.canonical (m + 1) element = true ∧
        eval module (fuel + 1) values (.primitive id [point] result) =
          some (.pairInt (SpectralRuntime.actionEntry spectrum.endomorphism.rows element x row column).1
            (SpectralRuntime.actionEntry spectrum.endomorphism.rows element x row column).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point] result _ operands
    output found input outputType accepted
  have valid : actionEntryValid module.declarations.indexed smooth spectrum element row column = true :=
    rule.bindingValid
  unfold actionEntryValid annihilatesValid at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨⟨hsmooth, hdeclared⟩, helement⟩, hrow⟩, hcolumn⟩ := valid
  obtain ⟨p, rfl⟩ := SpectralPrimitives.actionEntry_shape rule.association
  obtain ⟨-, -, pointZero, resultEq⟩ := SpectralPrimitives.actionEntry_association.mp rule.association
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval]) typed (by intro _ h; cases h)
  obtain ⟨x, shapes, rfl⟩ := actionEntry_inv primitive
  simp only [List.cons.injEq, and_true] at shapes
  subst shapes
  obtain ⟨program, n, valueEq, hx, welltyped⟩ :=
    SmoothFibers.point_value (SmoothPrimitives.smooth_family hsmooth) pointZero typed.1
  simp only [Value.indexed.injEq, IndexedValue.smooth.injEq] at valueEq
  subst valueEq
  have hcanonical : AlgebraRuntime.Poly.canonical (n + 1) element = true := by
    unfold spectralElementValid at helement
    rw [hx] at helement
    exact helement
  exact ⟨declaredSpectrum_of_spectrumDeclared hdeclared, resultEq.symm, hrow, hcolumn, n, x, hx, rfl,
    SmoothFibers.coordinates_length welltyped, hcanonical, evaluated⟩

/-- The two operands of a branch observation: a point of the branch's object
with its coordinates, and a value with one coordinate. -/
theorem branch_operands {env : Indexed.Environment} {smooth line point : DeclId} {p : Indexed.ObjectRef}
    {branch : BranchRef} {pointValue valueValue : Value}
    (hsmooth : isSmoothFamily env smooth = true) (hline : smoothDimension? env line = some 1)
    (pointZero : smoothDimension? env point = some 0) (hp : .global point = p)
    (typed : PrimitiveValuesHaveTypes env world [pointValue, valueValue]
      [.indexed ⟨smooth, [.object (.global point), .object (.global branch.object)]⟩,
        .indexed ⟨smooth, [.object p, .object (.global line)]⟩]) :
    ∃ m x v, smoothDimension? env branch.object = some m ∧ pointValue = .indexed (.smooth x) ∧
      valueValue = .indexed (.smooth v) ∧ x.wellTyped 0 m = true ∧
      (SmoothRuntime.coordinates x).length = m ∧ (SmoothRuntime.coordinates v).length = 1 := by
  subst hp
  have representation := SmoothPrimitives.smooth_family hsmooth
  obtain ⟨x, m, rfl, hm, hx⟩ := SmoothFibers.point_value representation pointZero typed.1
  obtain ⟨v, source, target, n, k, rfl, indices, hsource, htarget, hv⟩ :=
    SmoothPrimitives.smooth_value representation typed.2.1
  simp only [List.cons.injEq, Index.object.injEq, ObjectRef.global.injEq, and_true] at indices
  obtain ⟨rfl, rfl⟩ := indices
  rw [pointZero, Option.some.injEq] at hsource
  rw [hline, Option.some.injEq] at htarget
  subst hsource htarget
  exact ⟨m, x, v, hm, rfl, rfl, hx, SmoothFibers.coordinates_length hx, SmoothFibers.coordinates_length hv⟩

/-- **`on_branch` on accepted Core.** An accepted `on_branch(p, t, branch = B)`
evaluates to `SpectralRuntime.onBranch g χ p t` with the declared
localization `g` of `B` and `χ` of its spectrum. -/
theorem core_spectral_on_branch {point valueTerm : Core.Term} {smooth line : DeclId} {branch : BranchRef}
    {pointValue valueValue : Value}
    (found : module.declarations.primitive? id = some (.onBranch smooth line branch))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue] operands) :
    DeclaredBranch module.declarations.indexed branch ∧ output = .boolean ∧
      ∃ m x v, smoothDimension? module.declarations.indexed branch.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧
        (SmoothRuntime.coordinates x).length = m ∧ (SmoothRuntime.coordinates v).length = 1 ∧
        eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
          some (.boolean (SpectralRuntime.onBranch branch.localize branch.spectrum.characteristic x v)) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point, valueTerm] result _
    operands output found input outputType accepted
  have valid : onBranchValid module.declarations.indexed smooth line branch = true := rule.bindingValid
  unfold onBranchValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨hsmooth, hline⟩, hdeclared⟩ := valid
  obtain ⟨pointId, p, rfl⟩ := SpectralPrimitives.onBranch_shape rule.association
  obtain ⟨-, -, -, -, hp, pointZero, resultEq⟩ := SpectralPrimitives.onBranch_association.mp rule.association
  obtain ⟨m, x, v, hm, rfl, rfl, -, hx, hv⟩ := branch_operands hsmooth hline pointZero hp typed
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval, valueEval]) typed (by intro _ h; cases h)
  obtain ⟨x', v', shapes, rfl⟩ := onBranch_inv primitive
  simp only [List.cons.injEq, Value.indexed.injEq, IndexedValue.smooth.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨declaredBranch_of_branchDeclared hdeclared, resultEq.symm, m, x, v, hm, rfl, rfl, hx, hv, evaluated⟩

/-- **The branch differential on accepted Core.** An accepted
`branch_differential(p, t, branch = B)` evaluates to the covector
`SpectralRuntime.branchDifferential g χ p t` over the branch's object, with the
declared data of `B`, and the value has the node's checked type. -/
theorem core_spectral_branch_differential {point valueTerm : Core.Term} {smooth cotangent line : DeclId}
    {branch : BranchRef} {pointValue valueValue : Value}
    (found : module.declarations.primitive? id = some (.branchDifferential smooth cotangent line branch))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue] operands) :
    DeclaredBranch module.declarations.indexed branch ∧
      output = .indexed ⟨cotangent, [.object (.global branch.object)]⟩ ∧
      ∃ m x v, smoothDimension? module.declarations.indexed branch.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧
        (SmoothRuntime.coordinates x).length = m ∧ (SmoothRuntime.coordinates v).length = 1 ∧
        eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
          some (.indexed (.fiber .cotangent
            (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic x v))) ∧
        PrimitiveValueHasType module.declarations.indexed world
          (.indexed (.fiber .cotangent
            (SpectralRuntime.branchDifferential branch.localize branch.spectrum.characteristic x v))) output := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point, valueTerm] result _
    operands output found input outputType accepted
  have valid : branchDifferentialValid module.declarations.indexed smooth cotangent line branch = true :=
    rule.bindingValid
  unfold branchDifferentialValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq] at valid
  obtain ⟨⟨⟨⟨hsmooth, _⟩, hline⟩, hdeclared⟩, _⟩ := valid
  obtain ⟨pointId, p, rfl⟩ := SpectralPrimitives.branchDifferential_shape rule.association
  obtain ⟨-, -, -, -, hp, pointZero, resultEq⟩ :=
    SpectralPrimitives.branchDifferential_association.mp rule.association
  obtain ⟨m, x, v, hm, rfl, rfl, -, hx, hv⟩ := branch_operands hsmooth hline pointZero hp typed
  obtain ⟨value, primitive, evaluated, valueTyped⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval, valueEval]) typed (by intro _ h; cases h)
  obtain ⟨x', v', shapes, rfl⟩ := branchDifferential_inv primitive
  simp only [List.cons.injEq, Value.indexed.injEq, IndexedValue.smooth.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨declaredBranch_of_branchDeclared hdeclared, resultEq.symm, m, x, v, hm, rfl, rfl, hx, hv, evaluated,
    valueTyped⟩

/-- **The eigenprojector on accepted Core.** An accepted
`branch_projector(p, t, branch = B, eᵢ, eⱼ)` evaluates to the entry `(i, j)`
of the eigenprojector, `SpectralRuntime.projectorEntry g χ adj p t i j`, with
the declared data of `B`, and `i, j` below the rank. -/
theorem core_spectral_branch_projector {point valueTerm : Core.Term} {smooth line : DeclId} {branch : BranchRef}
    {row column : Nat} {pointValue valueValue : Value}
    (found : module.declarations.primitive? id = some (.branchProjector smooth line branch row column))
    (input : ([point, valueTerm].map Core.Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (accepted : Core.Typing.HasType module.declarations functions ctx (.primitive id [point, valueTerm] result))
    (pointEval : eval module fuel values point = some pointValue)
    (valueEval : eval module fuel values valueTerm = some valueValue)
    (typed : PrimitiveValuesHaveTypes module.declarations.indexed world [pointValue, valueValue] operands) :
    DeclaredBranch module.declarations.indexed branch ∧ output = .integerPair ∧
      row < branch.spectrum.rank ∧ column < branch.spectrum.rank ∧
      ∃ m x v, smoothDimension? module.declarations.indexed branch.object = some m ∧
        pointValue = .indexed (.smooth x) ∧ valueValue = .indexed (.smooth v) ∧
        (SmoothRuntime.coordinates x).length = m ∧ (SmoothRuntime.coordinates v).length = 1 ∧
        eval module (fuel + 1) values (.primitive id [point, valueTerm] result) =
          some (.pairInt
            (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
              x v row column).1
            (SpectralRuntime.projectorEntry branch.localize branch.spectrum.characteristic branch.spectrum.adjugate
              x v row column).2) := by
  have rule := IndexedCore.typed_primitive_contract module.declarations functions ctx id [point, valueTerm] result _
    operands output found input outputType accepted
  have valid : branchProjectorValid module.declarations.indexed smooth line branch row column = true :=
    rule.bindingValid
  unfold branchProjectorValid onBranchValid at valid
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at valid
  obtain ⟨⟨⟨⟨hsmooth, hline⟩, hdeclared⟩, hrow⟩, hcolumn⟩ := valid
  obtain ⟨pointId, p, rfl⟩ := SpectralPrimitives.branchProjector_shape rule.association
  obtain ⟨-, -, -, -, hp, pointZero, resultEq⟩ := SpectralPrimitives.branchProjector_association.mp rule.association
  obtain ⟨m, x, v, hm, rfl, rfl, -, hx, hv⟩ := branch_operands hsmooth hline pointZero hp typed
  obtain ⟨value, primitive, evaluated, -⟩ := SmoothReverse.core_outcome (fuel := fuel) (values := values)
    found input outputType accepted (by simp [pointEval, valueEval]) typed (by intro _ h; cases h)
  obtain ⟨x', v', shapes, rfl⟩ := branchProjector_inv primitive
  simp only [List.cons.injEq, Value.indexed.injEq, IndexedValue.smooth.injEq, and_true] at shapes
  obtain ⟨rfl, rfl⟩ := shapes
  exact ⟨declaredBranch_of_branchDeclared hdeclared, resultEq.symm, hrow, hcolumn, m, x, v, hm, rfl, rfl, hx, hv,
    evaluated⟩

end Accepted

end VastitasOracle.SpectralCore
