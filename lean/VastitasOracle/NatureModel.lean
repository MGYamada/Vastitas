import VastitasKernel.NatureModel
import VastitasOracle.SpectralAverage

set_option autoImplicit false

/-! Oracle theorems about the declarations of `nature::model` (Stage 6, #841;
ADR 0002 §4): what an accepted convention and an accepted model
(`NatureModel.checkConvention`, `NatureModel.checkModel`) guarantee about
their references. Mathlib-free.

* **Conventions** (`checkConvention_true`): every convention declaration is
  valid; the decoder admits only `hbar_one`.
* **The references of a model** (`predictsAverage_sound`, `checkModel_sound`):
  an accepted model names an endomorphism field `H` on its object `X`,
  `prepare` and `observe` are indices of the basis of `H`'s free module, the
  reading is a reading of `X`, the convention is a convention declaration,
  and `predicts` is a transition average on `X` from `prepare` to `observe`
  of a branch of a spectrum of `H`.
* **In a valid environment** (`model_sound`): moreover the free module of `H`
  is on `X`, `H` is symmetric, its `n × n` rows have `n` the rank of that
  module, and the predicted average satisfies `AverageValid` with `H`'s rows,
  the certificate of the branch's spectrum and the branch's gap certificate,
  from `prepare` to `observe`: the model predicts the transition average of
  its own field between its own basis vectors
  (`SpectralAverage.AverageValid.value_at` gives its value on the chart).
* **The regime is recorded, not checked** (`checkModel_regime_free`): the
  check of a model does not read its regime, an Assumed text.

That the field, the prepared and observed vectors and the regime describe an
experiment is a statement about the world (ADR 0002 §4), not a theorem.
Models and conventions change no `std` validity and no value
(`NatureWeakening`). -/
namespace VastitasOracle.NatureModel

open VastitasKernel VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.NatureModel (checkConvention checkModel predictsAverage)
open VastitasOracle.SpectralDeclarations (SpectralValid WitnessValid)
open VastitasOracle.SpectralAverage (AverageValid)

/-- **Every convention is valid**: `hbar_one` is the only convention of the
profile, and the decoder admits no other. -/
theorem checkConvention_true (env : Environment) (value : Convention) : checkConvention env value = true := rfl

/-- **The predicted average.** `predictsAverage` holds exactly for a
transition average on the object, from `prepare` to `observe`, of a branch of
a spectrum of `hamiltonian`. -/
theorem predictsAverage_sound {env : Environment} {object hamiltonian predicts : DeclId} {prepare observe : Nat}
    (h : predictsAverage env object hamiltonian prepare observe predicts = true) :
    ∃ averageFamily branch numerator denominator certificate,
      transitionAverageData? env predicts =
        some (averageFamily, object, branch, prepare, observe, numerator, denominator, certificate) ∧
      ∃ branchFamily branchObject spectrum localize witness exponent quotient,
        branchData? env branch = some (branchFamily, branchObject, spectrum, localize, witness, exponent, quotient) ∧
        ∃ spectrumFamily spectrumObject fiber spectral,
          spectrumData? env spectrum = some (spectrumFamily, spectrumObject, hamiltonian, fiber, spectral) := by
  unfold predictsAverage at h
  cases ha : transitionAverageData? env predicts with
  | none => rw [ha] at h; cases h
  | some data =>
    obtain ⟨averageFamily, averageObject, branch, source, target, numerator, denominator, certificate⟩ := data
    rw [ha] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hobject, hsource⟩, htarget⟩, hrest⟩ := h
    subst hobject hsource htarget
    cases hb : branchData? env branch with
    | none => rw [hb] at hrest; cases hrest
    | some bdata =>
      obtain ⟨branchFamily, branchObject, spectrum, localize, witness, exponent, quotient⟩ := bdata
      rw [hb] at hrest
      dsimp only at hrest
      cases hs : spectrumData? env spectrum with
      | none => rw [hs] at hrest; cases hrest
      | some sdata =>
        obtain ⟨spectrumFamily, spectrumObject, endomorphism, fiber, spectral⟩ := sdata
        rw [hs] at hrest
        dsimp only at hrest
        simp only [beq_iff_eq] at hrest
        subst hrest
        exact ⟨averageFamily, branch, numerator, denominator, certificate, rfl, branchFamily, branchObject, spectrum,
          localize, witness, exponent, quotient, hb, spectrumFamily, spectrumObject, fiber, spectral, hs⟩

/-- **The references of an accepted model** (C4). Its family is a `model`
family applied to a declared smooth object `X`; `hamiltonian` is an
endomorphism on `X` whose free module has `prepare` and `observe` among the
indices of its basis; `reading` is a reading of `X`; `convention` is a
convention declaration; and `predicts` is a transition average on `X` from
`prepare` to `observe` of a branch of a spectrum of `hamiltonian`. -/
theorem checkModel_sound {env : Environment} {family object hamiltonian reading convention predicts : DeclId}
    {prepare observe : Nat} {regime : String}
    (h : checkModel env family object hamiltonian reading convention prepare observe predicts regime = true) :
    isModelFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      (smoothDimension? env object).isSome = true ∧
      (∃ hamiltonianFamily module rows symmetric,
        endomorphismData? env hamiltonian = some (hamiltonianFamily, object, module, rows, symmetric) ∧
        ∃ moduleFamily moduleObject basis, freeModuleData? env module = some (moduleFamily, moduleObject, basis) ∧
          prepare < basis.length ∧ observe < basis.length) ∧
      (∃ readingFamily quantities, readingData? env reading = some (readingFamily, object, quantities)) ∧
      (∃ value, conventionData? env convention = some value) ∧
      predictsAverage env object hamiltonian prepare observe predicts = true := by
  simp only [checkModel, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hdeclared, hhamiltonian⟩, hreading⟩, hconvention⟩, hpredicts⟩ := h
  obtain ⟨hfamily, happ, hdimension⟩ := SpectralDeclarations.declaredAt_spec hdeclared
  refine ⟨hfamily, happ, hdimension, ?_, ?_, ?_, hpredicts⟩
  · cases he : endomorphismData? env hamiltonian with
    | none => rw [he] at hhamiltonian; cases hhamiltonian
    | some data =>
      obtain ⟨hamiltonianFamily, hamiltonianObject, module, rows, symmetric⟩ := data
      rw [he] at hhamiltonian
      simp only [Bool.and_eq_true, beq_iff_eq] at hhamiltonian
      obtain ⟨hobject, hmodule⟩ := hhamiltonian
      subst hobject
      cases hm : freeModuleData? env module with
      | none => rw [hm] at hmodule; cases hmodule
      | some mdata =>
        obtain ⟨moduleFamily, moduleObject, basis⟩ := mdata
        rw [hm] at hmodule
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hmodule
        exact ⟨hamiltonianFamily, module, rows, symmetric, rfl, moduleFamily, moduleObject, basis, hm, hmodule.1,
          hmodule.2⟩
  · cases hr : readingData? env reading with
    | none => rw [hr] at hreading; cases hreading
    | some data =>
      obtain ⟨readingFamily, readingObject, quantities⟩ := data
      rw [hr] at hreading
      simp only [beq_iff_eq] at hreading
      subst hreading
      exact ⟨readingFamily, quantities, rfl⟩
  · cases hc : conventionData? env convention with
    | none => rw [hc] at hconvention; cases hconvention
    | some value => exact ⟨value, rfl⟩

/-- **The regime is recorded, not checked.** The check of a model does not
read its regime: the regime is an Assumed text. -/
theorem checkModel_regime_free (env : Environment) (family object hamiltonian reading convention predicts : DeclId)
    (prepare observe : Nat) (regime regime' : String) :
    checkModel env family object hamiltonian reading convention prepare observe predicts regime =
      checkModel env family object hamiltonian reading convention prepare observe predicts regime' := rfl

/-- **Models of a valid environment** (C4). A declared model on `X` names
an endomorphism `H` on `X` with symmetric rows, whose free module is on `X`
and has the rank of `H` and `prepare`, `observe` among its basis indices; a
reading of `X`; a convention; and a predicted transition average on `X`,
from `prepare` to `observe`, of a branch on `X` of a spectrum of `H`, whose
certificate is valid for the rows of `H`, whose gap certificate is valid, and
whose closed form satisfies `AverageValid` with that data. -/
theorem model_sound {env : Environment} (envValid : env.Valid)
    {id family object hamiltonian reading convention predicts : DeclId} {prepare observe : Nat} {regime : String}
    (found : lookup env id =
      some (.model family object hamiltonian reading convention prepare observe predicts regime)) :
    isModelFamily env family = true ∧ validApplication env ⟨family, [.object (.global object)]⟩ = true ∧
      ∃ implementation coordinates hamiltonianFamily module rows moduleFamily basis,
        lookup env object = some (.smoothAffine implementation coordinates) ∧
        endomorphismData? env hamiltonian = some (hamiltonianFamily, object, module, rows, true) ∧
        freeModuleData? env module = some (moduleFamily, object, basis) ∧
        rows.length = basis.length ∧ prepare < basis.length ∧ observe < basis.length ∧
        (∃ readingFamily quantities, readingData? env reading = some (readingFamily, object, quantities)) ∧
        (∃ value, conventionData? env convention = some value) ∧
        ∃ averageFamily branch numerator denominator certificate branchFamily spectrum localize witness exponent
          quotient spectrumFamily fiber spectral,
          transitionAverageData? env predicts =
            some (averageFamily, object, branch, prepare, observe, numerator, denominator, certificate) ∧
          branchData? env branch = some (branchFamily, object, spectrum, localize, witness, exponent, quotient) ∧
          spectrumData? env spectrum = some (spectrumFamily, object, hamiltonian, fiber, spectral) ∧
          SpectralValid coordinates.length rows spectral ∧
          WitnessValid coordinates.length rows.length spectral.characteristic localize witness exponent quotient ∧
          AverageValid coordinates.length rows spectral.characteristic spectral.adjugate localize witness exponent
            prepare observe numerator denominator certificate := by
  have valid := SpectralDeclarations.valid_of_lookup envValid found
  obtain ⟨hfamily, happ, -, ⟨hamiltonianFamily, module, rows, symmetric, he, moduleFamily, moduleObject, basis, hm,
    hprepare, hobserve⟩, hreading, hconvention, hpredicts⟩ := checkModel_sound valid
  obtain ⟨averageFamily, branch, numerator, denominator, certificate, ha, branchFamily, branchObject, spectrum,
    localize, witness, exponent, quotient, hb, spectrumFamily, spectrumObject, fiber, spectral, hs⟩ :=
    predictsAverage_sound hpredicts
  obtain ⟨-, -, implementation, coordinates, branchFamily', spectrum', localize', witness', exponent', quotient',
    spectrumFamily', endomorphism, fiber', spectral', endomorphismFamily, module', rows', hobject, hb', hs', he', hv,
    hw, haverage⟩ := SpectralAverage.transitionAverage_sound envValid (SpectralAverage.transitionAverageData_lookup ha)
  rw [hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb'
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨-, rfl, rfl, -, rfl⟩ := hs'
  rw [he] at he'
  simp only [Option.some.injEq, Prod.mk.injEq] at he'
  obtain ⟨-, -, rfl, rfl, rfl⟩ := he'
  obtain ⟨-, -, implementation', coordinates', moduleFamily', basis', hobject', hmodule', -, hsquare, -⟩ :=
    SpectralDeclarations.endomorphism_sound envValid (SpectralAverage.endomorphism_lookup he)
  rw [hm] at hmodule'
  simp only [Option.some.injEq, Prod.mk.injEq] at hmodule'
  obtain ⟨-, rfl, rfl⟩ := hmodule'
  have hlength := (VastitasOracle.SpectralAlgebra.squareOf_spec hsquare).1
  exact ⟨hfamily, happ, implementation, coordinates, hamiltonianFamily, module, rows, moduleFamily, basis, hobject,
    he, hm, hlength, hprepare, hobserve, hreading, hconvention, averageFamily, branch, numerator, denominator,
    certificate, branchFamily, spectrum, localize, witness, exponent, quotient, spectrumFamily, fiber, spectral, ha, hb,
    hs, hv, hw, haverage⟩

end VastitasOracle.NatureModel
