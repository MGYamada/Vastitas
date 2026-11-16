import VastitasKernel.SpectralDeclarations

set_option autoImplicit false

/-! Checks for the declarations of `nature::model` (Stage 6, #841; ADR 0002
§4).

- A convention states how a model writes its physical quantities. The profile
  has one, `hbar_one`: energies are angular frequencies, `ħ = 1`. The decoder
  admits no other, so every convention declaration is valid
  (`checkConvention`).
- A model `Model<X>` names an endomorphism field `H` on the smooth object `X`,
  a reading of `X`, a convention, a prepared and an observed basis vector of
  the free module of `H`, the transition average that it predicts and its
  regime. `checkModel` checks that the references fit:
  1. the family is a `model` family applied to the declared smooth object `X`;
  2. `H` is an endomorphism declaration on `X`, and `prepare` and `observe`
     are indices of the basis of its free module;
  3. the reading is a reading declaration of `X`;
  4. the convention is a convention declaration;
  5. `predicts` is a transition average declaration on `X` of a branch of a
     spectrum of `H`, from `prepare` to `observe` (`predictsAverage`).
  The regime is a recorded assumption, which no check proves.

A convention and a model compute nothing: they change no value, no validity
and no generated code of a `std` declaration. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration. -/
namespace VastitasKernel.NatureModel

open VastitasKernel.Indexed

/-- Why a check of `nature::model` rejects. `code` is the diagnostic code: a
limit is `E_LIMIT`, everything else `E_MODEL`. -/
inductive Problem where
  /-- A declaration beyond a limit of the compiler. -/
  | limit (message : String)
  /-- A declaration that the rules of `nature::model` do not admit. -/
  | invalid (message : String)
  deriving Repr, Inhabited, DecidableEq

def Problem.code : Problem → String
  | .limit _ => "E_LIMIT"
  | .invalid _ => "E_MODEL"

def Problem.message : Problem → String
  | .limit message | .invalid message => message

/-- The convention declaration `convention value`. `hbar_one` is the only
convention of the profile, and the decoder admits no other. -/
def checkConvention (_env : Environment) (_value : Convention) : Bool :=
  true

/-- The transition average `predicts` is on `object`, of a branch of a
spectrum of `hamiltonian`, from the basis vector `prepare` to `observe`. -/
def predictsAverage (env : Environment) (object hamiltonian : DeclId) (prepare observe : Nat) (predicts : DeclId) :
    Bool :=
  match transitionAverageData? env predicts with
  | some (_, averageObject, branch, source, target, _, _, _) =>
    averageObject == object && source == prepare && target == observe &&
      match branchData? env branch with
      | some (_, _, spectrum, _, _, _, _) =>
        match spectrumData? env spectrum with
        | some (_, _, endomorphism, _, _) => endomorphism == hamiltonian
        | none => false
      | none => false
  | none => false

/-- The model declaration `model family object hamiltonian reading convention
prepare observe predicts regime`: the checks 1–5 of the module comment. -/
def checkModel (env : Environment) (family object hamiltonian reading convention : DeclId)
    (prepare observe : Nat) (predicts : DeclId) (_regime : String) : Bool :=
  SpectralDeclarations.declaredAt env (isModelFamily env family) family object &&
    (match endomorphismData? env hamiltonian with
      | some (_, hamiltonianObject, module, _, _) =>
        hamiltonianObject == object &&
          match freeModuleData? env module with
          | some (_, _, basis) => decide (prepare < basis.length) && decide (observe < basis.length)
          | none => false
      | none => false) &&
    (match readingData? env reading with
      | some (_, readingObject, _) => readingObject == object
      | none => false) &&
    (conventionData? env convention).isSome &&
    predictsAverage env object hamiltonian prepare observe predicts

end VastitasKernel.NatureModel
