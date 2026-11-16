import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the declarations of `nature::model` (Stage 6, #841; ADR 0002
§4).

- A convention states how a model writes its physical quantities. The profile
  has one, `hbar_one`: energies are angular frequencies, `ħ = 1`.
- A model `Model<X>` names a symmetric endomorphism field `H` on the smooth
  object `X`, a reading of `X`, a convention, a prepared and an observed basis
  vector of the free module of `H`, the transition average that it predicts
  and its regime. The check is that the references fit: the reading is a
  reading of `X`, both basis vectors belong to the module of `H`, and the
  predicted average is the average of a branch of a spectrum of `H` from the
  prepared to the observed vector. The regime is a recorded assumption, which
  no check proves.

A convention and a model compute nothing: they change no value, no validity
and no generated code of a `std` declaration. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration.

Not implemented yet: every check rejects, so no environment with a convention
or a model is valid. -/
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

/-- The convention declaration `convention value`. It rejects every
convention until the checks of `nature::model` are implemented. -/
def checkConvention (_env : Environment) (_value : Convention) : Bool :=
  false

/-- The model declaration `model family object hamiltonian reading convention
prepare observe predicts regime`. It rejects every model until the checks of
`nature::model` are implemented. -/
def checkModel (_env : Environment) (_family _object _hamiltonian _reading _convention : DeclId)
    (_prepare _observe : Nat) (_predicts : DeclId) (_regime : String) : Bool :=
  false

end VastitasKernel.NatureModel
