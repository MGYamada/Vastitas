import VastitasKernel.Runtime
import Init.Data.Rat.Lemmas

/-!
A small mathematical interpretation of the rational affine fragment. This is
only its coordinate space and admitted origin/identity, not an identification
of a scheme with its set of rational points. The constant-coordinate lemma is
an auxiliary mathematical fact; Stage 0 does not expose arbitrary coordinate
point constructors.
-/
namespace VastitasOracle.Coordinates

open VastitasKernel.Runtime

abbrev RationalCoordinates (object : Object) := Fin object.dimension → Rat

def denoteOrigin (dimension : Nat) :
    RationalCoordinates (origin (affine .qq dimension)).target := fun _ => 0

def denoteIdentity (dimension : Nat) :
    RationalCoordinates (idMap (affine .qq dimension)).source →
      RationalCoordinates (idMap (affine .qq dimension)).target := fun point => point

theorem identity_preserves_origin (dimension : Nat) :
    denoteIdentity dimension (denoteOrigin dimension) = denoteOrigin dimension := rfl

theorem origin_coordinates_are_zero (dimension : Nat) (coordinate : Fin dimension) :
    denoteOrigin dimension coordinate = 0 := rfl

def integerConstant (dimension : Nat) (value : Int) : Fin dimension → Rat := fun _ => value

/-- Exact integer constants remain distinct in nonempty rational coordinate spaces. -/
theorem integerConstant_injective (dimension : Nat) (nonempty : 0 < dimension) :
    Function.Injective (integerConstant dimension) := by
  intro left right equal
  apply Rat.intCast_inj.mp
  exact congrFun equal ⟨0, nonempty⟩

end VastitasOracle.Coordinates
