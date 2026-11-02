import Lean

/-!
Kernel-checked finite Hodge reference for #375 / PR #404.

This is a deliberately small mathematical fragment: standard oriented Euclidean
rank three and Minkowski (-,+,+,+) rank four, with integral coefficients.
It verifies the defining wedge-pairing equation and square laws on complete
ordered basis sets by kernel reduction (`decide +kernel`, not `native_decide`).

NOT a universal C∞/scheme Hodge construction, scalar-extension theorem,
accepted source/Core binding, native-refinement proof, or physical clock claim.
The independent VastitasMath package and Bridge obligations remain #285.
-/

namespace VastitasOracle.HodgeFinite

/-- Coordinates on 1-forms in the ordered basis (dx,dy,dz). -/
abbrev One3 := Fin 3 → Int
/-- Coordinates on 2-forms in the oriented basis (dy∧dz,dz∧dx,dx∧dy). -/
abbrev Two3 := Fin 3 → Int

def basis3 (j : Fin 3) : One3 := fun i => if i == j then 1 else 0

/-- Euclidean star in the complement-oriented ordered bases. -/
def star3One (a : One3) : Two3 := fun i => a i
def star3Two (a : Two3) : One3 := fun i => a i

/-- The oriented top-form coefficient in α∧β. -/
def wedge3 (a : One3) (b : Two3) : Int :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2
/-- The standard Euclidean 1-form pairing. -/
def pair3 (a b : One3) : Int :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

theorem euclidean3_defining_basis :
    ∀ i : Fin 3, ∀ j : Fin 3,
      wedge3 (basis3 i) (star3One (basis3 j)) = pair3 (basis3 i) (basis3 j) := by
  decide +kernel

theorem euclidean3_square_basis :
    ∀ i : Fin 3, ∀ j : Fin 3,
      star3Two (star3One (basis3 i)) j = basis3 i j := by
  decide +kernel

/-- Reversing a chosen orientation negates the displayed star. -/
def reversedStar3One (a : One3) : Two3 := fun i => -(star3One a i)
def reversedStar3Two (a : Two3) : One3 := fun i => -(star3Two a i)

theorem euclidean3_reversed_square_basis :
    ∀ i : Fin 3, ∀ j : Fin 3,
      reversedStar3Two (reversedStar3One (basis3 i)) j = basis3 i j := by
  decide +kernel

/-- Ordered Lorentzian 2-forms: (dt∧dx,dt∧dy,dt∧dz,dx∧dy,dx∧dz,dy∧dz). -/
abbrev Two4 := Fin 6 → Int

def basis6 (j : Fin 6) : Two4 := fun i => if i == j then 1 else 0

/-- Oriented coefficient of α∧β in dt∧dx∧dy∧dz. -/
def wedge4 (a b : Two4) : Int :=
  a 0 * b 5 - a 1 * b 4 + a 2 * b 3 +
  a 3 * b 2 - a 4 * b 1 + a 5 * b 0

/-- Induced Λ²-pairing for the metric diag(-1,+1,+1,+1). -/
def pairLorentz (a b : Two4) : Int :=
  -(a 0 * b 0) - a 1 * b 1 - a 2 * b 2 +
  a 3 * b 3 + a 4 * b 4 + a 5 * b 5

/-- Hodge star on Λ² for the selected metric and orientation. -/
def starLorentz (a : Two4) : Two4 := fun i =>
  if i == 0 then a 5
  else if i == 1 then -(a 4)
  else if i == 2 then a 3
  else if i == 3 then -(a 2)
  else if i == 4 then a 1
  else -(a 0)

theorem lorentz4_defining_basis :
    ∀ i : Fin 6, ∀ j : Fin 6,
      wedge4 (basis6 i) (starLorentz (basis6 j)) =
        pairLorentz (basis6 i) (basis6 j) := by
  decide +kernel

/-- On 2-forms in signature (1,3), ⋆² = -id. -/
theorem lorentz4_square_basis :
    ∀ i : Fin 6, ∀ j : Fin 6,
      starLorentz (starLorentz (basis6 i)) j = -(basis6 i j) := by
  decide +kernel

theorem lorentz4_tdx_sign : starLorentz (basis6 0) 5 = -1 := by
  decide +kernel

/-- A Euclidean-sign substitution fails the chosen Minkowski profile. -/
theorem reject_euclidean_twoform_sign :
    starLorentz (basis6 0) 5 ≠ 1 := by
  decide +kernel

end VastitasOracle.HodgeFinite
