import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the frame declarations of the finite frame profile (Stage 4,
#759).

A frame `Frame<X>` is an ordered basis of every tangent fiber of a smooth
object `X`: an invertible matrix `P` of polynomials in the coordinates of `X`,
given as rows, with its inverse `Q`. `Entry.Valid` (`IndexedValidity`) calls
`checkFrame` for every frame declaration.

Not implemented yet: `checkFrame` rejects every frame, so no environment with
a frame declaration is valid. -/
namespace VastitasKernel.FrameDeclarations

open VastitasKernel.Indexed

/-- The frame declaration `frame family object matrix inverse`. It rejects
every frame until the frame checks are implemented. -/
def checkFrame (_env : Environment) (_family _object : DeclId) (_matrix _inverse : PolyMatrix) : Bool :=
  false

end VastitasKernel.FrameDeclarations
