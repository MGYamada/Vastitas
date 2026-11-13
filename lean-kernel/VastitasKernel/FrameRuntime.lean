import VastitasKernel.SmoothRuntime

set_option autoImplicit false

/-! Exact runtime for frames of the tangent fibers of smooth affine objects
(Stage 4, #759).

A frame of an object of dimension `n` is given by two `n × n` matrices of
polynomials in the coordinates, as rows: `P`, whose column `j` is the `j`-th
frame vector in the coordinate frame, and its inverse `Q`. `matrixAt` evaluates
every entry at a point. The kernel checks `P · Q = Q · P = I` before code
generation; the functions below read the matrices they are given and check no
identity.

The coordinates of a vector or covector in a frame are a
`SmoothRuntime.Fiber`: a basepoint and components, here in the frame instead
of the coordinate frame. Arrays carry no frame at run time, so the frame
profile reads them with the smooth runtime's `vector`, `fiberAt`,
`fiberEqual`, `component` and `pairing`. A vector `v` at `p` has the array
`Q(p) v`, which decodes back as `P(p) a`; a covector `α` has the array
`P(p)ᵀ α`, which decodes back as `Q(p)ᵀ a`.

The matrix of a linear map between tangent fibers in two frames is a
`FrameMatrix`: the basepoints of its source and target and the entries, one
row per target component. `frameMatrix` takes the rows of the matrix of a
tangent map from the recomputing reverse pass of the program value that
checked Core builds; it neither expands the program nor forms a Jacobian.

`none` is the failure value; it is absorbing. A fiber whose point or
components do not have one entry per frame vector, an array over a point that
is not the source of a matrix, and two matrices whose middle points differ
give it.

Every definition here applies `List.map` and `List.range` to rows and
columns, and calls the smooth runtime. The rows, columns and coordinates are
at most the dimension of an object, 16, so `dot`, `List.getD` and
`monomialValue` recurse at most that often, and no definition needs a
replacement for compiled code. The deep recursions, over the nodes of a
program, the terms of a polynomial and the units of an exponent, are those of
`Program.eval`, `Program.reverse` and `evalAt`, whose `csimp` replacements
compiled code runs (#630). Exact rationals are not bounded here: their growth
inside `frameMatrix` is a recorded gap of Stage 4.

Generated programs import this module; it imports only the smooth runtime: no
compiler, oracle or mathlib module. -/
namespace VastitasKernel.FrameRuntime

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

/-- The matrix of a linear map `T_p X → T_q Y` in a frame of each fiber: the
source point `p`, the target point `q` and `target.length` rows of
`source.length` entries. -/
structure FrameMatrix where
  source : List Rat
  target : List Rat
  entries : SmoothRuntime.Matrix
  deriving Repr, DecidableEq, Inhabited

/-- A frame matrix, or the failure value `none`. -/
abbrev FrameMatrixValue := Option FrameMatrix

/-! ## Rational matrices -/

/-- Every entry of a matrix of polynomials, given as rows, at a point. -/
def matrixAt (matrix : List (List Poly)) (point : List Rat) : Matrix :=
  matrix.map fun row => row.map fun entry => evalAt entry point

/-- `Mᵀ v` for a matrix `M` with `columns` columns, given as rows: component
`j` is `Σᵢ vᵢ Mᵢⱼ`. The number of columns is explicit because a matrix with no
rows has columns too. -/
def transposeVec (columns : Nat) (matrix : Matrix) (vector : List Rat) : List Rat :=
  (List.range columns).map fun j => dot vector (matrix.map fun row => row.getD j 0)

/-- The product `L R` of two matrices, given as rows, for `R` with `columns`
columns: row `i` is `Rᵀ` applied to row `i` of `L`. Unfolded, it is
`SmoothDeclarations.matMul columns`, which the runtime does not import. -/
def matrixProduct (columns : Nat) (left right : Matrix) : Matrix :=
  left.map (transposeVec columns right)

/-! ## Encoding and decoding -/

/-- A fiber fits a frame of dimension `dimension` when its point and its
components have `dimension` entries each. -/
def fits (dimension : Nat) (fiber : Fiber) : Bool :=
  fiber.point.length == dimension && fiber.components.length == dimension

/-- The coordinates of a vector in the frame with inverse `Q`: `v ↦ Q(p) v`,
over the same point `p`. A fiber that does not fit the frame gives the failure
value. -/
def encodeTangent (inverse : List (List Poly)) (value : FiberValue) : FiberValue :=
  match value with
  | some fiber =>
    if fits inverse.length fiber then
      some ⟨fiber.point, matVec (matrixAt inverse fiber.point) fiber.components⟩
    else none
  | none => none

/-- The coordinates of a covector in the frame `P`: `α ↦ P(p)ᵀ α`, over the
same point `p`. A fiber that does not fit the frame gives the failure value. -/
def encodeCotangent (matrix : List (List Poly)) (value : FiberValue) : FiberValue :=
  match value with
  | some fiber =>
    if fits matrix.length fiber then
      some ⟨fiber.point,
        transposeVec matrix.length (matrixAt matrix fiber.point) fiber.components⟩
    else none
  | none => none

/-- The vector with coordinates `a` in the frame `P`: `a ↦ P(p) a`, over the
same point `p`, the inverse of `encodeTangent`. An array that does not fit the
frame gives the failure value. -/
def decodeTangent (matrix : List (List Poly)) (value : FiberValue) : FiberValue :=
  match value with
  | some fiber =>
    if fits matrix.length fiber then
      some ⟨fiber.point, matVec (matrixAt matrix fiber.point) fiber.components⟩
    else none
  | none => none

/-- The covector with coordinates `a` in the frame with inverse `Q`:
`a ↦ Q(p)ᵀ a`, over the same point `p`, the inverse of `encodeCotangent`. An
array that does not fit the frame gives the failure value. -/
def decodeCotangent (inverse : List (List Poly)) (value : FiberValue) : FiberValue :=
  match value with
  | some fiber =>
    if fits inverse.length fiber then
      some ⟨fiber.point,
        transposeVec inverse.length (matrixAt inverse fiber.point) fiber.components⟩
    else none
  | none => none

/-! ## Frame matrices -/

/-- The matrix of the tangent map of `map` at `point`, from the frame `P_b` of
its source to the frame of its target with inverse `Q_c`:
`⟨p, F(p), Q_c(F(p)) J(p) P_b(p)⟩`. Row `i` is `P_b(p)ᵀ (J(p)ᵀ ηᵢ)` for the
row `ηᵢ` of `Q_c(F(p))`, and `J(p)ᵀ ηᵢ` is the recomputing reverse pass of the
program value, the pass that `pullback` runs: one reverse run per row of the
result, on the program as checked Core builds it, with no expanded composite
and no Jacobian. A point or an image whose length is not the dimension of its
frame gives the failure value. -/
def frameMatrix (map point : Program) (sourceFrame targetInverse : List (List Poly)) :
    FrameMatrixValue :=
  let source := coordinates point
  let target := map.eval source
  if source.length == sourceFrame.length && target.length == targetInverse.length then
    let frame := matrixAt sourceFrame source
    some ⟨source, target, (matrixAt targetInverse target).map fun row =>
      transposeVec source.length frame (map.reverse source row)⟩
  else none

/-- The change from the frame `P_s` to the frame with inverse `Q_t`, two
frames of one object, at `point`: `⟨p, p, Q_t(p) P_s(p)⟩`. It sends the
coordinates of a vector in the first frame to its coordinates in the second.
A point whose length is not the dimension of both frames gives the failure
value. -/
def transition (point : Program) (sourceFrame targetInverse : List (List Poly)) :
    FrameMatrixValue :=
  let p := coordinates point
  if p.length == sourceFrame.length && p.length == targetInverse.length then
    some ⟨p, p, matrixProduct p.length (matrixAt targetInverse p) (matrixAt sourceFrame p)⟩
  else none

/-- A frame matrix applied to the coordinates of a vector: `a ↦ M a`, from the
matrix's source point to its target point. The array must lie over the source
point and have one component per source coordinate; otherwise, or for a
failure value, the result is the failure value. -/
def apply (matrix : FrameMatrixValue) (value : FiberValue) : FiberValue :=
  match matrix, value with
  | some matrix, some fiber =>
    if fiber.point == matrix.source && fiber.components.length == matrix.source.length then
      some ⟨matrix.target, matVec matrix.entries fiber.components⟩
    else none
  | _, _ => none

/-- The transpose of a frame matrix applied to the coordinates of a covector:
`α ↦ Mᵀ α`, from the matrix's target point back to its source point. The
array must lie over the target point and have one component per target
coordinate; otherwise, or for a failure value, the result is the failure
value. -/
def coapply (matrix : FrameMatrixValue) (value : FiberValue) : FiberValue :=
  match matrix, value with
  | some matrix, some fiber =>
    if fiber.point == matrix.target && fiber.components.length == matrix.target.length then
      some ⟨matrix.source, transposeVec matrix.source.length matrix.entries fiber.components⟩
    else none
  | _, _ => none

/-- The composite `after · before` of two frame matrices, from the source of
`before` to the target of `after`. The target point of `before` must be the
source point of `after`; otherwise, or for a failure value, the result is the
failure value. -/
def compose (after before : FrameMatrixValue) : FrameMatrixValue :=
  match after, before with
  | some after, some before =>
    if before.target == after.source then
      some ⟨before.source, after.target,
        matrixProduct before.source.length after.entries before.entries⟩
    else none
  | _, _ => none

/-- The entry in row `row` and column `column`, as a reduced numerator and
positive denominator. The failure value and an entry out of range read
`(0, 0)`, which no rational has. -/
def entry (matrix : FrameMatrixValue) (row column : Nat) : Int × Int :=
  match matrix with
  | some matrix =>
    match matrix.entries[row]? with
    | some entries =>
      match entries[column]? with
      | some value => ratPair value
      | none => (0, 0)
    | none => (0, 0)
  | none => (0, 0)

/-- Equality of frame matrices: points and entries. The failure value equals
nothing, itself included. -/
def matrixEqual : FrameMatrixValue → FrameMatrixValue → Bool
  | some left, some right => left == right
  | _, _ => false

end VastitasKernel.FrameRuntime
