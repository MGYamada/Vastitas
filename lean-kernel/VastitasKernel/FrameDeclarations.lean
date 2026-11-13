import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the frame declarations of the finite frame profile (Stage 4,
#759; ADR 0001 §11).

A frame `Frame<X>` is an ordered basis of every tangent fiber of a smooth
object `X` of dimension `n`: an `n × n` matrix `P` of polynomials in the
coordinates of `X`, stored as rows, whose column `j` is frame vector `j` in
the coordinate frame, together with its inverse `Q`. `Entry.Valid`
(`IndexedValidity`) calls `checkFrame` for every frame declaration. The
check reads only the declaration, its family and its object:

* both matrices are `n` rows of `n` canonical polynomials of arity `n`;
* a *constant* frame (every entry of `P` constant) has a constant inverse,
  every entry of `P` within `Limits.metricEntryBits` and the whole of `P`
  within `Limits.metricMatrixBits` (`SmoothDeclarations.matrixBounded`, the
  bounds of a Gram matrix), and `P·Q = I` and `Q·P = I` exactly over `ℚ`;
* a *polynomial* frame has `P·Q = I` and `Q·P = I` as identities of
  canonical polynomials, with every product and sum charged to one
  `Limits.algebraWork` budget and bounded by `Limits.algebraTerms`
  (`AlgebraBasis.mul`, `AlgebraBasis.add`).

So an accepted frame is invertible at every point. The kernel computes `Q`
for a constant frame (`IndexedFrameSource`); a polynomial frame declares it.
Soundness depends only on these checks, never on how `Q` was found. -/
namespace VastitasKernel.FrameDeclarations

open VastitasKernel.Indexed VastitasKernel.AlgebraRuntime

/-! ## Polynomial matrices -/

/-- `n` rows of `n` canonical polynomials of arity `n`. -/
def polySquare (n : Nat) (matrix : PolyMatrix) : Bool :=
  matrix.length == n && matrix.all fun row => row.length == n && row.all (Poly.canonical n)

/-- Every term of the polynomial has the zero monomial. -/
def constantPoly (p : Poly) : Bool := p.all fun term => term.monomial.all (· == 0)

/-- Every entry of the matrix is a constant polynomial. -/
def constantMatrix (matrix : PolyMatrix) : Bool := matrix.all (·.all constantPoly)

/-- The values of a matrix of constant polynomials of arity `n`. -/
def values (n : Nat) (matrix : PolyMatrix) : SmoothRuntime.Matrix :=
  matrix.map (·.map fun p => SmoothRuntime.evalAt p (List.replicate n 0))

/-- The constant polynomials of arity `n` with the entries of `matrix`. -/
def constants (n : Nat) (matrix : SmoothRuntime.Matrix) : PolyMatrix := matrix.map (·.map (Poly.const n))

/-- The `n × n` identity of polynomials of arity `n`. -/
def polyIdentity (n : Nat) : PolyMatrix :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then Poly.one n else []

/-- Column `j` of a matrix given as rows. -/
def polyColumn (matrix : PolyMatrix) (j : Nat) : List Poly := matrix.map fun row => row.getD j []

/-- `Σₖ leftₖ · rightₖ`, every product and sum within the work budget. -/
def polyDot (left right : List Poly) : AlgebraBasis.Work Poly :=
  (left.zip right).foldlM (fun sum (a, b) => do AlgebraBasis.add sum (← AlgebraBasis.mul a b)) []

/-- The product of two matrices with `n` columns, given as rows, every
product and sum within the work budget. -/
def polyMatMul (n : Nat) (left right : PolyMatrix) : AlgebraBasis.Work PolyMatrix :=
  left.mapM fun row => (List.range n).mapM fun j => polyDot row (polyColumn right j)

/-! ## The frame check -/

/-- Why `checkMatrices` rejects a pair of matrices. `code` is the diagnostic
code: the limits are `E_LIMIT`, everything else `E_FRAME`. -/
inductive Failure where
  /-- The object has more than `Limits.algebraGenerators` coordinates. -/
  | dimension
  /-- `P` (`inverse = false`) or `Q` (`inverse = true`) is not `n` rows of
  `n` canonical polynomials of arity `n`. -/
  | shape (inverse : Bool)
  /-- `P` is constant and `Q` is not. -/
  | constantInverse
  /-- The entry in row `row`, column `column` of a constant `P` has more than
  `Limits.metricEntryBits` bits in its numerator or denominator. -/
  | entry (row column : Nat)
  /-- A constant `P` exceeds `Limits.metricMatrixBits`. -/
  | matrix
  /-- The products of a polynomial frame exceed an algebra limit. -/
  | work (error : AlgebraBasis.Error)
  /-- `P·Q ≠ I`. -/
  | leftInverse
  /-- `Q·P ≠ I`. -/
  | rightInverse
  deriving Repr, DecidableEq, Inhabited

def Failure.code : Failure → String
  | .dimension | .entry .. | .matrix | .work _ => "E_LIMIT"
  | _ => "E_FRAME"

/-- The first entry of a matrix, as `(row, column)`, beyond
`Limits.metricEntryBits`. -/
def unboundedEntry? (matrix : SmoothRuntime.Matrix) : Option (Nat × Nat) :=
  matrix.zipIdx.findSome? fun (row, i) =>
    row.zipIdx.findSome? fun (value, j) => if SmoothDeclarations.entryBounded value then none else some (i, j)

/-- The entry and matrix bounds of a constant frame, the bounds of a Gram
matrix. They bound the inverse and its check, so the elaboration checks them
before it computes the inverse. -/
def checkBounds (values : SmoothRuntime.Matrix) : Except Failure Unit := do
  if let some (i, j) := unboundedEntry? values then throw (.entry i j)
  unless SmoothDeclarations.matrixBounded values do throw .matrix

/-- `P·Q` and `Q·P` of a polynomial frame, both within one work budget. -/
def products (n : Nat) (matrix inverse : PolyMatrix) : AlgebraBasis.Work (PolyMatrix × PolyMatrix) := do
  let left ← polyMatMul n matrix inverse
  let right ← polyMatMul n inverse matrix
  pure (left, right)

/-- The matrices `P` and `Q` of a frame on an object of dimension `n`: their
shape, the bounds of a constant frame, and both inverse identities. -/
def checkMatrices (n : Nat) (matrix inverse : PolyMatrix) : Except Failure Unit := do
  if n > Limits.algebraGenerators then throw .dimension
  unless polySquare n matrix do throw (.shape false)
  unless polySquare n inverse do throw (.shape true)
  if constantMatrix matrix then
    unless constantMatrix inverse do throw .constantInverse
    let p := values n matrix
    let q := values n inverse
    checkBounds p
    unless SmoothDeclarations.matMul n p q == SmoothDeclarations.identityMatrix n do throw .leftInverse
    unless SmoothDeclarations.matMul n q p == SmoothDeclarations.identityMatrix n do throw .rightInverse
  else
    match AlgebraBasis.run (products n matrix inverse) with
    | .error error => throw (.work error)
    | .ok (left, right) =>
      unless left == polyIdentity n do throw .leftInverse
      unless right == polyIdentity n do throw .rightInverse

/-- The frame declaration `frame family object matrix inverse`: an
application of a `frame` family to a declared smooth object, and matrices
that `checkMatrices` accepts at the object's dimension. -/
def checkFrame (env : Environment) (family object : DeclId) (matrix inverse : PolyMatrix) : Bool :=
  isFrameFamily env family && validApplication env ⟨family, [.object (.global object)]⟩ &&
    match smoothDimension? env object with
    | some n => (checkMatrices n matrix inverse).isOk
    | none => false

end VastitasKernel.FrameDeclarations
