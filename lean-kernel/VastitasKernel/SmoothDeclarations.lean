import VastitasKernel.SmoothRuntime
import VastitasKernel.Limits

/-! Checks for the declarations of the finite smooth affine profile.

A smooth object is `ℝⁿ` with `n` distinct named coordinates. A metric is a
constant symmetric `n × n` Gram matrix with rational entries. Its evidence is
an exact certificate that the kernel computes and then checks again:

* nondegenerate: an inverse `B` with `G B = I` and `B G = I`;
* Riemannian: `G = L D Lᵀ` with `L` unit lower triangular, every entry of `D`
  positive, and an inverse `L⁻¹` with `L L⁻¹ = I` and `L⁻¹ L = I`.

Soundness depends only on the checks (`checkNondegenerate`,
`checkRiemannian`), never on how `invert?` or `ldl?` found the certificate.
Whether every invertible or positive-definite form is found is tested, not
proved. -/
namespace VastitasKernel.SmoothDeclarations

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

inductive Error where
  | limit (resource : String)
  | smooth (reason : String)
  | metric (reason : String)
  deriving Repr, DecidableEq, Inhabited

def Error.code : Error → String
  | .limit _ => "E_LIMIT"
  | .smooth _ => "E_SMOOTH"
  | .metric _ => "E_METRIC"

def Error.message : Error → String
  | .limit resource => s!"smooth {resource} limit exceeded"
  | .smooth reason | .metric reason => reason

/-! ## Smooth objects and maps -/

/-- A smooth object `Affine(n)[c₁, …, cₙ]`. -/
def checkObject (dimension : Nat) (coordinates : List String) : Except Error Unit := do
  if dimension > Limits.algebraGenerators then throw (.limit "dimension")
  unless coordinates.length == dimension do
    throw (.smooth s!"Affine({dimension}) needs {dimension} coordinates, but {coordinates.length} are given")
  unless coordinates.Nodup do throw (.smooth "smooth coordinates must be distinct")

/-- A smooth map between objects of the given dimensions. -/
def checkMap (source target : Nat) (map : Map) : Except Error Unit := do
  unless map.arity == source do throw (.smooth "a smooth map must use its source coordinates")
  unless map.basis.isEmpty do throw (.smooth "a smooth map has no relations")
  unless map.images.length == target do
    throw (.smooth s!"a smooth map needs {target} images, but {map.images.length} are given")
  unless map.images.all (Poly.canonical source) do throw (.smooth "a smooth map image is not canonical")

/-! ## Matrices -/

def entry (matrix : Matrix) (row column : Nat) : Rat := (matrix.getD row []).getD column 0

/-- `n` rows of `n` entries. -/
def square (n : Nat) (matrix : Matrix) : Bool :=
  matrix.length == n && matrix.all fun row => row.length == n

def symmetric (n : Nat) (matrix : Matrix) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j => entry matrix i j == entry matrix j i

def identityMatrix (n : Nat) : Matrix :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then 1 else 0

def column (matrix : Matrix) (j : Nat) : List Rat := matrix.map fun row => row.getD j 0

def transpose (n : Nat) (matrix : Matrix) : Matrix := (List.range n).map (column matrix)

/-- The product of two `n × n` matrices. -/
def matMul (n : Nat) (left right : Matrix) : Matrix :=
  left.map fun row => (List.range n).map fun j => dot row (column right j)

def diagonal (n : Nat) (values : List Rat) : Matrix :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then values.getD i 0 else 0

/-- `L` has ones on the diagonal and zeros above it. -/
def unitLower (n : Nat) (matrix : Matrix) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    entry matrix i j == (if i == j then 1 else if j > i then 0 else entry matrix i j)

/-! ## Certificate checks -/

/-- Both inverse identities, exactly. -/
def checkNondegenerate (n : Nat) (gram inverse : Matrix) : Bool :=
  square n gram && square n inverse &&
    matMul n gram inverse == identityMatrix n && matMul n inverse gram == identityMatrix n

/-- An exact `L D Lᵀ` factorization with positive `D`, and an inverse of `L`. -/
def checkRiemannian (n : Nat) (gram lower : Matrix) (pivots : List Rat) (lowerInverse : Matrix) :
    Bool :=
  square n gram && square n lower && square n lowerInverse && pivots.length == n &&
    pivots.all (fun d => decide (0 < d)) && unitLower n lower &&
    matMul n (matMul n lower (diagonal n pivots)) (transpose n lower) == gram &&
    matMul n lower lowerInverse == identityMatrix n &&
    matMul n lowerInverse lower == identityMatrix n

/-! ## Certificate search -/

private def scaleRow (factor : Rat) (row : List Rat) : List Rat := row.map (factor * ·)

private def subRow (row pivot : List Rat) (factor : Rat) : List Rat :=
  List.zipWith (fun a b => a - factor * b) row pivot

/-- One Gauss–Jordan column step on the augmented rows. -/
private def eliminate (n column : Nat) (rows : Matrix) : Option Matrix := do
  let candidates := (List.range n).filter fun r => r ≥ column && entry rows r column != 0
  let pivotRow ← candidates.head?
  let pivot := rows.getD pivotRow []
  let other := rows.getD column []
  let swapped := (rows.set column pivot).set pivotRow other
  let normalized := scaleRow (entry swapped column column)⁻¹ (swapped.getD column [])
  let withPivot := swapped.set column normalized
  pure <| (List.range n).map fun r =>
    let row := withPivot.getD r []
    if r == column then row else subRow row normalized (entry withPivot r column)

private def eliminateFrom (n : Nat) : Nat → Nat → Matrix → Option Matrix
  | 0, _, rows => some rows
  | remaining + 1, column, rows => do
    eliminateFrom n remaining (column + 1) (← eliminate n column rows)

/-- The exact inverse of an `n × n` matrix, if it exists. -/
def invert? (n : Nat) (matrix : Matrix) : Option Matrix := do
  unless square n matrix do none
  let augmented := (List.range n).map fun i => matrix.getD i [] ++ (identityMatrix n).getD i []
  let reduced ← eliminateFrom n n 0 augmented
  pure <| reduced.map (·.drop n)

private def ldlColumn (n j : Nat) (gram : Matrix) (state : Matrix × List Rat) :
    Option (Matrix × List Rat) := do
  let (lower, pivots) := state
  let previous := List.range j
  let pivot := entry gram j j -
    previous.foldl (fun sum k => sum + entry lower j k * entry lower j k * pivots.getD k 0) 0
  unless 0 < pivot do none
  let lower := (List.range n).foldl (fun current i =>
    if i > j then
      let value := (entry gram i j -
        previous.foldl (fun sum k => sum + entry lower i k * entry lower j k * pivots.getD k 0) 0) /
          pivot
      current.set i ((current.getD i []).set j value)
    else current) lower
  pure (lower, pivots ++ [pivot])

/-- `L`, `D` and `L⁻¹` with `G = L D Lᵀ` and `D > 0`, if they exist. They
exist exactly when `G` is symmetric positive definite. -/
def ldl? (n : Nat) (gram : Matrix) : Option (Matrix × List Rat × Matrix) := do
  unless square n gram && symmetric n gram do none
  let (lower, pivots) ← (List.range n).foldlM (fun state j => ldlColumn n j gram state)
    (identityMatrix n, [])
  let lowerInverse ← invert? n lower
  pure (lower, pivots, lowerInverse)

/-! ## Declaration checks -/

/-- The numerator and the denominator of `value` each have at most
`Limits.metricEntryBits` bits. -/
def entryBounded (value : Rat) : Bool :=
  value.num.natAbs < 2 ^ Limits.metricEntryBits && value.den < 2 ^ Limits.metricEntryBits

/-- Every entry of the matrix is bounded. With at most `algebraGenerators`
rows, this bounds the work of `invert?`, `ldl?` and the certificate checks. -/
def gramBounded (gram : Matrix) : Bool := gram.all fun row => row.all entryBounded

/-- A Gram matrix on an object of dimension `n`. -/
def checkGram (n : Nat) (gram : Matrix) : Except Error Unit := do
  if n > Limits.algebraGenerators then throw (.limit "dimension")
  unless square n gram do throw (.metric s!"a metric on a {n}-dimensional object needs an {n} × {n} Gram matrix")
  unless symmetric n gram do throw (.metric "a metric must be symmetric")

/-- Compute and check nondegeneracy evidence. -/
def certifyNondegenerate (n : Nat) (gram : Matrix) : Except Error Matrix := do
  checkGram n gram
  match invert? n gram with
  | none => throw (.metric "the metric is singular, so it is not nondegenerate")
  | some inverse =>
    unless checkNondegenerate n gram inverse do throw (.metric "the computed inverse failed its check")
    pure inverse

/-- Compute and check Riemannian evidence. -/
def certifyRiemannian (n : Nat) (gram : Matrix) : Except Error (Matrix × List Rat × Matrix) := do
  checkGram n gram
  match ldl? n gram with
  | none => throw (.metric "the metric is not positive definite, so it is not Riemannian")
  | some (lower, pivots, lowerInverse) =>
    unless checkRiemannian n gram lower pivots lowerInverse do
      throw (.metric "the computed factorization failed its check")
    pure (lower, pivots, lowerInverse)

end VastitasKernel.SmoothDeclarations
