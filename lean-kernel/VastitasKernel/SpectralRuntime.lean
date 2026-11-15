import VastitasKernel.FrameRuntime

set_option autoImplicit false

/-! Exact runtime for the spectral observations of polynomial matrix fields
(Stage 5, #806).

An endomorphism `H` of a free module of rank `n` over the coordinate ring
`A = ℚ[x₁, …, x_m]` of a smooth object is `n × n` polynomials in the
coordinates, as rows; its spectrum adds `χ = det(tI − H)` and `adj(tI − H)` in
`A[t]`, polynomials of arity `m + 1` whose last exponent is that of the fiber
coordinate `t`. The observations evaluate them at a point `p` (and an
eigenvalue candidate `t`):

- `evalMatrixPoly`: `f(H(p))` for an element `f` of `A[t]`, by Horner's rule
  in `t` over the evaluated matrix `H(p)` (`FrameRuntime.matrixAt`); it reads
  `f` coefficient by coefficient in `t` (`tCoefficient`), each evaluated at
  `p`. `annihilates` asks whether `f(H(p)) = 0`, and `actionEntry` reads one
  entry of it.
- `onBranch`: `(p, t)` is a point of the branch with localization `g`: `g(p) ≠ 0`
  and `χ(p, t) = 0`. Off the branch the other branch observations give the
  failure value: `none` for a fiber, `(0, 0)` for an entry.
- `branchDifferential`: the covector `−Σᵢ ∂ᵢχ(p, t) / χ′(p, t) dxᵢ` at `p`, a
  Stage 3 cotangent fiber, computed from the evaluated formal partial
  derivatives (`SmoothRuntime.partialDerivative`) of `χ`, never through `cot`
  or a pullback; `χ′` is the partial derivative in `t`.
- `projectorMatrix` and `projectorEntry`: the eigenprojector
  `adj(tI − H(p)) / χ′(p, t)` and one of its entries.

No operation computes or orders eigenvalues: the eigenvalue is an operand.
None checks an identity either: the kernel checks the spectral certificate,
and that the localization makes `χ′` a unit on the branch, before code
generation (`SpectralDeclarations`). The functions below read the
polynomials they are given.

The polynomial helpers `liftT`, `extend`, `fiberExponent`, `degT` and
`tCoefficient` view a polynomial of `A[t]` as a polynomial in `t` with
coefficients in `A`; the spectral checks share them.

Every definition maps over terms, rows, columns or the coefficients in `t`:
at most `spectralRank = 4` rows and columns and a degree in `t` bounded by the
algebra limits, so none needs a replacement for compiled code. Exact
rationals are not bounded here. Generated programs import this module; it
imports only the frame runtime, and through it the smooth runtime: no
compiler, oracle or mathlib module. -/
namespace VastitasKernel.SpectralRuntime

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime

/-! ## Polynomials in the fiber coordinate -/

/-- `p · tᵏ` for `p` in `A` (arity `m`), as a polynomial of `A[t]` (arity
`m + 1`, `t` last): every monomial gets the exponent `k` of `t` appended.
Appending one exponent to every monomial keeps the degree-lexicographic order
of the terms, so a canonical input gives a canonical output. -/
def liftT (power : Nat) (p : Poly) : Poly :=
  p.map fun term => ⟨term.monomial ++ [power], term.coefficient⟩

/-- A polynomial of `A` as a polynomial of `A[t]` that does not involve `t`:
arity `m` lifted to `m + 1`, `t` last. -/
def extend (p : Poly) : Poly := liftT 0 p

/-- The exponent of the fiber coordinate `t`, the last one, of a term of
`A[t]`. -/
def fiberExponent (term : Term) : Nat := term.monomial.getLastD 0

/-- The degree in `t` of a polynomial of `A[t]`; `0` for the zero polynomial. -/
def degT (p : Poly) : Nat := p.foldl (fun degree term => max degree (fiberExponent term)) 0

/-- The coefficient of `tᵏ` of a polynomial of `A[t]`, as a polynomial of `A`:
the terms whose exponent of `t` is `k`, without that exponent. The terms keep
their order, so a canonical input gives a canonical output. -/
def tCoefficient (p : Poly) (power : Nat) : Poly :=
  p.filterMap fun term =>
    if fiberExponent term == power then some ⟨term.monomial.dropLast, term.coefficient⟩ else none

/-! ## Rational matrices -/

/-- The `n × n` zero matrix. -/
def zeroMatrix (n : Nat) : Matrix := List.replicate n (List.replicate n 0)

/-- `M + c·I`: the value `c` added to every diagonal entry. -/
def addScalar (value : Rat) (matrix : Matrix) : Matrix :=
  matrix.zipIdx.map fun (row, i) => row.zipIdx.map fun (entry, j) => if i == j then entry + value else entry

/-- Every entry is zero. -/
def isZeroMatrix (matrix : Matrix) : Bool := matrix.all (·.all (· == 0))

/-- The entry in row `row` and column `column`, as a reduced numerator and
positive denominator; `(0, 0)`, which no rational has, out of range. -/
def matrixEntry (matrix : Matrix) (row column : Nat) : Int × Int :=
  match matrix[row]? with
  | some entries =>
    match entries[column]? with
    | some value => ratPair value
    | none => (0, 0)
  | none => (0, 0)

/-! ## The module action -/

/-- `f(H(p))` for `f` in `A[t]` and the `n × n` matrix `H` of polynomials of
`A`, at the point `p`: Horner's rule in `t`,
`R ← R · H(p) + f_k(p) · I` for `k` from `deg_t f` down to `0`, from `R = 0`,
where `f_k = tCoefficient f k`. -/
def evalMatrixPoly (element : Poly) (rows : List (List Poly)) (point : List Rat) : Matrix :=
  let n := rows.length
  let matrix := FrameRuntime.matrixAt rows point
  (List.range (degT element + 1)).reverse.foldl
    (fun acc k => addScalar (evalAt (tCoefficient element k) point) (FrameRuntime.matrixProduct n acc matrix))
    (zeroMatrix n)

/-- Whether `f(H(p)) = 0`, at the point that `point` evaluates to. -/
def annihilates (rows : List (List Poly)) (element : Poly) (point : Program) : Bool :=
  isZeroMatrix (evalMatrixPoly element rows (coordinates point))

/-- The entry in row `row` and column `column` of `f(H(p))`, as a reduced
fraction; `(0, 0)` out of range. -/
def actionEntry (rows : List (List Poly)) (element : Poly) (point : Program) (row column : Nat) : Int × Int :=
  matrixEntry (evalMatrixPoly element rows (coordinates point)) row column

/-! ## Branch observations -/

/-- The point `(p, t)` of `X × Line` from a point of `X` and a value. -/
def branchPoint (point value : Program) : List Rat := coordinates point ++ coordinates value

/-- Whether `(p, t)` lies on the branch with localization `g` of the spectrum
with characteristic polynomial `χ`: `g(p) ≠ 0` and `χ(p, t) = 0`. -/
def onBranch (localize characteristic : Poly) (point value : Program) : Bool :=
  evalAt localize (coordinates point) != 0 && evalAt characteristic (branchPoint point value) == 0

/-- `χ′(p, t)`, the partial derivative of `χ` in `t`, which follows the `m`
coordinates of `p`. -/
def slopeAt (characteristic : Poly) (point value : Program) : Rat :=
  evalAt (partialDerivative (coordinates point).length characteristic) (branchPoint point value)

/-- The differential at `p` of the eigenvalue of the branch through `(p, t)`:
the covector `−Σᵢ ∂ᵢχ(p, t) / χ′(p, t) dxᵢ` at `p`, with one component per
coordinate of `p`, from the evaluated partial derivatives of `χ`. Off the
branch it is the failure value. -/
def branchDifferential (localize characteristic : Poly) (point value : Program) : FiberValue :=
  if onBranch localize characteristic point value then
    let p := coordinates point
    let full := branchPoint point value
    let slope := slopeAt characteristic point value
    some ⟨p, (List.range p.length).map fun i => -evalAt (partialDerivative i characteristic) full / slope⟩
  else none

/-- The eigenprojector `adj(tI − H(p)) / χ′(p, t)` of the branch through
`(p, t)`, or `none` off the branch. -/
def projectorMatrix (localize characteristic : Poly) (adjugate : List (List Poly)) (point value : Program) :
    Option Matrix :=
  if onBranch localize characteristic point value then
    let slope := slopeAt characteristic point value
    some ((FrameRuntime.matrixAt adjugate (branchPoint point value)).map (·.map (· / slope)))
  else none

/-- The entry in row `row` and column `column` of the eigenprojector, as a
reduced fraction; `(0, 0)` off the branch and out of range. -/
def projectorEntry (localize characteristic : Poly) (adjugate : List (List Poly)) (point value : Program)
    (row column : Nat) : Int × Int :=
  match projectorMatrix localize characteristic adjugate point value with
  | some matrix => matrixEntry matrix row column
  | none => (0, 0)

end VastitasKernel.SpectralRuntime
