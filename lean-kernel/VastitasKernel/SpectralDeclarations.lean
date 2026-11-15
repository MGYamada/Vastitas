import VastitasKernel.FrameDeclarations
import VastitasKernel.Keywords
import VastitasKernel.SpectralRuntime

set_option autoImplicit false

/-! Checks for the spectral declarations of the finite spectral profile
(Stage 5, #806; `std::linalg::spectral`; ADR 0001 §12).

Over the coordinate ring `A = ℚ[x₁, …, x_m]` of a smooth object `X`:

- a free module `FreeModule<X>` is `Aⁿ` with a named ordered basis:
  `checkModule` accepts `n` distinct names, `1 ≤ n ≤ spectralRank`;
- an endomorphism `Endomorphism<X>` of a free module of rank `n` is an
  `n × n` matrix `H` of polynomials, as rows: `checkRows` accepts `n` rows of
  `n` canonical polynomials of arity `m`, and with `symmetric` checks `H = Hᵀ`,
  naming the first entry that differs from its mirror;
- a spectrum `Spectrum<X>` of `H` is the characteristic scheme `Σ_H` with the
  module action. Its fiber coordinate `t` is a new identifier, no strict
  keyword, no coordinate of `X` and no basis vector of the free module
  (`fiberValid`). Its
  certificate (`SpectralCertificate`) holds `χ` and
  `adj(tI − H)` in `A[t]`, `t` the last variable, and the matrix quotient `Q`
  of idempotence. `checkCertificate` checks, within one `algebraWork` run:
  1. `χ = det(tI − H)`, by cofactor expansion (`detPoly`: Laplace along row
     0, the minors by `List.eraseIdx`), a route independent of the producer;
  2. `(tI − H)·adj = χ·I`, and 2′. `adj·(tI − H) = χ·I`, so that the
     eigenprojector `adj/χ′` commutes with `H` on the branch;
  3. `Σᵢ adjᵢᵢ = χ′` (`χ′ = ∂_t χ`);
  4. `χ(H) = 0` in `Mₙ(A)` (Cayley–Hamilton), by Horner's rule in `t`;
  5. `adj² − χ′·adj = Q·χ` (the eigenprojector is idempotent modulo `χ`);
  6. `∂ᵢχ + tr(adj·∂ᵢH) = 0` for each coordinate `i` (Jacobi's formula).
- a branch `Branch<X>` of a spectrum is a gap certificate on the principal
  open `D(g)`: `checkWitness` accepts `g` in `A` (arity `m`, so without `t`),
  `g ≠ 0`, `W` reduced (`deg_t W < n`), `e ≤ spectralPower`, and
  `W·χ′ − gᵉ = Q·χ` for the stored quotient `Q`.

Every identity "modulo `χ`" is checked as `X − Q·χ = []` with a quotient that
the kernel computes during elaboration (`divideT`, division by `χ` as a monic
polynomial in `t`) and stores in the declaration; the check multiplies and
subtracts, so soundness does not depend on the division. Nothing here comes
from the wire. The producer `faddeevLeVerrier` computes `χ` and `adj` for the
elaboration (`certify`); it is not trusted either, since `checkCertificate`
checks its result by identities 1–6.

Every product is charged before it is computed: a product of two polynomials
is `AlgebraBasis.mul`, which charges each step of the fold as it performs it
(#768), and a product of matrices `FrameDeclarations.polyMatMul`, which
charges `productWork` before each product; sums are `AlgebraBasis.add` and
`AlgebraBasis.sub`, every result bounded by `algebraTerms`. The rank and
power limits are checked before any product. `Failure.code` is `E_LIMIT` for
the limits and the budget and `E_SPECTRAL` otherwise.

The invariants are `tracePower` (`tr(Hᵏ)`, `1 ≤ k ≤ spectralPower`, by
budgeted matrix products, the image bounded by `algebraTerms`) and
`charCoefficient` (the coefficient of `tⁱ` in `χ`).

`Entry.Valid` (`IndexedValidity`) calls one environment check per
declaration: `checkFreeModule`, `checkEndomorphism`, `checkSpectrum` and
`checkBranch`. Each reads its family, its object and the declaration it names
through the views of `Indexed`, and runs the data check above. -/
namespace VastitasKernel.SpectralDeclarations

open VastitasKernel.Indexed VastitasKernel.AlgebraRuntime
open VastitasKernel.SpectralRuntime (liftT extend degT tCoefficient)

/-! ## Failures -/

/-- Why a spectral check rejects. `code` is the diagnostic code: the limits
and the budget are `E_LIMIT`, everything else `E_SPECTRAL`. -/
inductive Failure where
  /-- A basis, or an endomorphism, of more than `Limits.spectralRank` vectors. -/
  | rank (size : Nat)
  /-- A free module with no basis vector. -/
  | emptyBasis
  /-- A basis name that occurs twice. -/
  | duplicateBasis (name : String)
  /-- The rows of an endomorphism are not `n` rows of `n` canonical
  polynomials of the object's arity. -/
  | shape
  /-- A `symmetric` endomorphism whose entry in row `row`, column `column`
  differs from the entry in row `column`, column `row` (`row < column`). -/
  | notSymmetric (row column : Nat)
  /-- The certificate of a spectrum is not `χ`, `n × n` adjugate entries and
  `n × n` quotients, canonical of arity `m + 1`. -/
  | certificateShape
  /-- Identity 1: `χ ≠ det(tI − H)`. -/
  | characteristic
  /-- Identity 2: `(tI − H)·adj ≠ χ·I`. -/
  | adjugate
  /-- Identity 2′: `adj·(tI − H) ≠ χ·I`. -/
  | adjugateRight
  /-- Identity 3: `Σᵢ adjᵢᵢ ≠ χ′`. -/
  | adjugateTrace
  /-- Identity 4: `χ(H) ≠ 0`. -/
  | cayleyHamilton
  /-- Identity 5: `adj² − χ′·adj ≠ Q·χ`. -/
  | idempotence
  /-- Identity 6 in the coordinate `coordinate`: `∂ᵢχ + tr(adj·∂ᵢH) ≠ 0`. -/
  | jacobi (coordinate : Nat)
  /-- A power `k` of `trace_power(H, k)` beyond `Limits.spectralPower`. -/
  | power (value : Nat)
  /-- The power `0` of `trace_power(H, 0)`; the powers start at `1`. -/
  | zeroPower
  /-- An index `i` of `char_coefficient(S, i)` beyond the degree `n` of `χ`. -/
  | coefficientIndex (index degree : Nat)
  /-- An exponent `e` of a branch beyond `Limits.spectralPower`. -/
  | exponent (value : Nat)
  /-- The localization of a branch is not a canonical polynomial of the base,
  of arity `m`. -/
  | localizeShape
  /-- The localization of a branch is zero. -/
  | localizeZero
  /-- The witness or the quotient of a branch is not a canonical polynomial
  of arity `m + 1`. -/
  | witnessShape
  /-- The witness of a branch has degree `degree ≥ n` in `t`. -/
  | unreducedWitness (degree : Nat)
  /-- `W·χ′ − gᵉ ≠ Q·χ`. -/
  | witness
  /-- The products exceed an algebra limit. -/
  | work (error : AlgebraBasis.Error)
  deriving Repr, DecidableEq, Inhabited

def Failure.code : Failure → String
  | .rank _ | .power _ | .exponent _ => "E_LIMIT"
  | .work error => error.code
  | _ => "E_SPECTRAL"

/-! ## Polynomial matrices -/

/-- `n` rows of `n` canonical polynomials of arity `arity`. -/
def squareOf (n arity : Nat) (matrix : PolyMatrix) : Bool :=
  matrix.length == n && matrix.all fun row => row.length == n && row.all (Poly.canonical arity)

/-- The `n × n` zero matrix of polynomials. -/
def zeroPolyMatrix (n : Nat) : PolyMatrix := List.replicate n (List.replicate n [])

/-- The `n × n` matrix with `value` on the diagonal and zero elsewhere. -/
def scalarMatrix (n : Nat) (value : Poly) : PolyMatrix :=
  (List.range n).map fun i => (List.range n).map fun j => if i == j then value else []

/-- Every entry is the zero polynomial. -/
def isZeroPolyMatrix (matrix : PolyMatrix) : Bool := matrix.all (·.all (·.isEmpty))

/-- The trace `Σᵢ Mᵢᵢ`, with `Poly.add`. -/
def tracePoly (matrix : PolyMatrix) : Poly :=
  matrix.zipIdx.foldl (fun sum (row, i) => Poly.add sum (row.getD i [])) []

/-- Every entry of a matrix of `A` as an entry of `A[t]` (`extend`). -/
def extendMatrix (matrix : PolyMatrix) : PolyMatrix := matrix.map (·.map extend)

/-- The entrywise partial derivative in coordinate `i`. -/
def derivativeMatrix (i : Nat) (matrix : PolyMatrix) : PolyMatrix :=
  matrix.map (·.map (SmoothRuntime.partialDerivative i))

/-- `tI − H` in `A[t]` for `H` over `A = ℚ[x₁, …, x_m]` (`arity = m`): the
entry in row `i`, column `j` is `δᵢⱼ t − Hᵢⱼ`, with `t` the variable `m` of
arity `m + 1`. -/
def charMatrix (arity : Nat) (rows : PolyMatrix) : PolyMatrix :=
  rows.zipIdx.map fun (row, i) => row.zipIdx.map fun (entry, j) =>
    Poly.sub (if i == j then Poly.var (arity + 1) arity else []) (extend entry)

/-- The first entry, as `(row, column)` with `row < column`, that differs from
its mirror: `H` is symmetric when there is none. -/
def asymmetricEntry? (matrix : PolyMatrix) : Option (Nat × Nat) :=
  matrix.zipIdx.findSome? fun (row, i) =>
    row.zipIdx.findSome? fun (entry, j) =>
      if i < j && entry != (matrix.getD j []).getD i [] then some (i, j) else none

/-- The first name of a list that occurs earlier in it. -/
def duplicate? : List String → Option String
  | [] => none
  | name :: rest => if rest.contains name then some name else duplicate? rest

/-- The identifier rule of the source grammar, as the frontend's
`Parser::name` applies it: an ASCII letter or `_`, then ASCII letters,
digits and `_`, and no strict keyword (`strictKeywords`, #831). -/
def isIdentifier (name : String) : Bool :=
  (match name.toList with
    | [] => false
    | first :: rest => (first.isAlpha && first.toNat < 128 || first == '_') &&
        rest.all fun c => c.isAlphanum && c.toNat < 128 || c == '_') &&
    !strictKeywords.contains name

/-- The fiber coordinate `t` of a spectrum `eigen(H, t)` is a new name: an
identifier, so no strict keyword, that is no coordinate of the object and no
basis vector of the free module of `H`. -/
def fiberValid (coordinates basis : List String) (fiber : String) : Bool :=
  isIdentifier fiber && !coordinates.contains fiber && !basis.contains fiber

/-! ## Budgeted algebra -/

open AlgebraBasis (Work)

/-- The cofactor determinant of the first `size` rows of `matrix`, over
polynomials of arity `arity`, by Laplace expansion along row 0:
`det M = Σⱼ (−1)ʲ M₀ⱼ · det M⁽⁰ʲ⁾`, where the minor `M⁽⁰ʲ⁾` drops row 0 and,
by `List.eraseIdx j`, column `j` of every other row. The determinant of no
rows is `1`. Every product and sum is budgeted. -/
def detPoly (arity : Nat) : Nat → PolyMatrix → Work Poly
  | 0, _ => pure (Poly.one arity)
  | size + 1, matrix =>
    (matrix.headD []).zipIdx.foldlM (fun sum (entry, j) => do
      let minor ← detPoly arity size (matrix.tail.map (·.eraseIdx j))
      let term ← AlgebraBasis.mul entry minor
      if j % 2 == 0 then AlgebraBasis.add sum term else AlgebraBasis.sub sum term) []

/-- The `n × n` identity of polynomials of arity `arity`. -/
def identityOf (n arity : Nat) : PolyMatrix := scalarMatrix n (Poly.one arity)

/-- `value` added to every diagonal entry of `matrix`, budgeted. -/
def addDiagonal (matrix : PolyMatrix) (value : Poly) : Work PolyMatrix :=
  matrix.zipIdx.mapM fun (row, i) => row.zipIdx.mapM fun (entry, j) =>
    if i == j then AlgebraBasis.add entry value else pure entry

/-- `f(H)` in `Mₙ(A)` for `f` in `A[t]` and `H` over `A`: Horner's rule in
`t`, `R ← R · H + f_k · I` for `k` from `deg_t f` down to `0`, from `R = 0`,
where `f_k = tCoefficient f k`. The runtime's `evalMatrixPoly` is its value
at a point. -/
def matrixPolynomial (n : Nat) (rows : PolyMatrix) (element : Poly) : Work PolyMatrix :=
  (List.range (degT element + 1)).reverse.foldlM
    (fun acc k => do addDiagonal (← FrameDeclarations.polyMatMul n acc rows) (tCoefficient element k))
    (zeroPolyMatrix n)

/-- `Hᵏ` over polynomials of arity `arity`, `H⁰ = I`. -/
def matrixPower (arity n : Nat) (rows : PolyMatrix) : Nat → Work PolyMatrix
  | 0 => pure (identityOf n arity)
  | k + 1 => do FrameDeclarations.polyMatMul n (← matrixPower arity n rows k) rows

/-- The invariant `tr(Hᵏ)`, a polynomial of `A`. The diagonal sum is linear,
but it can exceed `algebraTerms` when the diagonal entries of `Hᵏ` have
disjoint terms, so the image is bounded like every other result. -/
def tracePower (arity : Nat) (rows : PolyMatrix) (power : Nat) : Work Poly := do
  AlgebraBasis.bounded (tracePoly (← matrixPower arity rows.length rows power))

/-- The invariant `char_coefficient(S, i)`: the coefficient of `tⁱ` in `χ`, a
polynomial of `A`. -/
def charCoefficient (characteristic : Poly) (index : Nat) : Poly := tCoefficient characteristic index

/-- `x − q·χ`, budgeted: zero exactly when `x = q·χ`. -/
def residual (characteristic x quotient : Poly) : Work Poly := do
  AlgebraBasis.sub x (← AlgebraBasis.mul quotient characteristic)

/-! ## The producer (untrusted) -/

/-- Division of `x` by `χ`, monic of degree `n` in `t`, in `A[t]`: while the
remainder has degree `d ≥ n` in `t`, its coefficient `c` of `tᵈ` gives the
quotient term `c·t^(d−n)`. It returns the quotient and the remainder, with
`x = quotient·χ + remainder`. The checks never call it: they check
`x − quotient·χ = []`. -/
def divideT (n : Nat) (characteristic x : Poly) : Work (Poly × Poly) :=
  go (degT x + 1) [] x
where
  go : Nat → Poly → Poly → Work (Poly × Poly)
    | 0, quotient, remainder => pure (quotient, remainder)
    | fuel + 1, quotient, remainder =>
      let degree := degT remainder
      if remainder.isEmpty || degree < n then pure (quotient, remainder) else do
        let term := liftT (degree - n) (tCoefficient remainder degree)
        let quotient ← AlgebraBasis.add quotient term
        let remainder ← AlgebraBasis.sub remainder (← AlgebraBasis.mul term characteristic)
        go fuel quotient remainder

/-- `Σ entries` of two matrices entrywise, budgeted. -/
def addMatrices (left right : PolyMatrix) : Work PolyMatrix :=
  (left.zip right).mapM fun (a, b) => (a.zip b).mapM fun (x, y) => AlgebraBasis.add x y

/-- The Faddeev–LeVerrier recurrence for the `n × n` matrix `H` over `A`
(`arity = m`): `M₀ = 0`, `c_n = 1`, and for `k = 1, …, n`
`M_k = H·M_{k−1} + c_{n−k+1}·I`, `c_{n−k} = −tr(H·M_k)/k`. Then
`χ = Σ_k c_k tᵏ` and `adj(tI − H) = Σ_k M_k t^(n−k)`, in `A[t]`. -/
def faddeevLeVerrier (arity : Nat) (rows : PolyMatrix) : Work (Poly × PolyMatrix) := do
  let n := rows.length
  let mut previous := zeroPolyMatrix n
  let mut coefficient := Poly.one arity
  let mut characteristic := liftT n (Poly.one arity)
  let mut adjugate := zeroPolyMatrix n
  for step in List.range n do
    let k := step + 1
    let current ← addDiagonal (← FrameDeclarations.polyMatMul n rows previous) coefficient
    adjugate ← addMatrices adjugate (current.map (·.map (liftT (n - k))))
    let trace := tracePoly (← FrameDeclarations.polyMatMul n rows current)
    coefficient ← AlgebraBasis.bounded (Poly.scale (-1 / (k : Rat)) trace)
    characteristic ← AlgebraBasis.add characteristic (liftT (n - k) coefficient)
    previous := current
  pure (characteristic, adjugate)

/-- The certificate of the spectrum of `H` over `A` (`arity = m`): `χ` and
`adj(tI − H)` by Faddeev–LeVerrier, and the idempotence quotients
`(adj² − χ′·adj) div χ`. `checkCertificate` checks it. -/
def certify (arity : Nat) (rows : PolyMatrix) : Work SpectralCertificate := do
  let n := rows.length
  let (characteristic, adjugate) ← faddeevLeVerrier arity rows
  let slope := SmoothRuntime.partialDerivative arity characteristic
  let square ← FrameDeclarations.polyMatMul n adjugate adjugate
  let idempotence ← (square.zip adjugate).mapM fun (squares, entries) =>
    (squares.zip entries).mapM fun (s, a) => do
      let x ← AlgebraBasis.sub s (← AlgebraBasis.mul slope a)
      pure (← divideT n characteristic x).1
  pure ⟨characteristic, adjugate, idempotence⟩

/-- The gap certificate's left side `W·χ′ − gᵉ`, budgeted, over `A[t]`
(`arity = m`, `g` in `A`). -/
def witnessDifference (arity : Nat) (characteristic localize witness : Poly) (exponent : Nat) : Work Poly := do
  let slope := SmoothRuntime.partialDerivative arity characteristic
  let product ← AlgebraBasis.mul witness slope
  AlgebraBasis.sub product (← AlgebraBasis.power (arity + 1) (extend localize) exponent)

/-- The quotient of the gap certificate, `(W·χ′ − gᵉ) div χ`, which the
elaboration stores; `checkWitness` checks it. -/
def witnessQuotient (arity n : Nat) (characteristic localize witness : Poly) (exponent : Nat) : Work Poly := do
  pure (← divideT n characteristic (← witnessDifference arity characteristic localize witness exponent)).1

/-! ## The checks -/

/-- The basis of a free module: `1 ≤ n ≤ spectralRank` distinct names. The
rank is checked first. -/
def checkModule (basis : List String) : Except Failure Unit := do
  if basis.length > Limits.spectralRank then throw (.rank basis.length)
  if basis.isEmpty then throw .emptyBasis
  if let some name := duplicate? basis then throw (.duplicateBasis name)

/-- The rows of an endomorphism of a free module of rank `n` over `A`
(`arity = m`): `n ≤ spectralRank`, `n` rows of `n` canonical polynomials of
arity `m`, and `H = Hᵀ` when declared `symmetric`. -/
def checkRows (arity n : Nat) (rows : PolyMatrix) (symmetric : Bool) : Except Failure Unit := do
  if n > Limits.spectralRank then throw (.rank n)
  unless squareOf n arity rows do throw .shape
  if symmetric then
    if let some (i, j) := asymmetricEntry? rows then throw (.notSymmetric i j)

/-- The values that the identities of a certificate compare, all computed
within one work budget (`identities`). -/
structure Identities where
  /-- `det(tI − H)`, by `detPoly`. -/
  determinant : Poly
  /-- `(tI − H)·adj`. -/
  product : PolyMatrix
  /-- `adj·(tI − H)`. -/
  rightProduct : PolyMatrix
  /-- `χ(H)`. -/
  cayleyHamilton : PolyMatrix
  /-- `adj² − χ′·adj − Q·χ`, entrywise. -/
  idempotence : PolyMatrix
  /-- `∂ᵢχ + tr(adj·∂ᵢH)` for each coordinate `i`. -/
  jacobi : List Poly
  deriving Repr, Inhabited

/-- The values of identities 1, 2, 2′, 4, 5 and 6 for `H` over `A`
(`arity = m`) and a certificate, in one budget. Identity 3 needs no
product. -/
def identities (arity : Nat) (rows : PolyMatrix) (certificate : SpectralCertificate) : Work Identities := do
  let n := rows.length
  let characteristic := certificate.characteristic
  let adjugate := certificate.adjugate
  let shifted := charMatrix arity rows
  let determinant ← detPoly (arity + 1) n shifted
  let product ← FrameDeclarations.polyMatMul n shifted adjugate
  let rightProduct ← FrameDeclarations.polyMatMul n adjugate shifted
  let cayleyHamilton ← matrixPolynomial n rows characteristic
  let slope := SmoothRuntime.partialDerivative arity characteristic
  let square ← FrameDeclarations.polyMatMul n adjugate adjugate
  let idempotence ← ((square.zip adjugate).zip certificate.idempotence).mapM fun ((squares, entries), quotients) =>
    ((squares.zip entries).zip quotients).mapM fun ((s, a), q) => do
      residual characteristic (← AlgebraBasis.sub s (← AlgebraBasis.mul slope a)) q
  let jacobi ← (List.range arity).mapM fun i => do
    let derivative ← FrameDeclarations.polyMatMul n adjugate (extendMatrix (derivativeMatrix i rows))
    AlgebraBasis.add (SmoothRuntime.partialDerivative i characteristic) (tracePoly derivative)
  pure ⟨determinant, product, rightProduct, cayleyHamilton, idempotence, jacobi⟩

/-- The certificate of the spectrum of `H` over `A` (`arity = m`): the rank
first, then the shapes, then identities 1, 2, 2′ and 3–6 in order. -/
def checkCertificate (arity : Nat) (rows : PolyMatrix) (certificate : SpectralCertificate) :
    Except Failure Unit := do
  let n := rows.length
  if n > Limits.spectralRank then throw (.rank n)
  unless squareOf n arity rows do throw .shape
  unless Poly.canonical (arity + 1) certificate.characteristic && squareOf n (arity + 1) certificate.adjugate &&
      squareOf n (arity + 1) certificate.idempotence do
    throw .certificateShape
  match AlgebraBasis.run (identities arity rows certificate) with
  | .error error => throw (.work error)
  | .ok values =>
    unless values.determinant == certificate.characteristic do throw .characteristic
    unless values.product == scalarMatrix n certificate.characteristic do throw .adjugate
    unless values.rightProduct == scalarMatrix n certificate.characteristic do throw .adjugateRight
    unless tracePoly certificate.adjugate == SmoothRuntime.partialDerivative arity certificate.characteristic do
      throw .adjugateTrace
    unless isZeroPolyMatrix values.cayleyHamilton do throw .cayleyHamilton
    unless isZeroPolyMatrix values.idempotence do throw .idempotence
    if let some i := values.jacobi.findIdx? (!·.isEmpty) then throw (.jacobi i)

/-- The gap certificate of a branch of the spectrum with characteristic
polynomial `χ` of an endomorphism of rank `n` over `A` (`arity = m`): the
exponent limit first, `g` canonical of arity `m` and nonzero, `W` and `Q`
canonical of arity `m + 1`, `deg_t W < n`, and `W·χ′ − gᵉ − Q·χ = []`. -/
def checkWitness (arity n : Nat) (characteristic localize witness : Poly) (exponent : Nat) (quotient : Poly) :
    Except Failure Unit := do
  if exponent > Limits.spectralPower then throw (.exponent exponent)
  unless Poly.canonical arity localize do throw .localizeShape
  if localize.isEmpty then throw .localizeZero
  unless Poly.canonical (arity + 1) witness && Poly.canonical (arity + 1) quotient do throw .witnessShape
  if degT witness ≥ n then throw (.unreducedWitness (degT witness))
  match AlgebraBasis.run (do
      residual characteristic (← witnessDifference arity characteristic localize witness exponent) quotient) with
  | .error error => throw (.work error)
  | .ok difference => unless difference.isEmpty do throw .witness

/-- The power of `trace_power(H, k)`: `1 ≤ k ≤ spectralPower`, the limit first. -/
def checkPower (power : Nat) : Except Failure Unit := do
  if power > Limits.spectralPower then throw (.power power)
  if power == 0 then throw .zeroPower

/-- The image `tr(Hᵏ)` of `trace_power(H, k)` for `H` over `A` (`arity = m`),
or why it is rejected: the power and the rank are checked before any
product. -/
def tracePowerImage (arity : Nat) (rows : PolyMatrix) (power : Nat) : Except Failure Poly := do
  checkPower power
  if rows.length > Limits.spectralRank then throw (.rank rows.length)
  match AlgebraBasis.run (tracePower arity rows power) with
  | .error error => throw (.work error)
  | .ok image => pure image

/-- The image of `char_coefficient(S, i)` for `χ` of degree `n`, or why it is
rejected: `i ≤ n`. -/
def charCoefficientImage (n : Nat) (characteristic : Poly) (index : Nat) : Except Failure Poly := do
  if index > n then throw (.coefficientIndex index n)
  pure (charCoefficient characteristic index)

/-! ## The declaration checks -/

/-- The family is a family of `representation` applied to the declared smooth
object `object`. -/
def declaredAt (env : Environment) (isFamily : Bool) (family object : DeclId) : Bool :=
  isFamily && validApplication env ⟨family, [.object (.global object)]⟩ && (smoothDimension? env object).isSome

/-- The free module declaration `freeModule family object basis`: a
`free_module` family applied to a declared smooth object, and a basis that
`checkModule` accepts. -/
def checkFreeModule (env : Environment) (family object : DeclId) (basis : List String) : Bool :=
  declaredAt env (isFreeModuleFamily env family) family object && (checkModule basis).isOk

/-- The endomorphism declaration `endomorphism family object module rows
symmetric`: an `endomorphism` family applied to a declared smooth object of
dimension `m`, a free module of that object with a basis of `n` vectors, and
rows that `checkRows` accepts at `m` and `n`. -/
def checkEndomorphism (env : Environment) (family object module : DeclId) (rows : PolyMatrix)
    (symmetric : Bool) : Bool :=
  declaredAt env (isEndomorphismFamily env family) family object &&
    match smoothDimension? env object, freeModuleData? env module with
    | some m, some (_, moduleObject, basis) =>
      moduleObject == object && (checkRows m basis.length rows symmetric).isOk
    | _, _ => false

/-- The spectrum declaration `spectrum family object endomorphism fiber
certificate`: a `spectrum` family applied to a declared smooth object with
coordinates `x₁, …, x_m`, an endomorphism of that object whose free module is
declared, a fiber name that `fiberValid` accepts (an identifier, no
coordinate of the object and no basis vector of the module), and a
certificate that `checkCertificate` accepts for the endomorphism's rows. -/
def checkSpectrum (env : Environment) (family object endomorphism : DeclId) (fiber : String)
    (certificate : SpectralCertificate) : Bool :=
  declaredAt env (isSpectrumFamily env family) family object &&
    match smoothCoordinates? env object, endomorphismData? env endomorphism with
    | some coordinates, some (_, endomorphismObject, module, rows, _) =>
      endomorphismObject == object &&
        (match freeModuleData? env module with
          | some (_, _, basis) => fiberValid coordinates basis fiber
          | none => false) &&
        (checkCertificate coordinates.length rows certificate).isOk
    | _, _ => false

/-- The branch declaration `branch family object spectrum localize witness
exponent quotient`: a `branch` family applied to a declared smooth object of
dimension `m`, a spectrum of that object of an endomorphism of rank `n`, and
a gap certificate that `checkWitness` accepts for the spectrum's `χ`. -/
def checkBranch (env : Environment) (family object spectrum : DeclId) (localize witness : Poly)
    (exponent : Nat) (quotient : Poly) : Bool :=
  declaredAt env (isBranchFamily env family) family object &&
    match smoothDimension? env object, spectrumData? env spectrum with
    | some m, some (_, spectrumObject, endomorphism, _, certificate) =>
      spectrumObject == object &&
        match endomorphismData? env endomorphism with
        | some (_, _, _, rows, _) =>
          (checkWitness m rows.length certificate.characteristic localize witness exponent quotient).isOk
        | none => false
    | _, _ => false

end VastitasKernel.SpectralDeclarations
