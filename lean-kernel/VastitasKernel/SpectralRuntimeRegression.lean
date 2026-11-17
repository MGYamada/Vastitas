import VastitasKernel.SpectralDeclarations
import VastitasKernel.RegressionSupport
import Lean.Compiler.IR.EmitUtil

set_option autoImplicit false

/-! Executable regressions for the spectral runtime (Stage 5, #806). These are
tests, not proofs.

They run the observations of `SpectralRuntime` on the spectral pairs that the
kernel computes and checks (`SpectralDeclarations.certify`,
`checkCertificate`):

- the Stage 5 field `H = rows((x, y), (y, −x))` on the branch with
  localization `x² + y²`: the branch points `((3, 4), ±5)` and `((1, 0), ±1)`,
  the eigenvalue candidate `4` at `(3, 4)` and the origin, where `χ(0, 0) = 0`
  but `g(0) = 0`; the branch differentials `±(3/5, 4/5)`, the eigenprojectors
  `(1/5)[[4, 2], [2, 1]]` and `(1/5)[[1, −2], [−2, 4]]` with `P² = P`,
  `tr P = 1`, `HP = tP`, symmetry, `P₊ + P₋ = I` and `5P₊ − 5P₋ = H(p)`, and
  the implicit-function form against Hellmann–Feynman `tr(P ∂ᵢH)`;
- the module action over `ℚ`: `0` against `N = [[0, 1], [0, 0]]` and `2I`
  against `J = [[2, 1], [0, 2]]` have the same characteristic polynomial and
  the same trace powers, but `annihilates(t)`, `annihilates(t − 2)` and
  `action_entry(t − 2, e1, e2)` tell them apart;
- an element of `A[t]` that involves the coordinates, `f = t − x`, whose
  action `f(H(p)) = H(p) − p₀ I` varies with the point;
- the failure values: `none` and `(0, 0)` off the branch and out of range;
- one projector entry without the matrix (#864): every entry that
  `projectorEntry` gives is the entry of `projectorMatrix`, on and off the
  branch and out of range, for the Stage 5 field and for the rank-4 field
  `diag(x, y, x + y, 1)`, and the compiled code of `projectorEntry`, which
  every generated program links, reaches no evaluated matrix. -/
namespace VastitasKernel.SpectralRuntimeRegression

open VastitasKernel VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime
  VastitasKernel.SpectralRuntime

private def check := RegressionSupport.check "spectral runtime regression failed"

private def x : Poly := Poly.var 2 0
private def y : Poly := Poly.var 2 1
/-- `H = rows((x, y), (y, −x))` on `Plane = Affine(2)[x, y]`. -/
private def stage5 : List (List Poly) := [[x, y], [y, Poly.neg x]]
/-- The localization `g = x² + y²`. -/
private def gap : Poly := Poly.add (Poly.mul x x) (Poly.mul y y)

/-- The certificate that the kernel computes for `H` over `arity`
coordinates, after its check. -/
private def certificateOf (arity : Nat) (rows : List (List Poly)) : IO Indexed.SpectralCertificate := do
  match AlgebraBasis.run (SpectralDeclarations.certify arity rows) with
  | .error error => throw (IO.userError s!"spectral runtime regression: {repr error}")
  | .ok certificate =>
    check "the kernel's certificate passes its check"
      (SpectralDeclarations.checkCertificate arity rows certificate).isOk
    pure certificate

private def point (values : List Rat) : Program := ratPoint values
private def value (t : Rat) : Program := ratPoint [t]

private def projector (certificate : Indexed.SpectralCertificate) (p : List Rat) (t : Rat) : Option Matrix :=
  projectorMatrix gap certificate.characteristic certificate.adjugate (point p) (value t)

private def identity2 : Matrix := [[1, 0], [0, 1]]

private def product (left right : Matrix) : Matrix := FrameRuntime.matrixProduct 2 left right

private def scaled (c : Rat) (m : Matrix) : Matrix := m.map (·.map (c * ·))

private def plus (left right : Matrix) : Matrix := (left.zip right).map fun (a, b) => (a.zip b).map fun (u, v) => u + v

private def transpose (m : Matrix) : Matrix := (List.range 2).map fun j => m.map (·.getD j 0)

/-! ## Branch points of the Stage 5 field -/

#eval show IO Unit from do
  let certificate ← certificateOf 2 stage5
  let χ := certificate.characteristic
  let onAt (p : List Rat) (t : Rat) := onBranch gap χ (point p) (value t)
  check "((3, 4), 5) and ((3, 4), -5) are branch points" (onAt [3, 4] 5 && onAt [3, 4] (-5))
  check "((1, 0), 1) and ((1, 0), -1) are branch points" (onAt [1, 0] 1 && onAt [1, 0] (-1))
  check "4 is no eigenvalue at (3, 4)" (!onAt [3, 4] 4)
  check "the origin is off the chart although χ(0, 0) = 0"
    (!onAt [0, 0] 0 && evalAt χ [0, 0, 0] == 0)
  check "the branch differential is ±(3/5, 4/5) at (3, 4)"
    (branchDifferential gap χ (point [3, 4]) (value 5) == some ⟨[3, 4], [3/5, 4/5]⟩ &&
      branchDifferential gap χ (point [3, 4]) (value (-5)) == some ⟨[3, 4], [-3/5, -4/5]⟩)
  check "the branch differential is ±(1, 0) at (1, 0)"
    (branchDifferential gap χ (point [1, 0]) (value 1) == some ⟨[1, 0], [1, 0]⟩ &&
      branchDifferential gap χ (point [1, 0]) (value (-1)) == some ⟨[1, 0], [-1, 0]⟩)
  check "the branch differential is the failure value off the branch"
    (branchDifferential gap χ (point [3, 4]) (value 4) == none &&
      branchDifferential gap χ (point [0, 0]) (value 0) == none)
  -- The differential is a unit covector for the Euclidean metric: (3/5)² + (4/5)² = 1.
  check "the branch differential at (3, 4) is a unit covector"
    (match branchDifferential gap χ (point [3, 4]) (value 5) with
      | some fiber => dot fiber.components fiber.components == 1
      | none => false)

/-! ## Eigenprojectors -/

#eval show IO Unit from do
  let certificate ← certificateOf 2 stage5
  let some plus5 := projector certificate [3, 4] 5 | check "the projector at ((3, 4), 5) exists" false
  let some minus5 := projector certificate [3, 4] (-5) | check "the projector at ((3, 4), -5) exists" false
  check "P₊ = (1/5)[[4, 2], [2, 1]] and P₋ = (1/5)[[1, -2], [-2, 4]]"
    (plus5 == [[4/5, 2/5], [2/5, 1/5]] && minus5 == [[1/5, -2/5], [-2/5, 4/5]])
  check "P² = P" (product plus5 plus5 == plus5 && product minus5 minus5 == minus5)
  check "tr P = 1" (plus5[0]![0]! + plus5[1]![1]! == 1 && minus5[0]![0]! + minus5[1]![1]! == 1)
  let h := FrameRuntime.matrixAt stage5 [3, 4]
  check "H P = t P" (product h plus5 == scaled 5 plus5 && product h minus5 == scaled (-5) minus5)
  check "P is symmetric" (transpose plus5 == plus5 && transpose minus5 == minus5)
  check "P₊ + P₋ = I" (plus plus5 minus5 == identity2)
  check "5 P₊ − 5 P₋ = H(p)" (plus (scaled 5 plus5) (scaled (-5) minus5) == h)
  check "the projector is the failure value off the branch"
    (projector certificate [3, 4] 4 == none && projector certificate [0, 0] 0 == none)
  let entry (p : List Rat) (t : Rat) (row column : Nat) :=
    projectorEntry gap certificate.characteristic certificate.adjugate (point p) (value t) row column
  check "projector entries are reduced fractions"
    (entry [3, 4] 5 0 0 == (4, 5) && entry [3, 4] 5 0 1 == (2, 5) && entry [3, 4] (-5) 0 1 == (-2, 5) &&
      entry [1, 0] 1 0 0 == (1, 1) && entry [1, 0] 1 1 1 == (0, 1))
  check "projector entries read (0, 0) off the branch and out of range"
    (entry [3, 4] 4 0 0 == (0, 0) && entry [0, 0] 0 0 0 == (0, 0) && entry [3, 4] 5 2 0 == (0, 0) &&
      entry [3, 4] 5 0 2 == (0, 0))
  -- Hellmann–Feynman: the differential is tr(P ∂ᵢH), and ∂ₓH = diag(1, −1), ∂ᵧH = [[0, 1], [1, 0]].
  let hellmann (projector : Matrix) : List Rat :=
    [projector[0]![0]! - projector[1]![1]!, projector[0]![1]! + projector[1]![0]!]
  check "the branch differential is tr(P ∂ᵢH) (Hellmann–Feynman)"
    (branchDifferential gap certificate.characteristic (point [3, 4]) (value 5) ==
        some ⟨[3, 4], hellmann plus5⟩ &&
      branchDifferential gap certificate.characteristic (point [3, 4]) (value (-5)) ==
        some ⟨[3, 4], hellmann minus5⟩)

/-! ## The module action: scalar against Jordan, zero against nilpotent -/

private def k0 (value : Rat) : Poly := Poly.const 0 value
private def matrix0 (rows : List (List Rat)) : List (List Poly) := rows.map (·.map k0)
private def t1 : Poly := Poly.var 1 0
private def shifted : Poly := Poly.sub t1 (Poly.const 1 2)

#eval show IO Unit from do
  let zero := matrix0 [[0, 0], [0, 0]]
  let nilpotent := matrix0 [[0, 1], [0, 0]]
  let scalar := matrix0 [[2, 0], [0, 2]]
  let jordan := matrix0 [[2, 1], [0, 2]]
  let zeroPair ← certificateOf 0 zero
  let nilpotentPair ← certificateOf 0 nilpotent
  let scalarPair ← certificateOf 0 scalar
  let jordanPair ← certificateOf 0 jordan
  check "0 and N have one characteristic polynomial, t²"
    (zeroPair.characteristic == nilpotentPair.characteristic &&
      zeroPair.characteristic == Poly.mul t1 t1)
  check "2I and J have one characteristic polynomial, (t − 2)²"
    (scalarPair.characteristic == jordanPair.characteristic &&
      scalarPair.characteristic == Poly.mul shifted shifted)
  let traces (rows : List (List Poly)) : List (Option Poly) :=
    [1, 2, 3, 4, 5].map fun k => (SpectralDeclarations.tracePowerImage 0 rows k).toOption
  check "2I and J, and 0 and N, have the same trace powers"
    (traces scalar == traces jordan && traces zero == traces nilpotent)
  let here := point []
  check "t annihilates 0 but not N, and t² annihilates both"
    (annihilates zero t1 here && !annihilates nilpotent t1 here &&
      annihilates zero (Poly.mul t1 t1) here && annihilates nilpotent (Poly.mul t1 t1) here)
  check "t − 2 annihilates 2I but not J, and (t − 2)² annihilates both"
    (annihilates scalar shifted here && !annihilates jordan shifted here &&
      annihilates scalar (Poly.mul shifted shifted) here && annihilates jordan (Poly.mul shifted shifted) here)
  check "the entry (e1, e2) of (t − 2)(H) is 0 for 2I and 1 for J"
    (actionEntry scalar shifted here 0 1 == (0, 1) && actionEntry jordan shifted here 0 1 == (1, 1))
  check "the action of t is the matrix itself, and of t² its square"
    (evalMatrixPoly t1 jordan [] == [[2, 1], [0, 2]] && evalMatrixPoly (Poly.mul t1 t1) jordan [] == [[4, 4], [0, 4]])
  check "an entry out of range reads (0, 0)"
    (actionEntry jordan shifted here 2 0 == (0, 0) && actionEntry jordan shifted here 0 2 == (0, 0))

/-! ## Elements that involve the coordinates -/

#eval show IO Unit from do
  -- `f = t − x` in `A[t]`, arity 3: `f(H(p)) = H(p) − p₀ I`.
  let f : Poly := Poly.sub (Poly.var 3 2) (Poly.var 3 0)
  check "(t − x)(H(3, 4)) = H(3, 4) − 3 I"
    (evalMatrixPoly f stage5 [3, 4] == [[0, 4], [4, -6]])
  check "(t − x)(H(1, 0)) = [[0, 0], [0, -2]]" (evalMatrixPoly f stage5 [1, 0] == [[0, 0], [0, -2]])
  -- `χ(H(p)) = 0` at every point (Cayley–Hamilton), here at three of them.
  let certificate ← certificateOf 2 stage5
  check "χ annihilates H(p)"
    ([[3, 4], [1, 0], [0, 0], [-2, 7]].all fun p => annihilates stage5 certificate.characteristic (point p))
  check "the entry (e2, e2) of (t − x)(H(3, 4)) is −6"
    (actionEntry stage5 f (point [3, 4]) 1 1 == (-6, 1))

/-! ## Polynomials in the fiber coordinate -/

#eval check "extend, liftT, degT and tCoefficient read A[t] by powers of t"
  (let p : Poly := [⟨[1, 0, 2], 3⟩, ⟨[0, 1, 1], -1⟩, ⟨[0, 0, 0], 5⟩];
    extend x == [⟨[1, 0, 0], 1⟩] && liftT 2 y == [⟨[0, 1, 2], 1⟩] && degT p == 2 && degT [] == 0 &&
      tCoefficient p 2 == [⟨[1, 0], 3⟩] && tCoefficient p 1 == [⟨[0, 1], -1⟩] &&
      tCoefficient p 0 == [⟨[0, 0], 5⟩] && tCoefficient p 3 == [])

/-! ## One projector entry without the matrix (#864) -/

/-- The entry of `projectorMatrix`, `(0, 0)` off the branch and out of range,
which `projectorEntry` gives without building the matrix. -/
private def matrixFormulation (localize characteristic : Poly) (adjugate : List (List Poly))
    (point value : Program) (row column : Nat) : Int × Int :=
  match projectorMatrix localize characteristic adjugate point value with
  | some matrix => matrixEntry matrix row column
  | none => (0, 0)

/-- Every entry in rows and columns `0, …, size` (the last out of range) at
each branch candidate `(p, t)` is the entry of `projectorMatrix`. -/
private def agreesWithMatrix (localize characteristic : Poly) (adjugate : List (List Poly))
    (candidates : List (List Rat × Rat)) (size : Nat) : Bool :=
  candidates.all fun (p, t) => (List.range (size + 1)).all fun row => (List.range (size + 1)).all fun column =>
    projectorEntry localize characteristic adjugate (point p) (value t) row column ==
      matrixFormulation localize characteristic adjugate (point p) (value t) row column

/-- `diag(x, y, x + y, 1)` on the plane, of rank 4, the rank limit. -/
private def diagonal4 : List (List Poly) :=
  [[x, [], [], []], [[], y, [], []], [[], [], Poly.add x y, []], [[], [], [], Poly.one 2]]

#eval show IO Unit from do
  let certificate ← certificateOf 2 stage5
  check "each entry of the Stage 5 projector is the entry of its matrix, on and off the branch and out of range"
    (agreesWithMatrix gap certificate.characteristic certificate.adjugate
      [([3, 4], 5), ([3, 4], -5), ([1, 0], 1), ([1, 0], -1), ([3, 4], 4), ([0, 0], 0), ([-2, 7], 0)] 2)
  let rank4 ← certificateOf 2 diagonal4
  let entry4 (t : Rat) (row column : Nat) :=
    projectorEntry (Poly.one 2) rank4.characteristic rank4.adjugate (point [1, 2]) (value t) row column
  -- At p = (1, 2) the eigenvalues are 1, 2, 3 and 1; 3 is simple, with χ′ = 2·1·2 = 4 and P = E₃₃.
  check "the rank-4 projector at ((1, 2), 3) reads 1 at (e3, e3) and 0 elsewhere"
    ((List.range 4).all fun row => (List.range 4).all fun column =>
      entry4 3 row column == if row == 2 && column == 2 then (1, 1) else (0, 1))
  check "the rank-4 projector reads (0, 0) off the branch and out of range"
    (entry4 4 2 2 == (0, 0) && entry4 3 4 2 == (0, 0) && entry4 3 2 4 == (0, 0))
  check "each entry of the rank-4 projector is the entry of its matrix"
    (agreesWithMatrix (Poly.one 2) rank4.characteristic rank4.adjugate [([1, 2], 3), ([1, 2], 2), ([1, 2], 4)] 4)

/-- The declarations of the kernel that the compiled code (IR) of `name`
calls or partially applies. Declarations outside the kernel are left out. -/
private def callees (env : Lean.Environment) (name : Lean.Name) : List Lean.Name :=
  match Lean.IR.findEnvDecl env name with
  | some decl => (Lean.IR.collectUsedDecls env [decl]).toList.filter fun callee =>
      (callee.toString.splitOn "VastitasKernel").length > 1
  | none => []

/-- The declarations of the kernel that the compiled code of `pending`
reaches, themselves included and added to `seen`, or `none` if that takes
more than `fuel` steps. -/
private def reachableWithin (env : Lean.Environment) : Nat → List Lean.Name → Lean.NameSet → Option Lean.NameSet
  | _, [], seen => some seen
  | 0, _ :: _, _ => none
  | fuel + 1, name :: rest, seen =>
    if seen.contains name then reachableWithin env fuel rest seen
    else reachableWithin env fuel (callees env name ++ rest) (seen.insert name)

/-- The declarations of the kernel that the compiled code of `name` reaches,
`name` included, within 10 000 steps. -/
private def reachable (env : Lean.Environment) (name : Lean.Name) : Option Lean.NameSet :=
  reachableWithin env 10000 [name] {}

/-- Whether reached code evaluates a polynomial matrix: whether it contains
`FrameRuntime.matrixAt`, `projectorMatrix` or a specialization of either. -/
private def buildsMatrix (reached : Lean.NameSet) : Bool :=
  reached.toList.any fun callee =>
    ["FrameRuntime.matrixAt", "SpectralRuntime.projectorMatrix"].any fun part =>
      (callee.toString.splitOn part).length > 1

#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let some matrix := reachable env ``projectorMatrix
    | check "the compiled projectorMatrix reaches its declarations within the bound" false
  let some reached := reachable env ``projectorEntry
    | check "the compiled projectorEntry reaches its declarations within the bound" false
  check "the compiled projectorMatrix evaluates the adjugate matrix" (buildsMatrix matrix)
  check "the compiled projectorEntry evaluates no matrix" (!buildsMatrix reached)
  check "the compiled projectorEntry evaluates one polynomial at (p, t) and divides it by the slope"
    ([``SmoothRuntime.evalAtSafe, ``slopeAt, ``SmoothRuntime.ratPair].all reached.contains)

end VastitasKernel.SpectralRuntimeRegression
