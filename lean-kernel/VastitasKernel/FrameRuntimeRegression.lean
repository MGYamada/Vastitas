import VastitasKernel.FrameRuntime
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Executable regressions for the frame runtime (Stage 4, #759). These are
tests, not proofs.

They run every function of `FrameRuntime` on concrete frames of the plane and
of the zero-dimensional object: encoding and decoding, transitions, the
matrices of tangent maps, apply, coapply, compose, entries and equality, with
failure values, mismatched points and wrong lengths. `apply` and `coapply` are
compared with the Stage 3 `pullback` on the same program, and `frameMatrix`
with a matrix product formed from the Jacobian, which the runtime never forms.
The independent reference fixture is checked in
`VastitasAlgebraTest.FrameReferenceRegression`. -/
namespace VastitasKernel.FrameRuntimeRegression

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime VastitasKernel.FrameRuntime

private def check := RegressionSupport.check "frame runtime regression failed"

/-! ## Frames of the plane and of the point

Each frame is `P` and its inverse `Q`, as rows; column `j` of `P` is frame
vector `j`. The constant frames have `P ≠ Pᵀ` and a determinant other than
`±1`, so a transposed or inverted matrix changes the results. -/

private def x : Poly := Poly.var 2 0
private def y : Poly := Poly.var 2 1
private def k (value : Rat) : Poly := Poly.const 2 value

private abbrev Rows := List (List Poly)

/-- The coordinate frame. -/
private def pI : Rows := [[k 1, k 0], [k 0, k 1]]
/-- `b = columns((1, 0), (1, 2))`, det 2. -/
private def pB : Rows := [[k 1, k 1], [k 0, k 2]]
private def qB : Rows := [[k 1, k (-1/2)], [k 0, k (1/2)]]
/-- `b' = columns((2, 1), (-1, 3))`, det 7. -/
private def pB' : Rows := [[k 2, k (-1)], [k 1, k 3]]
private def qB' : Rows := [[k (3/7), k (1/7)], [k (-1/7), k (2/7)]]
/-- `c = columns((1, 1), (0, 3))`, det 3. -/
private def pC : Rows := [[k 1, k 0], [k 1, k 3]]
private def qC : Rows := [[k 1, k 0], [k (-1/3), k (1/3)]]
/-- `c' = columns((1, -1), (2, 1))`, det 3. -/
private def pC' : Rows := [[k 1, k 2], [k (-1), k 1]]
private def qC' : Rows := [[k (1/3), k (-2/3)], [k (1/3), k (1/3)]]
/-- `r = columns((1, 0), (x, 2))`, polynomial in the point, det 2. -/
private def pR : Rows := [[k 1, x], [k 0, k 2]]
private def qR : Rows := [[k 1, Poly.scale (-1/2) x], [k 0, k (1/2)]]
/-- `s = columns((1, y), (0, 1))`, polynomial in the point, det 1. -/
private def pS : Rows := [[k 1, k 0], [y, k 1]]
private def qS : Rows := [[k 1, k 0], [Poly.neg y, k 1]]
/-- The only frame of the zero-dimensional object `Pt`. -/
private def pPt : Rows := []

/-- Every frame of the plane, with its inverse. -/
private def planeFrames : List (Rows × Rows) :=
  [(pI, pI), (pB, qB), (pB', qB'), (pC, qC), (pC', qC'), (pR, qR), (pS, qS)]

private def identity2 : Matrix := [[1, 0], [0, 1]]

/-! ## Maps and points -/

/-- `F(x, y) = (x², xy + y)`. -/
private def square : Program := .primitive ⟨2, [], [Poly.pow 2 x 2, Poly.add (Poly.mul x y) y]⟩
/-- `G(x, y) = (x + y, y)`. -/
private def shear : Program := .primitive ⟨2, [], [Poly.add x y, y]⟩
/-- `H(x, y) = (x + y, 2x + 2y)`, of rank one everywhere. -/
private def rankOne : Program :=
  .primitive ⟨2, [], [Poly.add x y, Poly.add (Poly.scale 2 x) (Poly.scale 2 y)]⟩

private def p : Program := intPoint [3, -1]
private def p' : Program := ratPoint [1/2, 2]
private def origin : Program := intPoint [0, 0]
/-- The point of `Pt`. -/
private def pt : Program := intPoint []

private def at_ (point : Program) (components : List Rat) : FiberValue :=
  some ⟨coordinates point, components⟩

private def samples : List (List Rat) := [[1, 0], [0, 1], [3, -1/2], [2/3, 5]]

/-- The Jacobian of a primitive map at a point, from the formal partial
derivatives. The runtime never forms it; the checks below compare with it. -/
private def jacobianAt : Program → List Rat → Matrix
  | .primitive map, point =>
    map.images.map fun image =>
      (List.range map.arity).map fun j => evalAt (partialDerivative j image) point
  | .compose _ _, _ => []

/-- `Q_c(F(p)) J(p) P_b(p)` from the Jacobian. -/
private def byJacobian (map point : Program) (pb qc : Rows) : FrameMatrixValue :=
  let source := coordinates point
  let target := map.eval source
  some ⟨source, target,
    matrixProduct 2 (matrixProduct 2 (matrixAt qc target) (jacobianAt map source)) (matrixAt pb source)⟩

/-! ## The frames themselves -/

#eval check "the polynomial frame r at (3, -1) is [[1, 3], [0, 2]]"
  (matrixAt pR [3, -1] == [[1, 3], [0, 2]])
#eval check "every frame times its inverse is the identity at three points"
  (planeFrames.all fun (pf, qf) => [[3, -1], [1/2, 2], [0, 0]].all fun point =>
    matrixProduct 2 (matrixAt pf point) (matrixAt qf point) == identity2 &&
      matrixProduct 2 (matrixAt qf point) (matrixAt pf point) == identity2)
#eval check "transposeVec keeps the columns of a matrix with no rows"
  (transposeVec 3 [] [] == [0, 0, 0] && transposeVec 0 [[1], [2]] [5, 7] == [])
#eval check "matrixProduct multiplies rows by columns" (matrixProduct 2 [[1, 2], [3, 4]] [[0, 1], [1, 0]] == [[2, 1], [4, 3]])

/-! ## Encoding and decoding (C4) -/

#eval check "a vector in b: Q(p) v keeps the point"
  (encodeTangent qB (at_ p [3, -1/2]) == at_ p [13/4, -1/4])
#eval check "a covector in b: P(p)ᵀ α keeps the point"
  (encodeCotangent pB (at_ p [2/3, 5]) == at_ p [2/3, 32/3])
#eval check "decoding a vector in b: P(p) a" (decodeTangent pB (at_ p [13/4, -1/4]) == at_ p [3, -1/2])
#eval check "decoding a covector in b: Q(p)ᵀ a" (decodeCotangent qB (at_ p [2/3, 32/3]) == at_ p [2/3, 5])
#eval check "decode ∘ encode and encode ∘ decode are the identity in every frame, at three points"
  (planeFrames.all fun (pf, qf) => [p, p', origin].all fun point => samples.all fun v =>
    decodeTangent pf (encodeTangent qf (at_ point v)) == at_ point v &&
      encodeTangent qf (decodeTangent pf (at_ point v)) == at_ point v &&
      decodeCotangent qf (encodeCotangent pf (at_ point v)) == at_ point v &&
      encodeCotangent pf (decodeCotangent qf (at_ point v)) == at_ point v)
#eval check "the polynomial frame r encodes differently at two points"
  (encodeTangent qR (at_ p [1, 1]) == at_ p [-1/2, 1/2] &&
    encodeTangent qR (at_ p' [1, 1]) == at_ p' [3/4, 1/2])
#eval check "the coordinate frame leaves the components as they are"
  (encodeTangent pI (at_ p [3, -1/2]) == at_ p [3, -1/2] && encodeCotangent pI (at_ p [2/3, 5]) == at_ p [2/3, 5])
#eval check "the failure value is preserved"
  (encodeTangent qB none == none && encodeCotangent pB none == none &&
    decodeTangent pB none == none && decodeCotangent qB none == none &&
    decodeTangent pB (encodeTangent qB none) == none)
#eval check "wrong component counts give the failure value"
  (encodeTangent qB (at_ p [1]) == none && encodeCotangent pB (at_ p [1, 2, 3]) == none &&
    decodeTangent pB (at_ p []) == none && decodeCotangent qB (at_ p [1, 2, 3]) == none)
#eval check "a point of the wrong dimension gives the failure value"
  (encodeTangent qB (some ⟨[3], [1, 2]⟩) == none && decodeCotangent qR (some ⟨[3, -1, 0], [1, 2]⟩) == none)

/-! ## Pairing in frames (C6) -/

#eval check "the pairing in frames does not depend on the frame"
  (planeFrames.all fun (pf, qf) => [p, p'].all fun point => samples.all fun alpha => samples.all fun v =>
    pairing (encodeCotangent pf (at_ point alpha)) (encodeTangent qf (at_ point v)) ==
      pairing (at_ point alpha) (at_ point v))
#eval check "arrays at mismatched points read (0, 0)"
  (pairing (encodeCotangent pB (at_ p [1, 0])) (encodeTangent qB (at_ p' [1, 0])) == (0, 0))
#eval check "arrays read by component and point with the smooth runtime"
  (component (encodeTangent qB (at_ p [3, -1/2])) 0 == (13, 4) &&
    fiberAt (encodeTangent qB (at_ p [3, -1/2])) p && !fiberAt (encodeTangent qB (at_ p [3, -1/2])) p' &&
    fiberEqual (encodeTangent qB (at_ p [3, -1/2])) (at_ p [13/4, -1/4]) &&
    !fiberEqual (encodeTangent qB none) none)
#eval check "a frame array from integers is a fiber at the point"
  (SmoothRuntime.vector p [1, 2] == at_ p [1, 2])

/-! ## Transitions (C5) -/

private def tBB' : FrameMatrixValue := transition p pB qB'
private def tB'B : FrameMatrixValue := transition p pB' qB
private def tBC : FrameMatrixValue := transition p pB qC
private def tB'C : FrameMatrixValue := transition p pB' qC

#eval check "b → b' at (3, -1) is Q_b' P_b" (tBB' == some ⟨[3, -1], [3, -1], [[3/7, 5/7], [-1/7, 3/7]]⟩)
#eval check "b → b is the identity in every frame"
  (planeFrames.all fun (pf, qf) => [p, p'].all fun point =>
    transition point pf qf == some ⟨coordinates point, coordinates point, identity2⟩)
#eval check "b → b' → c equals b → c"
  (FrameRuntime.compose tB'C tBB' == tBC)
#eval check "b → b' and b' → b are inverse"
  (FrameRuntime.compose tB'B tBB' == transition p pB qB && FrameRuntime.compose tBB' tB'B == transition p pB' qB')
#eval check "a transition sends the array of a vector in one frame to its array in the other"
  (samples.all fun v => FrameRuntime.apply tBB' (encodeTangent qB (at_ p v)) == encodeTangent qB' (at_ p v))
#eval check "the transition of a polynomial frame depends on the point"
  (transition p pR qS != transition p' pR qS &&
    transition p pR qS == some ⟨[3, -1], [3, -1], [[1, 3], [1, 5]]⟩)
#eval check "a point of the wrong dimension gives the failure value"
  (transition (intPoint [3]) pB qB' == none && transition p pB pPt == none)

/-! ## Matrices of tangent maps (C7, C8, C9, C11) -/

private def entryOf (m : FrameMatrix) (i j : Nat) : Rat := (m.entries.getD i []).getD j 0

private def mBC : FrameMatrixValue := frameMatrix square p pB qC
private def mB'C' : FrameMatrixValue := frameMatrix square p pB' qC'

#eval check "square at (3, -1) in (b, c)"
  (mBC == some ⟨[3, -1], [9, -4], [[6, 6], [-7/3, 1/3]]⟩)
#eval check "frameMatrix equals Q_c(F(p)) J(p) P_b(p) from the Jacobian"
  ([square, shear, rankOne].all fun map => [p, p', origin].all fun point =>
    planeFrames.all fun (pb, _) => planeFrames.all fun (_, qc) =>
      frameMatrix map point pb qc == byJacobian map point pb qc)
#eval check "the arrays in (b, c) and (b', c') differ"
  (!matrixEqual mBC mB'C')
#eval check "M_b'c' = T_c M_bc T_b"
  (FrameRuntime.compose (transition (applyPoint square p) pC qC') (FrameRuntime.compose mBC tB'B) == mB'C')
#eval check "both arrays decode to the same coordinate-frame array"
  (FrameRuntime.compose (transition (applyPoint square p) pC pI) (FrameRuntime.compose mBC (transition p pI qB)) ==
      frameMatrix square p pI pI &&
    FrameRuntime.compose (transition (applyPoint square p) pC' pI)
        (FrameRuntime.compose mB'C' (transition p pI qB')) == frameMatrix square p pI pI)
#eval check "the compose node gives the matrix of the composite"
  (frameMatrix (Program.compose square shear) p pB qC ==
      frameMatrix (composite (Program.compose square shear)) p pB qC &&
    frameMatrix (Program.compose square shear) p pR qS ==
      frameMatrix (composite (Program.compose square shear)) p pR qS)
#eval check "M(G ∘ F) = M(G at F(p)) M(F at p)"
  ([(pB, qB), (pR, qR), (pC', qC')].all fun (pm, qm) =>
    frameMatrix (Program.compose square shear) p pB qC ==
      FrameRuntime.compose (frameMatrix square (applyPoint shear p) pm qC) (frameMatrix shear p pB qm))
#eval check "a polynomial frame at two points gives two matrices, each at its points"
  (frameMatrix square p pR qS != frameMatrix square p' pR qS &&
    (frameMatrix square p' pR qS).map (·.source) == some [1/2, 2] &&
    (frameMatrix square p' pR qS).map (·.target) == some [1/4, 3])
#eval check "the target frame is evaluated at F(p), not at p"
  (frameMatrix square p pI qS ==
    some ⟨[3, -1], [9, -4], matrixProduct 2 (matrixAt qS [9, -4]) (jacobianAt square [3, -1])⟩ &&
   frameMatrix square p pI qS !=
    some ⟨[3, -1], [9, -4], matrixProduct 2 (matrixAt qS [3, -1]) (jacobianAt square [3, -1])⟩)
#eval check "a rank-one map is rank one in both frame pairs"
  ([frameMatrix rankOne p pB qC, frameMatrix rankOne p pB' qC', frameMatrix rankOne p' pR qS].all fun
    | some m => m.entries.length == 2 && m.entries != [[0, 0], [0, 0]] &&
        entryOf m 0 0 * entryOf m 1 1 - entryOf m 0 1 * entryOf m 1 0 == 0
    | none => false)
#eval check "rankOne at (3, -1) in (b, c)" (frameMatrix rankOne p pB qC == some ⟨[3, -1], [2, 4], [[1, 3], [1/3, 1]]⟩)
#eval check "a frame of the wrong dimension gives the failure value"
  (frameMatrix square p pPt qC == none && frameMatrix square p pB pPt == none)

/-! ## Apply and coapply against the Stage 3 pullback (C7, C10) -/

/-- Coapply in frames, decoded, is the pullback of the covector along the same
program, in both modes. -/
private def coapplyAgrees (map point : Program) (pb qb pc qc : Rows) : Bool :=
  let target := map.eval (coordinates point)
  samples.all fun alpha =>
    let covector : FiberValue := some ⟨target, alpha⟩
    let inFrames := decodeCotangent qb (coapply (frameMatrix map point pb qc) (encodeCotangent pc covector))
    inFrames == pullback .recomputed map point covector && inFrames == pullback .saved map point covector

/-- Apply in frames, decoded, pairs with every covector as the vector pairs
with its pullback: `⟨α, J v⟩ = ⟨Jᵀ α, v⟩`. -/
private def applyAgrees (map point : Program) (pb qb pc qc : Rows) : Bool :=
  let target := map.eval (coordinates point)
  samples.all fun v => samples.all fun alpha =>
    let image := decodeTangent pc (FrameRuntime.apply (frameMatrix map point pb qc) (encodeTangent qb (at_ point v)))
    let covector : FiberValue := some ⟨target, alpha⟩
    image.isSome && pairing covector image == pairing (pullback .saved map point covector) (at_ point v)

#eval check "coapply in frames equals the pullback"
  ([square, shear, rankOne, Program.compose square shear].all fun map => [p, p', origin].all fun point =>
    planeFrames.all fun (pb, qb) => planeFrames.all fun (pc, qc) => coapplyAgrees map point pb qb pc qc)
#eval check "apply in frames is adjoint to the pullback"
  ([square, shear, rankOne, Program.compose square shear].all fun map => [p, p'].all fun point =>
    planeFrames.all fun (pb, qb) => planeFrames.all fun (pc, qc) => applyAgrees map point pb qb pc qc)
#eval check "apply sends an array over the source point to one over the target point"
  (FrameRuntime.apply mBC (at_ p [1, 0]) == some ⟨[9, -4], [6, -7/3]⟩)
#eval check "coapply sends an array over the target point to one over the source point"
  (coapply mBC (some ⟨[9, -4], [1, 0]⟩) == some ⟨[3, -1], [6, 6]⟩)
#eval check "apply needs the source point"
  (FrameRuntime.apply mBC (some ⟨[9, -4], [1, 0]⟩) == none && FrameRuntime.apply mBC (at_ p' [1, 0]) == none)
#eval check "coapply needs the target point" (coapply mBC (at_ p [1, 0]) == none)
#eval check "apply and coapply need one component per coordinate"
  (FrameRuntime.apply mBC (at_ p [1]) == none && FrameRuntime.apply mBC (at_ p [1, 0, 0]) == none &&
    coapply mBC (some ⟨[9, -4], [1]⟩) == none)
#eval check "apply and coapply preserve the failure value"
  (FrameRuntime.apply none (at_ p [1, 0]) == none && FrameRuntime.apply mBC none == none &&
    coapply none (some ⟨[9, -4], [1, 0]⟩) == none && coapply mBC none == none)

/-! ## Compose, entries and equality -/

#eval check "compose needs the middle point"
  (FrameRuntime.compose (frameMatrix square p pC qC) mBC == none &&
    FrameRuntime.compose (frameMatrix square (applyPoint square p) pC qC) mBC != none)
#eval check "compose preserves the failure value"
  (FrameRuntime.compose none mBC == none && FrameRuntime.compose tBB' none == none)
#eval check "entries are reduced fractions" (entry mBC 1 0 == (-7, 3) && entry mBC 0 1 == (6, 1))
#eval check "an entry out of range reads (0, 0)"
  (entry mBC 2 0 == (0, 0) && entry mBC 0 2 == (0, 0))
#eval check "the failure value reads (0, 0)" (entry none 0 0 == (0, 0))
#eval check "matrix equality compares points and entries"
  (matrixEqual mBC (frameMatrix square p pB qC) &&
    !matrixEqual mBC (some ⟨[3, -1], [9, -5], [[6, 6], [-7/3, 1/3]]⟩) &&
    !matrixEqual mBC (some ⟨[3, 0], [9, -4], [[6, 6], [-7/3, 1/3]]⟩))
#eval check "the failure value equals nothing" (!matrixEqual none none && !matrixEqual mBC none)

/-! ## The zero-dimensional object (C11)

`Pt` has the empty frame. A map `Pt → ℝ²` has a `2 × 0` matrix, a map
`ℝ² → Pt` a `0 × 2` matrix and a map `Pt → Pt` a `0 × 0` matrix. -/

/-- The point `(3, -1)` as a map `Pt → ℝ²`. -/
private def toPlane : Program := intPoint [3, -1]
/-- The map `ℝ² → Pt`. -/
private def toPt : Program := .primitive ⟨2, [], []⟩
/-- The identity of `Pt`. -/
private def onPt : Program := .primitive ⟨0, [], []⟩

private def mIn : FrameMatrixValue := frameMatrix toPlane pt pPt qB
private def mOut : FrameMatrixValue := frameMatrix toPt p pB pPt

#eval check "a map Pt → ℝ² has a 2 × 0 matrix" (mIn == some ⟨[], [3, -1], [[], []]⟩)
#eval check "a map ℝ² → Pt has a 0 × 2 matrix" (mOut == some ⟨[3, -1], [], []⟩)
#eval check "a map Pt → Pt has a 0 × 0 matrix" (frameMatrix onPt pt pPt pPt == some ⟨[], [], []⟩)
#eval check "the empty frame encodes and decodes the empty array"
  (encodeTangent pPt (at_ pt []) == at_ pt [] && encodeCotangent pPt (at_ pt []) == at_ pt [] &&
    decodeTangent pPt (at_ pt []) == at_ pt [] && decodeCotangent pPt (at_ pt []) == at_ pt [] &&
    encodeTangent pPt (at_ pt [1]) == none)
#eval check "the transition of the empty frame is the 0 × 0 matrix" (transition pt pPt pPt == some ⟨[], [], []⟩)
#eval check "apply of a 2 × 0 matrix gives the zero vector over the target"
  (FrameRuntime.apply mIn (at_ pt []) == some ⟨[3, -1], [0, 0]⟩)
#eval check "coapply of a 0 × 2 matrix gives the zero covector over the source"
  (coapply mOut (at_ pt []) == some ⟨[3, -1], [0, 0]⟩)
#eval check "apply of a 0 × 2 matrix gives the empty array"
  (FrameRuntime.apply mOut (at_ p [1, 2]) == at_ pt [])
#eval check "coapply of a 2 × 0 matrix gives the empty array" (coapply mIn (some ⟨[3, -1], [1, 2]⟩) == at_ pt [])
#eval check "0 × 2 after 2 × 0 is 0 × 0" (FrameRuntime.compose mOut mIn == some ⟨[], [], []⟩)
#eval check "2 × 0 after 0 × 2 is the zero 2 × 2 matrix"
  (FrameRuntime.compose mIn mOut == some ⟨[3, -1], [3, -1], [[0, 0], [0, 0]]⟩)
#eval check "coapply of the empty matrix agrees with the pullback"
  (decodeCotangent qB (coapply mOut (encodeCotangent pPt (at_ pt []))) == pullback .recomputed toPt p (at_ pt []) &&
    decodeCotangent pPt (coapply mIn (encodeCotangent pB (some ⟨[3, -1], [1, 2]⟩))) ==
      pullback .saved toPlane pt (some ⟨[3, -1], [1, 2]⟩))
#eval check "entries of an empty matrix read (0, 0)" (entry mOut 0 0 == (0, 0) && entry mIn 0 0 == (0, 0))

end VastitasKernel.FrameRuntimeRegression
