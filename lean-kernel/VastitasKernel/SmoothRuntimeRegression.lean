import VastitasKernel.SmoothDeclarations
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Executable regressions for the smooth runtime and the metric certificates
(Stage 3). They exercise the acceptance numbers of the Stage 3 example on the
runtime definitions themselves. These are tests, not proofs. -/
namespace VastitasKernel.SmoothRuntimeRegression

open VastitasKernel.AlgebraRuntime VastitasKernel.SmoothRuntime VastitasKernel.SmoothDeclarations

private def check := RegressionSupport.check "smooth runtime regression failed"

private def v (arity index : Nat) : Poly := Poly.var arity index

/-- `f(t) = (t, t²)` from the line to the plane. -/
private def f : Program := .primitive ⟨1, [], [v 1 0, Poly.pow 1 (v 1 0) 2]⟩
/-- `g(x, y) = x² + y` from the plane to the line. -/
private def g : Program := .primitive ⟨2, [], [Poly.add (Poly.pow 2 (v 2 0) 2) (v 2 1)]⟩
/-- The composite `2t²`, declared by hand. -/
private def gf : Program := .primitive ⟨1, [], [Poly.scale 2 (Poly.pow 1 (v 1 0) 2)]⟩
private def sq : Program := .primitive ⟨1, [], [Poly.pow 1 (v 1 0) 2]⟩
private def shearA : Program := .primitive ⟨2, [], [Poly.add (v 2 0) (v 2 1), v 2 1]⟩
private def shearB : Program := .primitive ⟨2, [], [v 2 0, Poly.add (v 2 0) (v 2 1)]⟩

private def x : Program := intPoint [3]
private def fx : Program := .compose f x
private def seed (point : Program) (components : List Rat) : FiberValue :=
  some ⟨coordinates point, components⟩
private def eta : FiberValue := seed (.compose g fx) [1]
private def stepwise : FiberValue := pullback .saved f x (pullback .saved g fx eta)

#eval check "the seed lies over g(f(3)) = 18" (eta == some ⟨[18], [1]⟩)
#eval check "stepwise pullback is 12 at 3" (stepwise == some ⟨[3], [12]⟩)
#eval check "composite program agrees"
  (fiberEqual stepwise (pullback .saved (.compose g f) x eta))
#eval check "composite as one primitive agrees"
  (fiberEqual stepwise (pullback .saved (composite (.compose g f)) x eta))
#eval check "declared composite agrees and denotes the same map"
  (fiberEqual stepwise (pullback .saved gf x eta) && same (.compose g f) gf)
#eval check "recomputed forward values agree"
  (fiberEqual stepwise (pullback .recomputed (.compose g f) x eta))
#eval check "the first-class tape agrees"
  (fiberEqual stepwise (backward (linearize (.compose g f) x) eta))
#eval check "the tape keeps the intermediate point f(3) = (3, 9)"
  ((linearize (.compose g f) x).steps.map (·.input) == [[3], [3, 9]])
#eval check "a compose node records one step per factor; the composite records one"
  ((linearize (.compose g f) x).steps.length == 2 &&
    (linearize (composite (.compose g f)) x).steps.length == 1)
#eval check "the result lies over x" (fiberAt stepwise x && !fiberAt stepwise (intPoint [4]))
#eval check "a seed at 17 fails" (pullback .saved (.compose g f) x (some ⟨[17], [1]⟩) == none)
#eval check "a wrong intermediate basepoint propagates the failure"
  (pullback .saved f x (pullback .saved g (.compose f (intPoint [2])) eta) == none)
#eval check "a tape from 3 rejects a seed at sq(4) = 16"
  (backward (linearize sq x) (seed (.compose sq (intPoint [4])) [1]) == none)
#eval check "a wrong component count fails" (pullback .saved g fx (some ⟨[18], [1, 0]⟩) == none)
#eval check "the failure value reads (0, 0)"
  (component (pullback .saved (.compose g f) x (some ⟨[17], [1]⟩)) 0 == (0, 0))
#eval check "the failure value equals nothing" (!fiberEqual none none)

/-! Steps of compiled reverse Core (#623): an evaluated image and one backward
step by a Jacobian table, against the reverse pass of the runtime. -/
private def mapOf : Program → Map
  | .primitive map => map
  | .compose _ _ => default
private def step (map : Program) (input : Program) (seed : FiberValue) : FiberValue :=
  jacobianStep (mapOf map).images.length (jacobian (mapOf map)) input (applyPoint map input) seed

#eval check "the evaluated image of 3 under f is (3, 9)"
  (coordinates (applyPoint f x) == [3, 9] && coordinates (applyPoint (.compose g f) x) == [18])
#eval check "an evaluated point is a constant map from the 0-dimensional object"
  (applyPoint f x == ratPoint [3, 9] && (mapOf (applyPoint f x)).arity == 0)
#eval check "the Jacobian table of g is (2x, 1)"
  (jacobian (mapOf g) == [[Poly.scale 2 (v 2 0)], [Poly.const 2 1]])
#eval check "a table step equals cot" (transposeApply (jacobian (mapOf g)) [3, 9] [1] == cot (mapOf g) [3, 9] [1])
#eval check "two table steps give 12 dt at 3"
  (step f x (step g (applyPoint f x) eta) == some ⟨[3], [12]⟩)
#eval check "each table step equals the saved pullback along its map"
  ([f, g, gf, sq, shearA, shearB].all fun map =>
    let point := if (mapOf map).arity == 1 then x else intPoint [1, 2]
    let image := coordinates (applyPoint map point)
    [([1] : List Rat), [2, -3]].all fun components =>
      let seed : FiberValue := some ⟨image, components.take image.length⟩
      step map point seed == pullback .saved map point seed)
#eval check "a table step rejects a seed over another point and a wrong component count"
  (step g (applyPoint f x) (some ⟨[17], [1]⟩) == none && step g (applyPoint f x) (some ⟨[18], [1, 0]⟩) == none &&
    step g (applyPoint f x) none == none)
#eval check "the shears at the origin pull dx back to (1, 1) and (2, 1)"
  (let zero := intPoint [0, 0]
   let dx : FiberValue := some ⟨[0, 0], [1, 0]⟩
   step shearA zero (step shearB (applyPoint shearA zero) dx) == some ⟨[0, 0], [1, 1]⟩ &&
     step shearB zero (step shearA (applyPoint shearB zero) dx) == some ⟨[0, 0], [2, 1]⟩)
#eval check "a component of 12 reads (12, 1)" (component stepwise 0 == (12, 1))

private def o : Program := intPoint [0, 0]
#eval check "B ∘ A pulls dx back to (1, 1)"
  (pullback .saved (.compose shearB shearA) o (seed o [1, 0]) == some ⟨[0, 0], [1, 1]⟩)
#eval check "A ∘ B pulls dx back to (2, 1)"
  (pullback .saved (.compose shearA shearB) o (seed o [1, 0]) == some ⟨[0, 0], [2, 1]⟩)
#eval check "identity" (cot (identity 3) [1, 2, 3] [4, 5, 6] == [4, 5, 6])

/-! Stack-safe evaluation (#630). Compiled code runs the work lists of the
runtime in place of its recursive definitions. The checks run them on three
shapes of one chain of noncommuting maps, against folds over the list of maps
that use no program. -/

/-- 113 maps of the plane, applied first to last: shears, a linear map and one
quadratic map in the middle, so that a pullback depends on its point. -/
private def factors : List Map :=
  let block := (List.replicate 8 [mapOf shearA, mapOf shearB, mapOf shearA, mapOf shearA,
    mapOf shearB, ⟨2, [], [Poly.sub (v 2 0) (v 2 1), v 2 0]⟩, mapOf shearB]).flatten
  block ++ [⟨2, [], [Poly.mul (v 2 0) (v 2 1), Poly.add (v 2 0) (v 2 1)]⟩] ++ block
/-- Every node has the maps so far as its `before`. -/
private def deepBefore (maps : List Map) : Program :=
  maps.tail.foldl (fun program map => .compose (.primitive map) program)
    (.primitive (maps.headD default))
/-- Every node has the maps that follow as its `after`. -/
private def deepAfter (maps : List Map) : Program :=
  maps.reverse.tail.foldl (fun program map => .compose program (.primitive map))
    (.primitive (maps.reverse.headD default))
/-- Halves of halves, down to `depth` levels. -/
private def balanced : Nat → List Map → Program
  | depth + 1, maps =>
    let half := maps.length / 2
    if half = 0 then deepBefore maps
    else .compose (balanced depth (maps.drop half)) (balanced depth (maps.take half))
  | 0, maps => deepBefore maps
private def shapes : List Program := [deepBefore factors, deepAfter factors, balanced 12 factors]

/-- The maps with their inputs in application order, and the last output. -/
private def trace : List Map → List Rat → List Step × List Rat
  | [], point => ([], point)
  | map :: maps, point =>
    let (steps, output) := trace maps (apply map point)
    (⟨map, point⟩ :: steps, output)
/-- The seed pulled back along the maps, the last map first. -/
private def chainCot : List Map → List Rat → List Rat → List Rat
  | [], _, seed => seed
  | map :: maps, point, seed => cot map point (chainCot maps (apply map point) seed)
private def start : List Rat := [1, -2]
private def image : List Rat := (trace factors start).2
private def pulled : List Rat := chainCot factors start [3, 5]

#eval check "the pullback of the chain depends on its point"
  (chainCot factors [2, -2] [3, 5] != pulled && pulled.length == 2)
#eval check "forward evaluation applies the maps first to last"
  (shapes.all fun program => program.eval start == image)
#eval check "the forward record lists every map with its input, in order"
  (shapes.all fun program => program.record start == trace factors start)
#eval check "the recomputing pass pulls back along the maps last to first"
  (shapes.all fun program => program.reverse start [3, 5] == pulled)
#eval check "both pullback modes and the tape agree with the fold"
  (shapes.all fun program =>
    let seed : FiberValue := some ⟨image, [3, 5]⟩
    pullback .saved program (intPoint [1, -2]) seed == some ⟨start, pulled⟩ &&
      pullback .recomputed program (intPoint [1, -2]) seed == some ⟨start, pulled⟩ &&
      backward (linearize program (intPoint [1, -2])) seed == some ⟨start, pulled⟩)
#eval check "the three shapes denote one map, which sends the start to the image"
  (shapes.all fun program =>
    same program (deepBefore factors) && apply program.denote start == image &&
      cot program.denote start [3, 5] == pulled)
#eval check "denote keeps the order of noncommuting factors"
  (!same (deepBefore factors) (deepBefore factors.reverse))

/-! Exponents and long polynomials (#630): binary exponentiation, the iterated
polynomial power, and the sums and merges over the terms of a polynomial. -/
#eval check "powers of a rational"
  ((List.range 40).all fun exponent =>
    npow (-3 / 2) exponent == (List.replicate exponent (-3 / 2 : Rat)).foldl (· * ·) 1)
#eval check "2 ^ 1000 and its inverse by squaring"
  (npow 2 1000 == ((2 ^ 1000 : Nat) : Rat) && npow (1 / 2) 1000 == mkRat 1 (2 ^ 1000))
#eval check "the polynomial power multiplies on the right"
  (let q : Poly := Poly.add (v 2 0) (Poly.scale 2 (v 2 1))
   (List.range 12).all fun exponent =>
     Poly.pow 2 q exponent == (List.replicate exponent q).foldl Poly.mul (Poly.one 2))
#eval check "t ↦ t² twelve times is t ↦ t^4096, nested on either side"
  (let power : Program := .primitive ⟨1, [], [[⟨[4096], 1⟩]]⟩
   same (deepBefore (List.replicate 12 (mapOf sq))) power &&
     same (deepAfter (List.replicate 12 (mapOf sq))) power)
#eval check "the derivative of t^4096 is -4096 at -1 and 4096 · 2^4095 at 2"
  (let power : Program := .primitive ⟨1, [], [[⟨[4096], 1⟩]]⟩
   differential power (intPoint [-1]) == some ⟨[-1], [-4096]⟩ &&
     differential power (intPoint [2]) == some ⟨[2], [((4096 * 2 ^ 4095 : Nat) : Rat)]⟩)
#eval check "evaluation, derivative and sum of a polynomial with 3000 terms"
  (let q : Poly := (List.range 3000).reverse.map fun exponent => ⟨[exponent], 1⟩
   evalAt q [1] == 3000 && evalAt (partialDerivative 0 q) [1] == ((2999 * 3000 / 2 : Nat) : Rat) &&
     (partialDerivative 0 q).length == 2999 && Poly.add q q == Poly.scale 2 q &&
     Poly.sub q q == [])

private def p : Program := intPoint [1, 2]
private def dg : FiberValue := differential g p
#eval check "dg = (2, 1) at (1, 2)" (dg == some ⟨[1, 2], [2, 1]⟩)

-- Euclid, Skew and Lorentz, with kernel-computed certificates.
private def euclid : Matrix := [[1, 0], [0, 1]]
private def skew : Matrix := [[2, 1], [1, 1]]
private def lorentz : Matrix := [[1, 0], [0, -1]]
private def inverseOf (gram : Matrix) : Matrix :=
  match certifyNondegenerate 2 gram with
  | .ok inverse => inverse
  | .error _ => []
#eval check "Skew has the exact inverse ((1, -1), (-1, 2))" (inverseOf skew == [[1, -1], [-1, 2]])
#eval check "Euclid gradient (2, 1)" (sharp (inverseOf euclid) dg == some ⟨[1, 2], [2, 1]⟩)
#eval check "Skew gradient (1, 0)" (sharp (inverseOf skew) dg == some ⟨[1, 2], [1, 0]⟩)
#eval check "Lorentz gradient (2, -1)" (sharp (inverseOf lorentz) dg == some ⟨[1, 2], [2, -1]⟩)
#eval check "flat (5, -7) under Skew is (3, -2), and sharp undoes it"
  (flat skew (vector p [5, -7]) == some ⟨[1, 2], [3, -2]⟩ &&
    sharp (inverseOf skew) (flat skew (vector p [5, -7])) == vector p [5, -7])
#eval check "dg(grad) = Skew(grad, grad) = 2" (pairing dg (sharp (inverseOf skew) dg) == (2, 1))
#eval check "pairing at different points reads the failure value"
  (pairing dg (vector (intPoint [3, 4]) [1, 0]) == (0, 0))
#eval check "pairing with different component counts reads the failure value"
  (pairing dg (vector p [1]) == (0, 0))
#eval check "the differential runs one forward pass and agrees with the pullback"
  (differential g p == pullback .saved g p (some ⟨g.eval (coordinates p), [1]⟩))

private def code {α : Type} : Except Error α → String
  | .ok _ => "ok"
  | .error e => e.code
#eval check "diag(1, 0) is not nondegenerate" (code (certifyNondegenerate 2 [[1, 0], [0, 0]]) == "E_METRIC")
#eval check "diag(1, -1) is nondegenerate" (code (certifyNondegenerate 2 lorentz) == "ok")
#eval check "diag(1, -1) is not Riemannian" (code (certifyRiemannian 2 lorentz) == "E_METRIC")
#eval check "Euclid and Skew are Riemannian"
  (code (certifyRiemannian 2 euclid) == "ok" && code (certifyRiemannian 2 skew) == "ok")
#eval check "an asymmetric form is rejected" (code (certifyNondegenerate 2 [[1, 2], [0, 1]]) == "E_METRIC")
#eval check "a wrong-size form is rejected" (code (certifyNondegenerate 2 [[1]]) == "E_METRIC")
#eval check "a row swap needs pivoting"
  (code (certifyNondegenerate 3 [[0, 1, 0], [1, 0, 0], [0, 0, 3]]) == "ok")
#eval check "a 3 × 3 positive definite form is Riemannian"
  (code (certifyRiemannian 3 [[4, 2, 2], [2, 5, 3], [2, 3, 6]]) == "ok")
#eval check "16 dimensions are accepted, 17 are a limit"
  (code (checkObject 16 ((List.range 16).map toString)) == "ok" &&
    code (checkObject 17 ((List.range 17).map toString)) == "E_LIMIT")
#eval check "coordinates must match the dimension and be distinct"
  (code (checkObject 2 ["t"]) == "E_SMOOTH" && code (checkObject 2 ["t", "t"]) == "E_SMOOTH")
#eval check "a smooth map uses its source coordinates and has no relations"
  (code (checkMap 1 2 ⟨1, [], [v 1 0, v 1 0]⟩) == "ok" &&
    code (checkMap 2 1 ⟨1, [], [v 1 0]⟩) == "E_SMOOTH" &&
    code (checkMap 1 1 ⟨1, [v 1 0], [v 1 0]⟩) == "E_SMOOTH" &&
    code (checkMap 1 2 ⟨1, [], [v 1 0]⟩) == "E_SMOOTH")
#eval check "checkMap rejects non-canonical images"
  (code (checkMap 1 1 ⟨1, [], [[⟨[1], 0⟩]]⟩) == "E_SMOOTH" &&
    code (checkMap 1 1 ⟨1, [], [[⟨[0], 1⟩, ⟨[1], 1⟩]]⟩) == "E_SMOOTH" &&
    code (checkMap 1 1 ⟨1, [], [[⟨[1, 0], 1⟩]]⟩) == "E_SMOOTH")

end VastitasKernel.SmoothRuntimeRegression
