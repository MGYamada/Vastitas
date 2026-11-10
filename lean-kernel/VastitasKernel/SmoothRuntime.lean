import VastitasKernel.AlgebraRuntime

/-! Exact runtime for the finite smooth affine profile.

A smooth map between the smooth real affine spaces `ℝⁿ` and `ℝᵐ` of this
profile is a list of `m` polynomials with exact rational coefficients in the
`n` source coordinates. It reuses the canonical sparse polynomials of
`AlgebraRuntime`, always with an empty basis: smooth objects carry no
relations.

A program is the value that checked Core builds from smooth maps. `compose`
makes a node; it never expands the composite. The reverse pass runs over that
node tree. It either saves every forward value on a tape (`Program.forward`,
`Tape.backward`) or recomputes them (`Program.reverse`). The mathematical
operation is `cot`, the transpose of the Jacobian of one map at one point.

Covectors and vectors are fibers: a basepoint and components in the
coordinate coframe or frame. `none` is the checked failure value of a
pullback whose seed does not lie over the output point. It is absorbing and
never equal to a fiber.

The checker and generated programs share these definitions. This module
imports only the algebra runtime: no compiler, oracle or mathlib module.

The oracle and bridge theorems are about the definitions by structural
recursion. A program can build a chain of 2¹⁸ `compose` nodes, an exponent
of 2¹⁸ or a polynomial of more than 10⁵ terms from a short source, so
compiled code must not recurse once per node, per unit of an exponent or per
term of a polynomial. Each such definition has a replacement whose recursive
calls are tail calls, which Lean compiles to a loop, and a `csimp` theorem
that proves the replacement equal to the definition for every input (#630).
Lean compiles every use of the definition, in the kernel and in generated
programs, to the replacement. `dot` and `monomialValue` recurse once per
coordinate and stay as defined: an object has at most 16 coordinates. -/
namespace VastitasKernel.SmoothRuntime

open VastitasKernel.AlgebraRuntime

/-! ## Rational arithmetic on coordinate lists -/

/-- `value ^ exponent`, by recursion on the exponent. -/
def npow (value : Rat) : Nat → Rat
  | 0 => 1
  | exponent + 1 => npow value exponent * value

theorem npow_square (value : Rat) (n : Nat) : npow (value * value) n = npow value (n + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [npow, ih, show n + 1 + (n + 1) = n + n + 1 + 1 by omega, npow, npow, Rat.mul_assoc]

/-- `product * value ^ exponent` by repeated squaring: one squaring per binary
digit of the exponent after the leading one, and one product per digit that
is one. `npow` multiplies once per unit of the exponent. Every recursive call
is a tail call. -/
def npowOnto (product value : Rat) (exponent : Nat) : Rat :=
  if exponent = 0 then product
  else if exponent = 1 then product * value
  else
    npowOnto (if exponent % 2 = 1 then product * value else product) (value * value)
      (exponent / 2)
termination_by exponent
decreasing_by omega

theorem npowOnto_eq (product value : Rat) (exponent : Nat) :
    npowOnto product value exponent = product * npow value exponent := by
  induction exponent using Nat.strongRecOn generalizing product value with
  | _ exponent ih =>
    rw [npowOnto]
    split
    · subst exponent
      rw [npow, Rat.mul_one]
    · split
      · subst exponent
        rw [npow, npow, Rat.one_mul]
      · rw [ih (exponent / 2) (by omega), npow_square]
        split
        · rw [show exponent = exponent / 2 + exponent / 2 + 1 by omega, npow]
          rw [show (exponent / 2 + exponent / 2 + 1) / 2 = exponent / 2 by omega]
          rw [Rat.mul_assoc, Rat.mul_comm value]
        · rw [show exponent / 2 + exponent / 2 = exponent by omega]

/-- The `npow` of compiled code: binary exponentiation. -/
def npowSafe (value : Rat) (exponent : Nat) : Rat := npowOnto 1 value exponent

@[csimp] theorem npow_eq_npowSafe : @npow = @npowSafe := by
  funext value exponent
  rw [npowSafe, npowOnto_eq, Rat.one_mul]

/-- The sum of products of corresponding entries. Extra entries are ignored. -/
def dot : List Rat → List Rat → Rat
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- A matrix as a list of rows. -/
abbrev Matrix := List (List Rat)

/-- The matrix-vector product `G v`. -/
def matVec (matrix : Matrix) (vector : List Rat) : List Rat :=
  matrix.map fun row => dot row vector

/-! ## Evaluation and partial derivatives -/

/-- The value of a monomial at a point. -/
def monomialValue : Monomial → List Rat → Rat
  | exponent :: exponents, coordinate :: coordinates =>
    npow coordinate exponent * monomialValue exponents coordinates
  | _, _ => 1

/-- The value of a polynomial at a point. -/
def evalAt : Poly → List Rat → Rat
  | [], _ => 0
  | t :: p, point => t.coefficient * monomialValue t.monomial point + evalAt p point

/-- `sum` plus the value of a polynomial at a point, one term per tail call. -/
def evalAtOnto (point : List Rat) : Rat → Poly → Rat
  | sum, [] => sum
  | sum, t :: p => evalAtOnto point (sum + t.coefficient * monomialValue t.monomial point) p

theorem evalAtOnto_eq (point : List Rat) (sum : Rat) (p : Poly) :
    evalAtOnto point sum p = sum + evalAt p point := by
  induction p generalizing sum with
  | nil => rw [evalAtOnto, evalAt, Rat.add_zero]
  | cons t p ih => rw [evalAtOnto, ih, evalAt, Rat.add_assoc]

/-- The `evalAt` of compiled code. It adds the terms from the leading one on,
where `evalAt` adds them from the last one on; exact rationals make the sums
equal. -/
def evalAtSafe (p : Poly) (point : List Rat) : Rat := evalAtOnto point 0 p

@[csimp] theorem evalAt_eq_evalAtSafe : @evalAt = @evalAtSafe := by
  funext p point
  rw [evalAtSafe, evalAtOnto_eq, Rat.zero_add]

/-- The formal partial derivative in coordinate `j`. It works term by term.
Lowering one exponent of every surviving term keeps the strict degree-
lexicographic order, so a canonical input gives a canonical output. -/
def partialDerivative (j : Nat) : Poly → Poly
  | [] => []
  | t :: p =>
    let exponent := t.monomial.getD j 0
    if exponent = 0 then partialDerivative j p
    else ⟨t.monomial.set j (exponent - 1), t.coefficient * exponent⟩ :: partialDerivative j p

/-- The formal partial derivative of one term in coordinate `j`, or `none`
when it is zero. -/
def termDerivative (j : Nat) (t : Term) : Option Term :=
  let exponent := t.monomial.getD j 0
  if exponent = 0 then none
  else some ⟨t.monomial.set j (exponent - 1), t.coefficient * exponent⟩

/-- The `partialDerivative` of compiled code: the same terms through
`List.filterMap`, which compiled code runs as a loop. -/
def partialDerivativeSafe (j : Nat) (p : Poly) : Poly := p.filterMap (termDerivative j)

@[csimp] theorem partialDerivative_eq_partialDerivativeSafe :
    @partialDerivative = @partialDerivativeSafe := by
  funext j p
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [partialDerivative, partialDerivativeSafe, List.filterMap_cons, ← partialDerivativeSafe,
      ← ih, termDerivative]
    by_cases zero : t.monomial.getD j 0 = 0 <;> simp only [zero, ↓reduceIte]

/-! ## Smooth maps

A smooth map is an `AlgebraRuntime.Map` with an empty basis. `arity` is the
source dimension and `images` lists the target coordinates as polynomials in
the source coordinates. -/

/-- The image of a point. -/
def apply (map : Map) (point : List Rat) : List Rat :=
  map.images.map fun image => evalAt image point

/-- The identity of `ℝⁿ`. -/
def identity (arity : Nat) : Map :=
  ⟨arity, [], (List.range arity).map (Poly.var arity)⟩

/-- `compose after before`: substitute `before`'s images into `after`'s. With
no relations, no normal form is needed. -/
def compose (after before : Map) : Map :=
  ⟨before.arity, [], after.images.map (Poly.subst before.arity before.images)⟩

/-- The cotangent pullback along one map at one point: `Jᵀ η`. Component `j`
is `Σᵢ ηᵢ ∂ⱼ fᵢ(x)`. -/
def cot (map : Map) (point : List Rat) (seed : List Rat) : List Rat :=
  (List.range map.arity).map fun j =>
    dot seed (map.images.map fun image => evalAt (partialDerivative j image) point)

/-- A map is well formed between dimensions `source` and `target`. -/
def wellFormed (source target : Nat) (map : Map) : Bool :=
  map.arity == source && map.basis.isEmpty && map.images.length == target &&
    map.images.all (Poly.canonical source)

/-! ## Programs -/

/-- The value that checked Core builds from smooth maps. -/
inductive Program where
  | primitive (map : Map)
  | compose (after before : Program)
  deriving Repr, DecidableEq, Inhabited

namespace Program

def inputArity : Program → Nat
  | primitive map => map.arity
  | compose _ before => before.inputArity

def outputArity : Program → Nat
  | primitive map => map.images.length
  | compose after _ => after.outputArity

/-- Every node is a well-formed map and adjacent dimensions agree. -/
def wellTyped : Program → Nat → Nat → Bool
  | primitive map, source, target => wellFormed source target map
  | compose after before, source, target =>
    before.wellTyped source before.outputArity && after.wellTyped before.outputArity target

/-- Forward evaluation. -/
def eval : Program → List Rat → List Rat
  | primitive map, point => apply map point
  | compose after before, point => after.eval (before.eval point)

/-- The single map that the program denotes. -/
def denote : Program → Map
  | primitive map => map
  | compose after before => SmoothRuntime.compose after.denote before.denote

/-- The reverse pass that recomputes forward values. -/
def reverse : Program → List Rat → List Rat → List Rat
  | primitive map, point, seed => cot map point seed
  | compose after before, point, seed =>
    before.reverse point (after.reverse (before.eval point) seed)

/-! ### Work lists

`eval`, `denote` and `reverse` recurse once per `compose` node, and so does
`record` below. Compiled code runs a work list in place of each: the pending
programs are a list, every recursive call is a tail call, and a `csimp`
theorem proves the work list equal to the definition for every program. -/

/-- A bound on the steps of a work list for one program: one per primitive
and two per `compose` node. Every work list terminates by it. Compiled code
does not call it. -/
def workCost : Program → Nat
  | primitive _ => 1
  | compose after before => after.workCost + before.workCost + 2

/-- Evaluate the programs of `work` in order, each at the image of the one
before it. -/
def evalWork : List Program → List Rat → List Rat
  | [], point => point
  | primitive map :: work, point => evalWork work (apply map point)
  | compose after before :: work, point => evalWork (before :: after :: work) point
termination_by work => (work.map workCost).sum
decreasing_by all_goals (simp only [List.map_cons, List.sum_cons, workCost]; omega)

theorem evalWork_cons (program : Program) (work : List Program) (point : List Rat) :
    evalWork (program :: work) point = evalWork work (program.eval point) := by
  induction program generalizing work point with
  | primitive map => rw [evalWork, eval]
  | compose after before ihAfter ihBefore => rw [evalWork, ihBefore, ihAfter, eval]

/-- The `eval` of compiled code. It applies the same maps to the same points
in the same order. The `after` programs that wait for their input are a list;
in `eval` they are stack frames. -/
def evalSafe (program : Program) (point : List Rat) : List Rat := evalWork [program] point

@[csimp] theorem eval_eq_evalSafe : @eval = @evalSafe := by
  funext program point
  rw [evalSafe, evalWork_cons, evalWork]

/-- One pending task of `denoteWork`. -/
inductive DenoteTask where
  /-- Push the map a program denotes. -/
  | visit (program : Program)
  /-- Replace the two maps on top, `before` above `after`, with their composite. -/
  | combine

/-- The steps a task still needs. -/
def DenoteTask.cost : DenoteTask → Nat
  | visit program => program.workCost
  | combine => 1

/-- Run the pending tasks over a stack of maps. A `compose` node becomes the
tasks of its two sides followed by `combine`, so every composite is formed
from the same two maps as in `denote`: the association of the tree is kept. -/
def denoteWork : List DenoteTask → List Map → List Map
  | [], maps => maps
  | .visit (primitive map) :: work, maps => denoteWork work (map :: maps)
  | .visit (compose after before) :: work, maps =>
    denoteWork (.visit after :: .visit before :: .combine :: work) maps
  | .combine :: work, before :: after :: maps =>
    denoteWork work (SmoothRuntime.compose after before :: maps)
  | .combine :: work, maps => denoteWork work maps
termination_by work => (work.map DenoteTask.cost).sum
decreasing_by
  all_goals (simp only [List.map_cons, List.sum_cons, DenoteTask.cost, workCost]; omega)

theorem denoteWork_visit (program : Program) (work : List DenoteTask) (maps : List Map) :
    denoteWork (.visit program :: work) maps = denoteWork work (program.denote :: maps) := by
  induction program generalizing work maps with
  | primitive map => rw [denoteWork, denote]
  | compose after before ihAfter ihBefore => rw [denoteWork, ihAfter, ihBefore, denoteWork, denote]

/-- The `denote` of compiled code. It forms the same composites of the same
two maps, with the pending tasks and the finished maps in two lists. -/
def denoteSafe (program : Program) : Map :=
  match denoteWork [.visit program] [] with
  | map :: _ => map
  | [] => default

@[csimp] theorem denote_eq_denoteSafe : @denote = @denoteSafe := by
  funext program
  rw [denoteSafe, denoteWork_visit, denoteWork]

/-- Pull `seed` back along the programs of `work` in order, each at the point
stored with it. -/
def reverseWork : List (Program × List Rat) → List Rat → List Rat
  | [], seed => seed
  | (primitive map, point) :: work, seed => reverseWork work (cot map point seed)
  | (compose after before, point) :: work, seed =>
    reverseWork ((after, before.eval point) :: (before, point) :: work) seed
termination_by work => (work.map fun entry => entry.1.workCost).sum
decreasing_by all_goals (simp only [List.map_cons, List.sum_cons, workCost]; omega)

theorem reverseWork_cons (program : Program) (point : List Rat)
    (work : List (Program × List Rat)) (seed : List Rat) :
    reverseWork ((program, point) :: work) seed =
      reverseWork work (program.reverse point seed) := by
  induction program generalizing point work seed with
  | primitive map => rw [reverseWork, reverse]
  | compose after before ihAfter ihBefore => rw [reverseWork, ihAfter, ihBefore, reverse]

/-- The `reverse` of compiled code. It is the recomputing pass, not a taped
one: it evaluates `before.eval point` once per `compose` node, as `reverse`
does, so its time is quadratic in the length of a chain that is deep in
`before` and linear in one that is deep in `after`. It keeps the input point
of every `before` program that waits for its seed; `reverse` keeps the same
points in its stack frames. -/
def reverseSafe (program : Program) (point seed : List Rat) : List Rat :=
  reverseWork [(program, point)] seed

@[csimp] theorem reverse_eq_reverseSafe : @reverse = @reverseSafe := by
  funext program point seed
  rw [reverseSafe, reverseWork_cons, reverseWork]

end Program

/-! ## Saved forward values -/

/-- One primitive node and the input point it was evaluated at. -/
structure Step where
  map : Map
  input : List Rat
  deriving Repr, DecidableEq, Inhabited

/-- The saved forward values of one evaluation: every primitive node with its
input point, in evaluation order. -/
structure Tape where
  input : List Rat
  output : List Rat
  steps : List Step
  deriving Repr, DecidableEq, Inhabited

namespace Program

/-- The steps of a forward evaluation, and its output. -/
def record : Program → List Rat → List Step × List Rat
  | primitive map, point => ([⟨map, point⟩], apply map point)
  | compose after before, point =>
    let (beforeSteps, middle) := before.record point
    let (afterSteps, output) := after.record middle
    (beforeSteps ++ afterSteps, output)

theorem record_of_compose (after before : Program) (point : List Rat) :
    (compose after before).record point =
      ((before.record point).1 ++ (after.record (before.record point).2).1,
        (after.record (before.record point).2).2) := rfl

/-- Record the programs of `work` in order, each at the output of the one
before it. `steps` holds the steps so far, last step first. -/
def recordWork : List Program → List Step → List Rat → List Step × List Rat
  | [], steps, point => (steps.reverse, point)
  | primitive map :: work, steps, point =>
    recordWork work (⟨map, point⟩ :: steps) (apply map point)
  | compose after before :: work, steps, point => recordWork (before :: after :: work) steps point
termination_by work => (work.map workCost).sum
decreasing_by all_goals (simp only [List.map_cons, List.sum_cons, workCost]; omega)

theorem recordWork_cons (program : Program) (work : List Program) (steps : List Step)
    (point : List Rat) :
    recordWork (program :: work) steps point =
      recordWork work ((program.record point).1.reverse ++ steps) (program.record point).2 := by
  induction program generalizing work steps point with
  | primitive map => rw [recordWork, record]; rfl
  | compose after before ihAfter ihBefore =>
    rw [recordWork, ihBefore, ihAfter, record_of_compose, List.reverse_append, List.append_assoc]

/-- The `record` of compiled code. It makes every step once and reverses the
list at the end, so its time is linear in the number of nodes. `record`
appends at every `compose` node, which copies the steps of `before`: its
time is quadratic in the length of a chain that is deep in `before`. -/
def recordSafe (program : Program) (point : List Rat) : List Step × List Rat :=
  recordWork [program] [] point

@[csimp] theorem record_eq_recordSafe : @record = @recordSafe := by
  funext program point
  rw [recordSafe, recordWork_cons, recordWork, List.append_nil, List.reverse_reverse]

/-- Evaluate once and save every forward value. -/
def forward (program : Program) (point : List Rat) : Tape :=
  let (steps, output) := program.record point
  ⟨point, output, steps⟩

end Program

/-- The reverse pass over saved forward values: the last step first. -/
def backwardSteps (steps : List Step) (seed : List Rat) : List Rat :=
  steps.foldr (fun step current => cot step.map step.input current) seed

/-! ## Fibers -/

/-- A covector or vector: a basepoint and components in the coordinate coframe
or frame at that point. -/
structure Fiber where
  point : List Rat
  components : List Rat
  deriving Repr, DecidableEq, Inhabited

/-- A fiber, or the checked failure value `none`. -/
abbrev FiberValue := Option Fiber

/-- How the reverse pass obtains forward values. -/
inductive PullbackMode where
  | saved
  | recomputed
  deriving Repr, DecidableEq, Inhabited

/-- The coordinates of a point, given as a program from the point object. -/
def coordinates (point : Program) : List Rat := point.eval []

/-- Save the forward values of `map` at `point`. -/
def linearize (map point : Program) : Tape := map.forward (coordinates point)

/-- The reverse pass over a tape. `none` unless the seed lies over the tape's
output and has one component per output coordinate. -/
def backward (tape : Tape) (seed : FiberValue) : FiberValue :=
  match seed with
  | none => none
  | some seed =>
    if seed.point == tape.output && seed.components.length == tape.output.length then
      some ⟨tape.input, backwardSteps tape.steps seed.components⟩
    else none

/-- The pullback of `seed` along `map` at `point`. It is `none` unless the seed
lies over the image of the point and has one component per target
coordinate. The saved mode runs the forward pass once and checks the seed
against the tape's output; the recomputing mode evaluates forward values
again during the reverse pass. -/
def pullback (mode : PullbackMode) (map point : Program) (seed : FiberValue) : FiberValue :=
  match mode with
  | .saved => backward (linearize map point) seed
  | .recomputed =>
    match seed with
    | none => none
    | some seed =>
      let source := coordinates point
      if seed.point == map.eval source && seed.components.length == map.outputArity then
        some ⟨source, map.reverse source seed.components⟩
      else none

/-- The differential of a smooth function `φ : X → Affine(1)` at `point`: the
pullback of the coordinate covector `dt` at `φ(point)`. It runs the forward
pass once. -/
def differential (function point : Program) : FiberValue :=
  let tape := linearize function point
  backward tape (some ⟨tape.output, [1]⟩)

/-- A fiber at `point` from integer components. -/
def vector (point : Program) (components : List Int) : FiberValue :=
  some ⟨coordinates point, components.map fun c : Int => (c : Rat)⟩

/-- Whether a fiber lies over `point`. The failure value lies over nothing. -/
def fiberAt (value : FiberValue) (point : Program) : Bool :=
  match value with
  | some fiber => fiber.point == coordinates point
  | none => false

/-- Equality of fibers. The failure value equals nothing, itself included. -/
def fiberEqual : FiberValue → FiberValue → Bool
  | some left, some right => left == right
  | _, _ => false

/-- A reduced numerator and positive denominator. -/
def ratPair (value : Rat) : Int × Int := (value.num, value.den)

/-- Component `index` as a rational. The failure value reads `(0, 0)`, which
no rational has. -/
def component (value : FiberValue) (index : Nat) : Int × Int :=
  match value with
  | some fiber => ratPair (fiber.components.getD index 0)
  | none => (0, 0)

/-- The metric-free pairing of a covector with a vector at the same point.
Mismatched points or lengths, and failure values, read `(0, 0)`. -/
def pairing (covector vector : FiberValue) : Int × Int :=
  match covector, vector with
  | some alpha, some v =>
    if alpha.point == v.point && alpha.components.length == v.components.length then
      ratPair (dot alpha.components v.components)
    else (0, 0)
  | _, _ => (0, 0)

/-- Apply a matrix to the components of a fiber. -/
def transform (matrix : Matrix) (value : FiberValue) : FiberValue :=
  value.map fun fiber => ⟨fiber.point, matVec matrix fiber.components⟩

/-- `flat`: lower a vector with a Gram matrix `G`. -/
def flat (gram : Matrix) (value : FiberValue) : FiberValue := transform gram value

/-- `sharp`: raise a covector with the checked inverse `B` of a Gram matrix. -/
def sharp (inverse : Matrix) (value : FiberValue) : FiberValue := transform inverse value

/-- A rational point of `ℝⁿ` from integer coordinates: a map from `ℝ⁰`. -/
def intPoint (values : List Int) : Program := .primitive (Map.intPoint values)

/-- Equality of the maps two programs denote, for two programs checked at one
type `Smooth<X, Y>`. It compares images only: maps with different sources
can have equal images. Canonical polynomials make this exact equality of
polynomial maps. -/
def same (left right : Program) : Bool := left.denote.images == right.denote.images

/-- The composite as one primitive. -/
def composite (program : Program) : Program := .primitive program.denote

/-! ## Compiled reverse passes

The kernel compiles a reverse pass into Core whose steps call the two
operations below (#623). The forward Core evaluates each map at the point the
previous step produced and keeps the result as an evaluated point. The
backward Core pulls the seed back one map at a time. For a declared map, the
step evaluates a table of partial derivatives. The generated program declares
each distinct table once as a literal, which the kernel computes once per map
when it lowers the module, and every step names its table, so no derivative is
formed while the program runs. The kernel's own evaluator, which the checker
and the regressions use, computes the table again at every step it evaluates. -/

/-- A rational point of `ℝⁿ` from its coordinates: a map from `ℝ⁰` with
constant images. -/
def ratPoint (values : List Rat) : Program := .primitive ⟨0, [], values.map (Poly.const 0)⟩

/-- The image of a point under a program, as an evaluated point. -/
def applyPoint (map point : Program) : Program := ratPoint (map.eval (coordinates point))

/-- The Jacobian table of a map: entry `j` lists the partial derivative in
coordinate `j` of every image, in target order. -/
def jacobian (map : Map) : List (List Poly) :=
  (List.range map.arity).map fun j => map.images.map (partialDerivative j)

/-- `Jᵀ η` at a point from a Jacobian table: component `j` is `Σᵢ ηᵢ ∂ⱼfᵢ(x)`. -/
def transposeApply (table : List (List Poly)) (point seed : List Rat) : List Rat :=
  table.map fun column => dot seed (column.map fun derivative => evalAt derivative point)

/-- One step of a compiled reverse pass along a declared map with `outputs`
target coordinates and Jacobian table `table`. `input` is the point the map was
evaluated at and `output` its saved image. The step is `none` unless the seed
lies over `output` and has one component per target coordinate. -/
def jacobianStep (outputs : Nat) (table : List (List Poly)) (input output : Program)
    (seed : FiberValue) : FiberValue :=
  match seed with
  | none => none
  | some seed =>
    if seed.point == coordinates output && seed.components.length == outputs then
      let point := coordinates input
      some ⟨point, transposeApply table point seed.components⟩
    else none

end VastitasKernel.SmoothRuntime
