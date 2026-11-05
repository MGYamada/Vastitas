import VastitasKernel.IndexedTypeAudit
import VastitasKernel.IndexedSourceProgram
import VastitasKernel.Limits

set_option autoImplicit false

/-! Compiled reverse Core (#623).

A reverse site is a call whose derivative rule (`PrimitiveDescriptor.reverse`)
is a reverse pass: a pullback in either mode, a differential, or the reverse
pass of a tape that `linearize` builds. The compilation replaces each site of
a checked module by Core of its own:

- the forward Core, at the site, binds the input point `r₀` and the images
  `rᵢ = mᵢ(rᵢ₋₁)` along the maps `m₁, …, m_k` of the site, in application order,
  as ordinary Core values (evaluated points `Smooth<P, Xᵢ>`). `r_k` is the
  primal value; `r₀, …, r_{k-1}` are the residuals;
- the backward Core is a generated function that pulls the seed back along
  `m_k, …, m₁` from the points. A recomputing site passes only `r₀`, and the
  function evaluates the images again.

The maps of a site are read from the checked Core through the derivative
rules: a call whose rule is `chain after before` composes the maps at those
operand positions, and a `let` whose definition can be copied to the site is
read through. Every other map value is one step. A declared map (`morphism`)
is pulled back by its Jacobian table, which the kernel computes from the exact
map; any other map value is pulled back by the runtime reverse pass
(`SmoothRuntime.pullback` in saved mode) over the program it holds. Such a step
evaluates its map forward twice: once for its image, and again inside the
runtime reverse pass. A tape bound by a `let` is read at each of its reverse
passes, which evaluate the forward Core again.

The steps call bindings that the kernel declares for each site
(`smoothApply`, `cotangentJacobian`, a saved `cotangentPullback` for the other
map values and, for a differential, a `fiberVector` for the seed). These
declarations and the generated functions live in the scope of the function
that holds the site, under the names `__vastitas_rd…` and `__vastitas_rf…`,
which no source can spell. The ledger lists every site with its generated
function. `validate` compiles the source module again and requires the
generated module and the ledger to be the result: translation validation by
recompilation, not by an independent checker. `Core.Typing.checkModule` checks
the generated module like any other. A module without a site compiles to
itself. The compilation runs once, on source Core: an opaque step calls a
saved pullback, whose rule is a reverse pass, so compiling generated Core again
would compile that step again.

The compilation rejects no program. A site stays a call of the runtime reverse
pass when its maps cannot be read, when a family of the generated Core does
not apply to one of its objects, or when its declarations or its function's
`let`s would exceed a limit. -/
namespace VastitasKernel.Indexed.Core.Reverse

open VastitasKernel.Indexed

/-! ## Structural equality of Core

`Term` is a nested inductive type without derived decidable equality. The
validation compares Core with these structural tests. -/

mutual
/-- Structural equality of Core terms: the same constructor and equal fields. -/
def termEq : Term → Term → Bool
  | .natural a, .natural b => decide (a = b)
  | .integer a, .integer b => decide (a = b)
  | .boolean a, .boolean b => decide (a = b)
  | .unit, .unit => true
  | .variable s r, .variable s' r' => decide (s = s') && decide (r = r')
  | .unary o x r, .unary o' x' r' => decide (o = o') && termEq x x' && decide (r = r')
  | .binary o x y r, .binary o' x' y' r' =>
    decide (o = o') && termEq x x' && termEq y y' && decide (r = r')
  | .pair e x y, .pair e' x' y' => decide (e = e') && termEq x x' && termEq y y'
  | .project e f x, .project e' f' x' => decide (e = e') && decide (f = f') && termEq x x'
  | .natToInt x, .natToInt x' => termEq x x'
  | .ascribe a x, .ascribe a' x' => decide (a = a') && termEq x x'
  | .primitive i xs r, .primitive i' xs' r' => decide (i = i') && termsEq xs xs' && decide (r = r')
  | .call i xs s r, .call i' xs' s' r' =>
    decide (i = i') && termsEq xs xs' && decide (s = s') && decide (r = r')
  | .branch c y n r, .branch c' y' n' r' => termEq c c' && termEq y y' && termEq n n' && decide (r = r')
  | .pack a w fs, .pack a' w' fs' => decide (a = a') && termEq w w' && termsEq fs fs'
  | .unpack w fs p b, .unpack w' fs' p' b' =>
    decide (w = w') && decide (fs = fs') && termEq p p' && termEq b b'
  | .scope b, .scope b' => termEq b b'
  | .letE s v b, .letE s' v' b' => decide (s = s') && termEq v v' && termEq b b'
  | _, _ => false

/-- Structural equality of lists of Core terms. -/
def termsEq : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => termEq a b && termsEq as bs
  | _, _ => false
end

/-- Structural equality of Core functions. -/
def functionEq (a b : Function) : Bool :=
  decide (a.id = b.id) && decide (a.definition = b.definition) && decide (a.parameters = b.parameters) &&
    decide (a.returnType = b.returnType) && termEq a.body b.body && decide (a.span = b.span)

/-- Structural equality of lists of Core functions. -/
def functionsEq : List Function → List Function → Bool
  | [], [] => true
  | a :: as, b :: bs => functionEq a b && functionsEq as bs
  | _, _ => false

/-- Structural equality of Core modules. -/
def moduleEq (a b : Module) : Bool :=
  decide (a.declarations = b.declarations) && functionsEq a.functions b.functions && decide (a.main = b.main)

/-! ## Sites -/

/-- How a backward step pulls a covector back along one map. -/
inductive StepKind where
  /-- Along the declared map `morphism` of type `application`, by the Jacobian
  table of `map`. -/
  | declared (morphism : DeclId) (application : Application) (map : AlgebraRuntime.Map)
  /-- Along a map value whose structure the compilation does not open, by the
  reference pass over the program it holds. The value is a parameter of the
  generated function. -/
  | opaque
  deriving Repr, Inhabited, DecidableEq

/-- One map of a site: how it is pulled back, and its source and target. -/
structure Step where
  kind : StepKind
  source : DeclId
  target : DeclId
  deriving Repr, Inhabited, DecidableEq

/-- What determines the backward Core of a site: the smooth and cotangent
families, the 0-dimensional object of its points, its maps in application
order and its residual policy. `saved` passes every point; `recomputed` passes
the input point only. -/
structure Site where
  smooth : DeclId
  cotangent : DeclId
  point : DeclId
  steps : List Step
  mode : SmoothRuntime.PullbackMode
  deriving Repr, Inhabited, DecidableEq

/-- How the seed of a site is obtained: from the site's operand, or, for a
differential, as the coordinate covector at the primal value. -/
inductive Seed where
  | operand
  | unit
  deriving Repr, Inhabited, DecidableEq

/-- One compiled site: its index in the module, the scope and id of the
function that holds it, the id of its generated function, and what determines
that function. -/
structure Entry where
  index : Nat
  scope : Namespace.Scope
  caller : Nat
  function : Nat
  site : Site
  seed : Seed
  deriving Repr, Inhabited, DecidableEq

def Site.input (site : Site) : DeclId := (site.steps.head?.map Step.source).getD site.point
def Site.output (site : Site) : DeclId := (site.steps.getLast?.map Step.target).getD site.point
def Site.opaqueSteps (site : Site) : List Step := site.steps.filter fun step => step.kind == .opaque

def pointResult (site : Site) (object : DeclId) : Result :=
  ⟨.indexed ⟨site.smooth, [.object (.global site.point), .object (.global object)]⟩, none⟩
def fiberResult (site : Site) (object : DeclId) : Result :=
  ⟨.indexed ⟨site.cotangent, [.object (.global object)]⟩, none⟩
def mapResult (site : Site) (source target : DeclId) : Result :=
  ⟨.indexed ⟨site.smooth, [.object (.global source), .object (.global target)]⟩, none⟩

/-! ## The declarations of a site -/

/-- The declaration `j` of the site with index `index`, in `scope`. -/
def declId (scope : Namespace.Scope) (index j : Nat) : DeclId := ⟨scope, s!"__vastitas_rd{index}_{j}"⟩

/-- The generated function of the site with index `index`, in `scope`. -/
def functionOwner (scope : Namespace.Scope) (index : Nat) : Namespace.Owner :=
  ⟨scope, s!"__vastitas_rf{index}"⟩

/-- The names the Core of a site calls: the forward step, one backward step per
map, and the seed of a differential. -/
structure Names where
  apply : DeclId
  steps : List DeclId
  seed : DeclId

def Entry.names (entry : Entry) : Names :=
  let k := entry.site.steps.length
  ⟨declId entry.scope entry.index 0, (List.range k).map fun j => declId entry.scope entry.index (j + 1),
    declId entry.scope entry.index (k + 1)⟩

def stepBinding (site : Site) : StepKind → PrimitiveBinding
  | .declared _ application map => .cotangentJacobian site.cotangent application map
  | .opaque => .cotangentPullback site.smooth site.cotangent .saved

/-- The declarations of an entry. -/
def Entry.declarations (entry : Entry) : List NamedPrimitive :=
  let names := entry.names
  let site := entry.site
  [⟨names.apply, .smoothApply site.smooth⟩] ++
    (names.steps.zip site.steps).map (fun (id, step) => ⟨id, stepBinding site step.kind⟩) ++
    match entry.seed with
    | .operand => []
    | .unit => [⟨names.seed, .fiberVector site.cotangent site.smooth site.output⟩]

/-! ## Templates -/

/-- The forward step: the image of the point `input` under `map`, a map of
type `step`. -/
def applyTerm (names : Names) (site : Site) (step : Step) (map input : Term) : Term :=
  .primitive names.apply [map, input] (pointResult site step.target)

/-- The backward step along `step`, declared as `id`: from the covector `seed`
over `output`, the image of `input`, the covector over `input`. `map` is the
map value of an opaque step. -/
def stepTerm (site : Site) (id : DeclId) (step : Step) (map input output seed : Term) : Term :=
  match step.kind with
  | .declared _ _ _ => .primitive id [input, output, seed] (fiberResult site step.source)
  | .opaque => .primitive id [map, input, seed] (fiberResult site step.source)

/-- The map term of each step: the nullary call of a declared map, or the next
of `opaques` for an opaque one. -/
def mapTerms : List Step → List Term → List Term
  | [], _ => []
  | step :: rest, opaques =>
    match step.kind, opaques with
    | .declared morphism application _, _ =>
      .primitive morphism [] ⟨.indexed application, none⟩ :: mapTerms rest opaques
    | .opaque, value :: more => value :: mapTerms rest more
    | .opaque, [] => .unit :: mapTerms rest []

/-- The forward Core: `let rᵢ := apply(mᵢ, rᵢ₋₁)` for each step and map, with
the given symbols, around `body`. `previous` is the point the first step maps. -/
def forwardLets (names : Names) (site : Site) : List Step → List Term → Term → List Nat → Term → Term
  | step :: steps, map :: maps, previous, symbol :: symbols, body =>
    .letE symbol (applyTerm names site step map previous)
      (forwardLets names site steps maps (.variable symbol (pointResult site step.target)) symbols body)
  | _, _, _, _, body => body

/-- One backward step with its declaration, map term, input and output point. -/
abbrev Pull := DeclId × Step × Term × Term × Term

/-- The backward Core: the steps in reverse order from the covector `seed`,
each intermediate covector bound to the next symbol from `next`. The last step
is the result. -/
def backwardChain (site : Site) : List Pull → Term → Nat → Term
  | [], seed, _ => seed
  | [(id, step, map, input, output)], seed, _ => stepTerm site id step map input output seed
  | (id, step, map, input, output) :: rest, seed, next =>
    .letE next (stepTerm site id step map input output seed)
      (backwardChain site rest (.variable next (fiberResult site step.source)) (next + 1))

/-- The steps with their declarations, map terms and points, last step first. -/
def pulls (names : Names) (site : Site) (maps points : List Term) : List Pull :=
  ((names.steps.zip site.steps).zip ((maps.zip points).zip points.tail)).reverse.map
    fun ((id, step), ((map, input), output)) => (id, step, map, input, output)

/-- The parameters of the generated function, numbered from 0: the opaque maps,
the points (`r₀, …, r_k` when saved, `r₀` when recomputed) and the seed. -/
def functionParameters (site : Site) : List Parameter :=
  let opaques := site.opaqueSteps.map fun step => mapResult site step.source step.target
  let points := match site.mode with
    | .saved => pointResult site site.input :: site.steps.map fun step => pointResult site step.target
    | .recomputed => [pointResult site site.input]
  (opaques ++ points ++ [fiberResult site site.output]).zipIdx.map fun (result, symbol) => ⟨symbol, result⟩

/-- The body of the generated function: the backward Core, after the forward
Core when the site recomputes. -/
def backwardBody (names : Names) (site : Site) : Term :=
  let q := site.opaqueSteps.length
  let k := site.steps.length
  let opaques := (site.opaqueSteps.zipIdx).map fun (step, symbol) =>
    Term.variable symbol (mapResult site step.source step.target)
  let maps := mapTerms site.steps opaques
  let start : Term := .variable q (pointResult site site.input)
  match site.mode with
  | .saved =>
    let points := start :: (site.steps.zipIdx).map fun (step, index) =>
      Term.variable (q + 1 + index) (pointResult site step.target)
    let seed : Term := .variable (q + k + 1) (fiberResult site site.output)
    backwardChain site (pulls names site maps points) seed (q + k + 2)
  | .recomputed =>
    let seed : Term := .variable (q + 1) (fiberResult site site.output)
    let symbols := (List.range k).map fun index => q + 2 + index
    let points := start :: (site.steps.zip symbols).map fun (step, symbol) =>
      Term.variable symbol (pointResult site step.target)
    forwardLets names site site.steps maps start symbols
      (backwardChain site (pulls names site maps points) seed (q + k + 2))

/-- The generated function of an entry. -/
def Entry.generated (entry : Entry) : Function where
  id := entry.function
  definition := functionOwner entry.scope entry.index
  parameters := functionParameters entry.site
  returnType := .indexed ⟨entry.site.cotangent, [.object (.global entry.site.input)]⟩
  body := backwardBody entry.names entry.site

/-! ## Reading the maps of a site -/

/-- A `let` definition in scope: its symbol and value, the number of steps of
its maps read in full (at most `reverseLeaves + 1`), and whether every opaque
step of that reading may be copied to another position of the function. -/
structure Def where
  symbol : Nat
  value : Term
  leaves : Nat
  copies : Bool
  deriving Inhabited

/-- The definitions of the `let`s in scope, innermost first. Core forbids
shadowing, so a symbol names one definition at a time. -/
abbrev Defs := List Def

def Defs.find (defs : Defs) (symbol : Nat) : Option Def := defs.find? (·.symbol == symbol)

/-- A term without its type ascriptions. -/
def strip : Term → Term
  | .ascribe _ value => strip value
  | term => term

/-- The derivative rule of a declared primitive. -/
def ruleOf (env : Declarations) (id : DeclId) : ReverseRule :=
  match env.primitive? id with
  | some binding => binding.contract.reverse
  | none => .none

mutual
/-- A term that may be copied to another position of its function: it
evaluates the same there, and copying it duplicates no fresh object. These are
variables, literals and calls of non-allocating primitives on such terms. -/
def copyable (env : Declarations) : Term → Bool
  | .variable _ _ | .natural _ | .integer _ | .boolean _ | .unit => true
  | .ascribe _ value => copyable env value
  | .primitive id arguments _ =>
    match env.primitive? id with
    | some binding => !binding.allocates && copyableAll env arguments
    | none => false
  | _ => false

/-- Every term of the list may be copied. -/
def copyableAll (env : Declarations) : List Term → Bool
  | [] => true
  | term :: rest => copyable env term && copyableAll env rest
end

/-- The maps of a reverse pass, as the derivative rules compose them. -/
inductive Tree where
  /-- A declared map, from its nullary call. -/
  | declared (call : Term) (morphism : DeclId) (map : AlgebraRuntime.Map)
  /-- A map value whose structure is not opened. -/
  | opaque (value : Term)
  /-- `after ∘ before`. -/
  | node (after before : Tree)
  deriving Inhabited

/-- The leaves in application order: `before` first. -/
def Tree.leaves : Tree → List Tree
  | .node after before => before.leaves ++ after.leaves
  | leaf => [leaf]

/-- The opaque leaves in the order the source evaluates them: `after` first. -/
def Tree.evaluationOrder : Tree → List Term
  | .node after before => after.evaluationOrder ++ before.evaluationOrder
  | .opaque value => [value]
  | .declared _ _ _ => []

/-- A leaf charged to the remaining leaf budget; `none` when the budget is
spent. -/
def Tree.charge (tree : Tree) (budget : Nat) : Option (Tree × Nat) :=
  if budget = 0 then none else some (tree, budget - 1)

/-- The number of steps of a map term read in full, at most
`reverseLeaves + 1`, and whether its opaque steps may be copied. A variable is
read through as its definition records. `fuel` bounds the depth. -/
def measure (env : Declarations) (defs : Defs) : Nat → Term → Nat × Bool
  | 0, term => (1, copyable env term)
  | fuel + 1, term =>
    match strip term with
    | .primitive id arguments _ =>
      match ruleOf env id, arguments with
      | .morphism _, [] => (1, true)
      | .chain after before, _ =>
        match arguments[after]?, arguments[before]? with
        | some first, some second =>
          let (left, leftCopies) := measure env defs fuel first
          let (right, rightCopies) := measure env defs fuel second
          (min (left + right) (Limits.reverseLeaves + 1), leftCopies && rightCopies)
        | _, _ => (1, copyable env term)
      | _, _ => (1, copyable env term)
    | .variable symbol _ =>
      match defs.find symbol with
      | some definition =>
        if definition.copies && definition.leaves ≤ Limits.reverseLeaves then (definition.leaves, true) else (1, true)
      | none => (1, true)
    | _ => (1, copyable env term)

/-- The definition that a `let` records. An alias of a recorded `let` records
that `let`'s definition under its own symbol, so a chain of aliases is read in
one step. Core forbids shadowing, so the definition's variables still name
the same bindings at the alias. -/
def Def.record (env : Declarations) (defs : Defs) (symbol : Nat) (value : Term) : Def :=
  let measured : Def :=
    let (leaves, copies) := measure env defs (defs.length + 64) value
    ⟨symbol, value, leaves, copies⟩
  match strip value with
  | .variable source _ =>
    match defs.find source with
    | some definition => { definition with symbol }
    | none => measured
  | _ => measured

/-- Read the maps of a reverse pass from its map operand, with at most `budget`
leaves. `fuel` bounds the depth read through. A variable is read through when
its definition's opaque steps may be copied and its recorded steps fit in the
remaining budget; otherwise it is one step. The record decides before the
reading, so no reading is undone and the work stays within the budget times the
depth. The result is `none` when the operand itself exceeds the budget. -/
def resolve (env : Declarations) (defs : Defs) : Nat → Nat → Term → Option (Tree × Nat)
  | 0, budget, term => Tree.charge (.opaque term) budget
  | fuel + 1, budget, term =>
    match strip term with
    | .primitive id arguments result =>
      match ruleOf env id, arguments with
      | .morphism map, [] => Tree.charge (.declared (.primitive id [] result) id map) budget
      | .chain after before, _ =>
        match arguments[after]?, arguments[before]? with
        | some first, some second => do
          let (first, budget) ← resolve env defs fuel budget first
          let (second, budget) ← resolve env defs fuel budget second
          pure (.node first second, budget)
        | _, _ => Tree.charge (.opaque term) budget
      | _, _ => Tree.charge (.opaque term) budget
    | .variable symbol result =>
      let step := Tree.charge (.opaque (.variable symbol result)) budget
      match defs.find symbol with
      | some definition =>
        if definition.copies && definition.leaves ≤ budget then
          match resolve env defs fuel budget definition.value with
          | some read => some read
          | none => step
        else step
      | none => step
    | _ => Tree.charge (.opaque term) budget

/-- The two global objects of a map type `Smooth<X, Y>` of `smooth`. -/
def mapObjects (smooth : DeclId) (result : Result) : Option (DeclId × DeclId) :=
  match result.type, result.reference with
  | .indexed ⟨family, [.object (.global source), .object (.global target)]⟩, none =>
    if family == smooth then some (source, target) else none
  | _, _ => none

/-- The steps of a tree of maps of `smooth`; `none` when a leaf is not a map
between two global objects. -/
def stepsOf (smooth : DeclId) (leaves : List Tree) : Option (List Step) :=
  leaves.mapM fun
    | .declared call morphism map => do
      let (source, target) ← mapObjects smooth call.result
      pure ⟨.declared morphism ⟨smooth, [.object (.global source), .object (.global target)]⟩ map, source, target⟩
    | .opaque value => do
      let (source, target) ← mapObjects smooth value.result
      pure ⟨.opaque, source, target⟩
    | .node _ _ => none

/-- The smooth family and the two objects of a point `Smooth<P, X>`. -/
def pointObjects (point : Term) : Option (DeclId × DeclId × DeclId) :=
  match point.result.type, point.result.reference with
  | .indexed ⟨family, [.object (.global origin), .object (.global object)]⟩, none => some (family, origin, object)
  | _, _ => none

/-- The family of a covector type `C<X>`. -/
def fiberFamily (result : Result) : Option DeclId :=
  match result.type, result.reference with
  | .indexed ⟨family, [.object (.global _)]⟩, none => some family
  | _, _ => none

/-- The operands of a reverse site read through the derivative rules: the map
term, the point term, the seed term (none for a differential) and the mode. -/
def siteOperands (env : Declarations) (defs : Defs) (id : DeclId) (arguments : List Term) :
    Option (Term × Term × Option Term × SmoothRuntime.PullbackMode) :=
  let tapeOf (term : Term) : Option (Term × Term) :=
    match strip term with
    | .primitive builder [map, point] _ =>
      match ruleOf env builder with
      | .tape => some (map, point)
      | _ => none
    | _ => none
  match ruleOf env id, arguments with
  | .pass (.pullback mode), [map, point, seed] => some (map, point, some seed, mode)
  | .pass .differential, [function, point] => some (function, point, none, .saved)
  | .pass .backward, [tape, seed] =>
    match strip tape with
    | .variable symbol _ => do
      -- A tape bound by a `let`: its map and point are copied to the site.
      let (map, point) ← (defs.find symbol).bind fun definition => tapeOf definition.value
      if copyable env map && copyable env point then some (map, point, some seed, .saved) else none
    | _ => (tapeOf tape).map fun (map, point) => (map, point, some seed, .saved)
  | _, _ => none

/-! ## Rewriting -/

/-- The state of the rewriting: the next free symbol of the current function,
the scope and id of that function, the first id of the generated functions,
the entries compiled so far in the module and the number of declaration ids
of the source module. -/
structure State where
  next : Nat
  scope : Namespace.Scope
  caller : Nat
  base : Nat
  entries : List Entry
  /-- The declaration ids of the source module. -/
  baseIds : Nat
  deriving Inhabited

/-- The compiled form of a site whose operands are already rewritten, or `none`
when the call stays as it is, a call of the runtime reverse pass: the operands
are not read through the rules, an object is not global, a family of the
generated Core does not apply to an object of the site, the map has no step,
or the declarations of the site would exceed the 4096 declaration ids of a
module (`Declarations.Valid`). -/
def compileSite (env : Declarations) (defs : Defs) (state : State) (id : DeclId) (arguments : List Term)
    (result : Result) : Option (Term × State) := do
  let (map, point, seed, mode) ← siteOperands env defs id arguments
  let (smooth, origin, _) ← pointObjects point
  let cotangent ← fiberFamily result
  -- The depth read through is bounded by the `let`s in scope plus 64.
  let tree := match resolve env defs (defs.length + 64) Limits.reverseLeaves map with
    | some (tree, _) => tree
    | none => .opaque map
  let steps ← stepsOf smooth tree.leaves
  guard !steps.isEmpty
  let site : Site := ⟨smooth, cotangent, origin, steps, mode⟩
  -- The generated Core forms points and covectors over every object of the site.
  guard ((site.input :: steps.map Step.target).all fun object =>
    validApplication env.indexed ⟨cotangent, [.object (.global object)]⟩ &&
      validApplication env.indexed ⟨smooth, [.object (.global origin), .object (.global object)]⟩)
  let entry : Entry := ⟨state.entries.length, state.scope, state.caller, state.base + state.entries.length, site,
    if seed.isSome then .operand else .unit⟩
  let used := state.baseIds + (state.entries.map fun entry => entry.declarations.length).sum
  guard (used + entry.declarations.length ≤ 4096)
  let names := entry.names
  -- Bind the opaque map values that are not variables, in the order the
  -- source evaluates them, then the point and the seed.
  let compound := tree.evaluationOrder.filter fun value => match strip value with
    | .variable _ _ => false
    | _ => true
  let symbolOf := compound.zipIdx.map fun (value, offset) => (value, state.next + offset)
  let opaques := (tree.leaves.filterMap fun
    | .opaque value => some value
    | _ => none).map fun value => match strip value with
      | .variable _ _ => value
      | _ =>
        -- The symbol of the first compound leaf structurally equal to this one.
        match symbolOf.find? (fun (other, _) => termEq other value) with
        | some (_, symbol) => .variable symbol value.result
        | none => value
  let start := state.next + compound.length
  let seedSymbol := start + 1
  let firstPoint := start + 2
  let next := firstPoint + steps.length
  let binds := (symbolOf.map fun (value, symbol) => (symbol, value)) ++ [(start, point)]
  let wrap (inner : Term) : Term := binds.foldr (fun (symbol, value) rest => .letE symbol value rest) inner
  let startTerm : Term := .variable start point.result
  let call (arguments : List Term) : Term := .call entry.function arguments [] result
  let state := { state with next, entries := state.entries ++ [entry] }
  match mode, seed with
  | .recomputed, some seedTerm =>
    pure (wrap (.letE seedSymbol seedTerm
      (call (opaques ++ [startTerm, .variable seedSymbol seedTerm.result]))), state)
  | .recomputed, none => none
  | .saved, _ =>
    let symbols := (List.range steps.length).map fun offset => firstPoint + offset
    let points := startTerm :: (steps.zip symbols).map fun (step, symbol) =>
      Term.variable symbol (pointResult site step.target)
    let maps := mapTerms steps opaques
    match seed with
    | some seedTerm =>
      -- The source evaluates the seed before the reverse pass.
      pure (wrap (.letE seedSymbol seedTerm (forwardLets names site steps maps startTerm symbols
        (call (opaques ++ points ++ [.variable seedSymbol seedTerm.result])))), state)
    | none =>
      let last := (points.getLast?).getD startTerm
      let unitSeed : Term := .primitive names.seed [last, .integer 1] (fiberResult site site.output)
      pure (wrap (forwardLets names site steps maps startTerm symbols
        (.letE seedSymbol unitSeed (call (opaques ++ points ++ [.variable seedSymbol unitSeed.result])))), state)

mutual
/-- Rewrite every reverse site of a term, innermost first, with the `let`
definitions in scope. -/
def rewrite (env : Declarations) (defs : Defs) (state : State) : Term → Term × State
  | .unary operator value result =>
    let (value, state) := rewrite env defs state value
    (.unary operator value result, state)
  | .binary operator left right result =>
    let (left, state) := rewrite env defs state left
    let (right, state) := rewrite env defs state right
    (.binary operator left right result, state)
  | .pair element first second =>
    let (first, state) := rewrite env defs state first
    let (second, state) := rewrite env defs state second
    (.pair element first second, state)
  | .project element first value =>
    let (value, state) := rewrite env defs state value
    (.project element first value, state)
  | .natToInt value =>
    let (value, state) := rewrite env defs state value
    (.natToInt value, state)
  | .ascribe annotation value =>
    let (value, state) := rewrite env defs state value
    (.ascribe annotation value, state)
  | .primitive id arguments result =>
    let (arguments, state) := rewriteAll env defs state arguments
    match compileSite env defs state id arguments result with
    | some compiled => compiled
    | none => (.primitive id arguments result, state)
  | .call id arguments substitution result =>
    let (arguments, state) := rewriteAll env defs state arguments
    (.call id arguments substitution result, state)
  | .branch condition yes no result =>
    let (condition, state) := rewrite env defs state condition
    let (yes, state) := rewrite env defs state yes
    let (no, state) := rewrite env defs state no
    (.branch condition yes no result, state)
  | .pack application witness fields =>
    let (witness, state) := rewrite env defs state witness
    let (fields, state) := rewriteAll env defs state fields
    (.pack application witness fields, state)
  | .unpack witness fields package body =>
    let (package, state) := rewrite env defs state package
    let (body, state) := rewrite env defs state body
    (.unpack witness fields package body, state)
  | .scope body =>
    let (body, state) := rewrite env defs state body
    (.scope body, state)
  | .letE symbol value body =>
    let (value, state) := rewrite env defs state value
    let (body, state) := rewrite env (Def.record env defs symbol value :: defs) state body
    (.letE symbol value body, state)
  | term => (term, state)

/-- Rewrite every term of a list, in order. -/
def rewriteAll (env : Declarations) (defs : Defs) (state : State) : List Term → List Term × State
  | [] => ([], state)
  | term :: rest =>
    let (term, state) := rewrite env defs state term
    let (rest, state) := rewriteAll env defs state rest
    (term :: rest, state)
end

mutual
/-- The largest symbol a term binds or reads. -/
def maxSymbol : Term → Nat
  | .variable symbol _ => symbol
  | .unary _ value _ | .project _ _ value | .natToInt value | .ascribe _ value | .scope value => maxSymbol value
  | .binary _ left right _ | .pair _ left right => max (maxSymbol left) (maxSymbol right)
  | .primitive _ arguments _ | .call _ arguments _ _ => maxSymbols arguments
  | .branch condition yes no _ => max (maxSymbol condition) (max (maxSymbol yes) (maxSymbol no))
  | .pack _ witness fields => max (maxSymbol witness) (maxSymbols fields)
  | .unpack witness fields value body =>
    max (max witness (fields.foldl max 0)) (max (maxSymbol value) (maxSymbol body))
  | .letE symbol value body => max symbol (max (maxSymbol value) (maxSymbol body))
  | _ => 0

/-- The largest symbol a list of terms binds or reads. -/
def maxSymbols : List Term → Nat
  | [] => 0
  | term :: rest => max (maxSymbol term) (maxSymbols rest)
end

/-- Rewrite one function. A function whose rewritten body would exceed the
compiler limit `generatedLets`, measured as the elaboration measures it, keeps
its body and its sites. -/
def rewriteFunction (env : Declarations) (base baseIds : Nat) (entries : List Entry) (function : Function) :
    Function × List Entry :=
  let next := max (maxSymbol function.body) ((function.parameters.map Parameter.symbol).foldl max 0) + 1
  let (body, state) := rewrite env [] ⟨next, function.definition.scope, function.id, base, entries, baseIds⟩
    function.body
  if Source.Bodies.generatedLets body ≤ Limits.generatedLets then ({ function with body }, state.entries)
  else (function, entries)

/-- Compile every reverse site of a module. The result is the generated module
and its ledger; a module without a site is returned as it is. -/
def generate (module : Module) : Module × List Entry :=
  let base := (module.functions.map Function.id).foldl max 0 + 1
  let baseIds := module.declarations.ids.length
  let (functions, entries) := module.functions.foldl
    (fun (functions, entries) function =>
      let (function, entries) := rewriteFunction module.declarations base baseIds entries function
      (functions ++ [function], entries)) ([], [])
  if entries.isEmpty then (module, [])
  else
    ({ module with
        declarations := { module.declarations with
          primitives := module.declarations.primitives ++ entries.flatMap Entry.declarations }
        functions := entries.map Entry.generated ++ functions }, entries)

/-- The translation validation of compiled reverse Core: the source module
compiles to exactly `generated` with exactly the ledger `entries`. -/
def validate (source : Module) (entries : List Entry) (generated : Module) : Bool :=
  let (expected, sites) := generate source
  decide (sites = entries) && moduleEq expected generated

/-! ## The compilation stage -/

/-- A checked module with its compiled reverse Core: the generated module,
checked again by the independent Core audit, and its ledger, validated
against the source module. -/
structure Compiled {requireMain : Bool} (source : Typing.CheckedModule requireMain) where
  entries : List Entry
  core : Typing.CheckedModule requireMain
  validated : validate source.module entries core.module = true

/-- Compile the reverse sites of a checked module and check the result again.
A failed check is an internal error, reported with the code `E_INTERNAL_REVERSE`. -/
def compile {requireMain : Bool} (source : Typing.CheckedModule requireMain) :
    Except Diagnostic (Compiled source) := do
  let (generated, entries) := generate source.module
  let internal (diagnostic : Diagnostic) : Diagnostic :=
    { diagnostic with
      code := "E_INTERNAL_REVERSE"
      message := s!"compiled reverse Core failed the Core audit: {diagnostic.message}" }
  let core ← if entries.isEmpty then pure source
    else (Typing.checkModule generated requireMain).mapError internal
  if validated : validate source.module entries core.module = true then
    pure ⟨entries, core, validated⟩
  else throw { code := "E_INTERNAL_REVERSE", message := "compiled reverse Core failed its validation" }

end VastitasKernel.Indexed.Core.Reverse
