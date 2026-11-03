import VastitasKernel.AlgebraRuntime
import VastitasKernel.Limits

/-! Budgeted Gröbner bases for presented QQ-algebras.

`compute` runs Buchberger's algorithm with cofactor tracking and returns a
reduced, monic basis together with its cofactors. `verify` is an independent
check of a stored certificate:

- the basis is canonical, monic, strictly ordered and reduced;
- every basis element equals the stated combination of the relations;
- every relation divides to remainder zero, with the quotient identity
  checked exactly;
- every S-pair divides to remainder zero, with the quotient identity and
  the standard-representation bound checked exactly.

Acceptance uses only `verify`, so `compute` is not trusted. Every operation is
charged against `algebraWork`, and every produced polynomial against
`algebraTerms`. That Buchberger's criterion makes these normal forms
canonical is a mathematical theorem proved in the mathlib bridge; this
module checks only the exact identities above. -/
namespace VastitasKernel.AlgebraBasis

open AlgebraRuntime

inductive Error where
  | limit (resource : String)
  | invalid (reason : String)
  | base (reason : String)
  | coordinate (reason : String)
  deriving Repr, DecidableEq, Inhabited

def Error.code : Error → String
  | .limit _ => "E_LIMIT"
  | .invalid _ => "E_AFFINE_RELATION"
  | .base _ => "E_AFFINE_BASE"
  | .coordinate _ => "E_AFFINE_COORDINATE"

def Error.message : Error → String
  | .limit resource => s!"algebraic {resource} limit exceeded"
  | .invalid reason | .base reason | .coordinate reason => reason

/-- Checker work: the state counts weighted term operations. -/
abbrev Work := StateT Nat (Except Error)

def termWeight (t : Term) : Nat :=
  1 + (t.coefficient.num.natAbs.log2 + t.coefficient.den.log2) / 64

def cost (p : Poly) : Nat := p.foldl (fun total t => total + termWeight t) 0

def charge (amount : Nat) : Work Unit := do
  let used := (← get) + amount
  if used > Limits.algebraWork then throw (.limit "work")
  set used

def bounded (p : Poly) : Work Poly := do
  if p.length > Limits.algebraTerms then throw (.limit "term")
  pure p

def add (p q : Poly) : Work Poly := do
  charge (cost p + cost q + 1)
  bounded (Poly.add p q)

def mul (p q : Poly) : Work Poly := do
  charge (cost p * cost q + 1)
  bounded (Poly.mul p q)

def mulTerm (t : Term) (p : Poly) : Work Poly := do
  charge (cost p + 1)
  bounded (Poly.mulTerm t p)

def sub (p q : Poly) : Work Poly := do
  charge (cost p + cost q + 1)
  bounded (Poly.sub p q)

/-- Budgeted division. It takes the same steps as `AlgebraRuntime.divide`. -/
def divide (divisors : List Poly) (p : Poly) : Work Division :=
  go (divisionFuel p) (Division.start divisors p)
where
  divisorCost : Nat := divisors.foldl (fun total g => total + cost g) 0
  go : Nat → Division → Work Division
    | 0, state => pure {state with remainder := Poly.add state.remainder state.rest, rest := []}
    | fuel + 1, state => do
      charge (cost state.rest + divisorCost + 1)
      match Division.step divisors state with
      | some next =>
        if next.rest.length > Limits.algebraTerms || next.remainder.length > Limits.algebraTerms then
          throw (.limit "term")
        go fuel next
      | none => pure state

/-- `Σ coefficients[i] * generators[i]`, computed without budget. -/
def combination (coefficients generators : List Poly) : Poly :=
  (coefficients.zip generators).foldl (fun total (c, g) => Poly.add total (Poly.mul c g)) []

def combinationCost (coefficients generators : List Poly) : Nat :=
  (coefficients.zip generators).foldl (fun total (c, g) => total + cost c * cost g + cost c + cost g) 1

def combine (coefficients generators : List Poly) : Work Poly := do
  charge (combinationCost coefficients generators)
  bounded (combination coefficients generators)

def leadingMonomials (basis : List Poly) : List Monomial :=
  basis.filterMap fun g => g.leading?.map (·.monomial)

/-- Strictly decreasing leading monomials. -/
def strictlyOrdered : List Monomial → Bool
  | [] | [_] => true
  | a :: b :: rest => Monomial.compare a b == .gt && strictlyOrdered (b :: rest)

def monic (g : Poly) : Bool := g.leading?.map (·.coefficient == 1) == some true

/-- No term of any element is divisible by the leading monomial of another. -/
def reduced (basis : List Poly) : Bool :=
  let indexed := basis.zipIdx
  indexed.all fun (g, i) => indexed.all fun (h, j) =>
    i == j || match h.leading? with
      | some lead => g.all fun t => !lead.monomial.divides t.monomial
      | none => false

def shapeValid (arity : Nat) (basis : List Poly) : Bool :=
  basis.all (Poly.canonical arity) && basis.all monic &&
    strictlyOrdered (leadingMonomials basis) && reduced basis

/-- The S-polynomial of two monic or non-monic nonzero polynomials, together
with the two term multipliers. -/
def sPolynomialTerms (g h : Poly) : Option (Term × Term) :=
  match g.leading?, h.leading? with
  | some lg, some lh =>
    let l := Monomial.lcm lg.monomial lh.monomial
    some (⟨l.quotient lg.monomial, 1 / lg.coefficient⟩, ⟨l.quotient lh.monomial, 1 / lh.coefficient⟩)
  | _, _ => none

def sPolynomial (g h : Poly) : Poly :=
  match sPolynomialTerms g h with
  | some (a, b) => Poly.sub (Poly.mulTerm a g) (Poly.mulTerm b h)
  | none => []

/-- Every summand `q * g` of a standard representation has leading monomial
at most that of `s`. Zero `s` needs a zero representation, which the exact
identity already forces. -/
def standard (s : Poly) (quotients basis : List Poly) : Bool :=
  match s.leading? with
  | none => true
  | some lead => (quotients.zip basis).all fun (q, g) =>
    match q.leading?, g.leading? with
    | some lq, some lg => Monomial.compare (lq.monomial.mul lg.monomial) lead.monomial != .gt
    | _, _ => true

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter (i < ·)).map (i, ·)

structure Certificate where
  arity : Nat
  relations : List Poly
  basis : List Poly
  cofactors : List (List Poly)
  deriving Repr, DecidableEq, Inhabited

/-- Fail with `error` unless `condition` holds. -/
def ensure (condition : Bool) (error : Error) : Work Unit :=
  if condition then pure () else throw error

def checkRelation (basis : List Poly) (f : Poly) : Work Unit := do
  let division ← divide basis f
  let identity ← combine division.quotients basis
  ensure (division.remainder == [] && identity == f)
    (.invalid "a relation does not reduce to zero modulo the basis")

def checkPair (basis : List Poly) (pair : Nat × Nat) : Work Unit := do
  charge (cost (basis.getD pair.1 []) + cost (basis.getD pair.2 []) + 1)
  let s := sPolynomial (basis.getD pair.1 []) (basis.getD pair.2 [])
  let division ← divide basis s
  let identity ← combine division.quotients basis
  ensure (division.remainder == [] && identity == s && standard s division.quotients basis)
    (.invalid "an S-pair does not reduce to zero modulo the basis")

def checkCofactor (relations : List Poly) (entry : Poly × List Poly) : Work Unit := do
  ensure (entry.2.length == relations.length) (.invalid "cofactor row has the wrong length")
  let identity ← combine entry.2 relations
  ensure (identity == entry.1) (.invalid "a basis element is not the stated combination")

/-- Independent verification of a stored certificate. -/
def verify (certificate : Certificate) : Work Unit := do
  ensure (certificate.arity ≤ Limits.algebraGenerators) (.limit "generator")
  ensure (certificate.relations.length ≤ Limits.algebraRelations) (.limit "relation")
  ensure (certificate.basis.length ≤ Limits.algebraBasis) (.limit "basis")
  ensure (certificate.relations.all (Poly.canonical certificate.arity))
    (.invalid "relations are not canonical")
  ensure (certificate.relations.all (·.length ≤ Limits.algebraTerms)) (.limit "term")
  charge (certificate.basis.foldl (fun total g => total + cost g) 0 *
    (certificate.basis.length + 1) + 1)
  ensure (shapeValid certificate.arity certificate.basis)
    (.invalid "basis is not canonical, monic, ordered and reduced")
  ensure (certificate.cofactors.length == certificate.basis.length)
    (.invalid "cofactor table has the wrong size")
  (certificate.basis.zip certificate.cofactors).forM (checkCofactor certificate.relations)
  certificate.relations.forM (checkRelation certificate.basis)
  (pairs certificate.basis.length).forM (checkPair certificate.basis)

/-! ## Buchberger's algorithm with cofactors (untrusted computation) -/

structure Tracked where
  poly : Poly
  cofactors : List Poly
  deriving Repr, Inhabited

def unitRow (count index : Nat) (arity : Nat) : List Poly :=
  (List.range count).map fun j => if j == index then Poly.one arity else []

def rowAdd (left right : List Poly) : Work (List Poly) :=
  (left.zip right).mapM fun (a, b) => add a b

def rowMulTerm (t : Term) (row : List Poly) : Work (List Poly) := row.mapM (mulTerm t)

def rowMul (q : Poly) (row : List Poly) : Work (List Poly) := row.mapM (mul q)

def rowSub (left right : List Poly) : Work (List Poly) :=
  (left.zip right).mapM fun (a, b) => sub a b

def scaleTracked (value : Rat) (t : Tracked) : Tracked :=
  ⟨Poly.scale value t.poly, t.cofactors.map (Poly.scale value)⟩

/-- Divide a tracked polynomial and update its cofactors. -/
def reduceTracked (divisors : List Tracked) (p : Tracked) : Work Tracked := do
  let division ← divide (divisors.map (·.poly)) p.poly
  let mut row := p.cofactors
  for (q, d) in division.quotients.zip divisors do
    unless q == [] do
      let product ← rowMul q d.cofactors
      row ← rowSub row product
  pure ⟨division.remainder, row⟩

def sTracked (g h : Tracked) : Work Tracked := do
  match sPolynomialTerms g.poly h.poly with
  | none => pure ⟨[], g.cofactors.map fun _ => []⟩
  | some (a, b) =>
    let left ← mulTerm a g.poly
    let right ← mulTerm b h.poly
    let poly ← sub left right
    let leftRow ← rowMulTerm a g.cofactors
    let rightRow ← rowMulTerm b h.cofactors
    pure ⟨poly, ← rowSub leftRow rightRow⟩

/-- Buchberger's first criterion: coprime leading monomials need no S-pair. -/
def coprimeLeading (g h : Poly) : Bool :=
  match g.leading?, h.leading? with
  | some a, some b => (List.zipWith (fun x y => x == 0 || y == 0) a.monomial b.monomial).all id
  | _, _ => true

def intermediateLimit : Nat := 4 * Limits.algebraBasis

def buchberger (initial : List Tracked) : Work (List Tracked) :=
  loop Limits.algebraWork initial.toArray (pairs initial.length)
where
  loop : Nat → Array Tracked → List (Nat × Nat) → Work (List Tracked)
    | 0, _, _ => throw (.limit "work")
    | _, basis, [] => pure basis.toList
    | fuel + 1, basis, (i, j) :: queue => do
      charge 1
      let g := basis.getD i default
      let h := basis.getD j default
      if coprimeLeading g.poly h.poly then loop fuel basis queue else
      let s ← sTracked g h
      let r ← reduceTracked basis.toList s
      if r.poly == [] then loop fuel basis queue else
      if basis.size + 1 > intermediateLimit then throw (.limit "basis")
      let index := basis.size
      loop fuel (basis.push r) (queue ++ (List.range index).map (·, index))

/-- Drop elements whose leading monomial is divisible by another's, keeping
the first of equal leading monomials. -/
def minimize (elements : List Tracked) : List Tracked :=
  let indexed := elements.zipIdx
  indexed.filterMap fun (g, i) =>
    match g.poly.leading? with
    | none => none
    | some lead =>
      let dominated := indexed.any fun (h, j) =>
        i != j && match h.poly.leading? with
          | some other =>
            other.monomial.divides lead.monomial &&
              (other.monomial != lead.monomial || j < i)
          | none => false
      if dominated then none else some g

def insertOrdered (g : Tracked) : List Tracked → List Tracked
  | [] => [g]
  | h :: rest =>
    match g.poly.leading?, h.poly.leading? with
    | some a, some b =>
      if Monomial.compare a.monomial b.monomial == .gt then g :: h :: rest
      else h :: insertOrdered g rest
    | _, _ => h :: insertOrdered g rest

def interreduce (elements : List Tracked) : Work (List Tracked) := do
  let mut result := []
  for (g, i) in elements.zipIdx do
    let others := (elements.zipIdx.filter (·.2 != i)).map (·.1)
    let r ← reduceTracked others g
    match r.poly.leading? with
    | some lead => result := insertOrdered (scaleTracked (1 / lead.coefficient) r) result
    | none => throw (.invalid "interreduction removed a minimal basis element")
  pure result

/-- Compute a reduced, monic basis with cofactors. -/
def computeTracked (arity : Nat) (relations : List Poly) : Work (List Tracked) := do
  if arity > Limits.algebraGenerators then throw (.limit "generator")
  if relations.length > Limits.algebraRelations then throw (.limit "relation")
  unless relations.all (Poly.canonical arity) do throw (.invalid "relations are not canonical")
  unless relations.all (·.length ≤ Limits.algebraTerms) do throw (.limit "term")
  let initial := (relations.zipIdx.filter (·.1 != [])).map fun (f, j) =>
    (⟨f, unitRow relations.length j arity⟩ : Tracked)
  let basis ← buchberger initial
  let result ← interreduce (minimize basis)
  if result.length > Limits.algebraBasis then throw (.limit "basis")
  pure result

/-- Compute a certificate and verify it independently. Both phases share one
work budget. -/
def certify (arity : Nat) (relations : List Poly) : Work Certificate := do
  let tracked ← computeTracked arity relations
  let certificate : Certificate :=
    ⟨arity, relations, tracked.map (·.poly), tracked.map (·.cofactors)⟩
  verify certificate
  pure certificate

def run (action : Work α) : Except Error α := (action.run 0).map (·.1)

end VastitasKernel.AlgebraBasis
