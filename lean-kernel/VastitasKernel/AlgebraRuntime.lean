/-! Exact rational polynomial runtime for the finite Stage 2 affine profile.

Polynomials have one explicit arity and exact `Rat` coefficients, and are kept
in a canonical sparse form: nonzero coefficients, with strictly decreasing
monomials in the degree-lexicographic order. That order compares total degree
first, then exponents lexicographically with coordinate 0 most significant.

The checker and generated programs share these definitions. Statically
checked bases make normal forms meaningful. This module never decides
whether a basis is a Gröbner basis: `AlgebraBasis` verifies that before code
generation. There are deliberately no compiler, oracle or mathlib imports.

`Poly.add` recurses once per term and `Poly.pow` once per unit of the
exponent, and a generated program can build a polynomial of more than 10⁵
terms or an exponent of 2¹⁸. Each has a replacement whose recursive calls are
tail calls, which Lean compiles to a loop, and a `csimp` theorem that proves
the replacement equal to the definition for every input (#630). Lean compiles
every use of the definition to the replacement; the theorems of the oracle
and the bridge stay about the definitions. -/
namespace VastitasKernel.AlgebraRuntime

/-- An exponent vector. Every polynomial of one ring uses one arity. -/
abbrev Monomial := List Nat

namespace Monomial

def degree (m : Monomial) : Nat := m.foldr (· + ·) 0

/-- Lexicographic comparison with coordinate 0 most significant. -/
def lexCompare : Monomial → Monomial → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match Ord.compare a b with
    | .eq => lexCompare as bs
    | order => order

/-- The degree-lexicographic monomial order. -/
def compare (a b : Monomial) : Ordering :=
  match Ord.compare a.degree b.degree with
  | .eq => lexCompare a b
  | order => order

def one (arity : Nat) : Monomial := List.replicate arity 0

def var (arity index : Nat) : Monomial :=
  (List.range arity).map fun position => if position == index then 1 else 0

def mul (a b : Monomial) : Monomial := List.zipWith (· + ·) a b

/-- `divides a b` holds when `a` divides `b` and both have the same arity. -/
def divides (a b : Monomial) : Bool :=
  a.length == b.length && (List.zipWith (fun x y => decide (x ≤ y)) a b).all id

/-- The quotient `b / a`, meaningful when `divides a b`. -/
def quotient (b a : Monomial) : Monomial := List.zipWith (· - ·) b a

def lcm (a b : Monomial) : Monomial := List.zipWith max a b

/-- An order embedding of all monomials of degree at most `bound` into `Nat`. -/
def encode (bound : Nat) (m : Monomial) : Nat :=
  let base := bound + 1
  m.foldl (fun code exponent => code * base + exponent) m.degree

end Monomial

structure Term where
  monomial : Monomial
  coefficient : Rat
  deriving Repr, DecidableEq, Inhabited, BEq, ReflBEq, LawfulBEq

/-- A sparse polynomial. Canonical form: strictly decreasing monomials in
`Monomial.compare`, nonzero coefficients and one common arity. -/
abbrev Poly := List Term

namespace Poly

def const (arity : Nat) (value : Rat) : Poly :=
  if value == 0 then [] else [⟨Monomial.one arity, value⟩]

def one (arity : Nat) : Poly := const arity 1

def var (arity index : Nat) : Poly := [⟨Monomial.var arity index, 1⟩]

/-- Merge two canonical polynomials. -/
def add : Poly → Poly → Poly
  | [], q => q
  | s :: p, [] => s :: p
  | s :: p, t :: q =>
    match Monomial.compare s.monomial t.monomial with
    | .gt => s :: add p (t :: q)
    | .lt => t :: add (s :: p) q
    | .eq =>
      let coefficient := s.coefficient + t.coefficient
      if coefficient == 0 then add p q else ⟨s.monomial, coefficient⟩ :: add p q
termination_by p q => p.length + q.length

/-- `add` onto the terms merged so far, which `merged` holds last term
first. Every recursive call is a tail call. -/
def addOnto (merged : Poly) : Poly → Poly → Poly
  | [], q => merged.reverseAux q
  | s :: p, [] => merged.reverseAux (s :: p)
  | s :: p, t :: q =>
    match Monomial.compare s.monomial t.monomial with
    | .gt => addOnto (s :: merged) p (t :: q)
    | .lt => addOnto (t :: merged) (s :: p) q
    | .eq =>
      let coefficient := s.coefficient + t.coefficient
      if coefficient == 0 then addOnto merged p q
      else addOnto (⟨s.monomial, coefficient⟩ :: merged) p q
termination_by p q => p.length + q.length

theorem addOnto_eq (merged p q : Poly) : addOnto merged p q = merged.reverse ++ add p q := by
  fun_induction add p q generalizing merged <;> simp_all +zetaDelta [addOnto]

/-- The `add` of compiled code. It makes the same comparisons as `add` and
reverses the merged terms once. -/
def addSafe (p q : Poly) : Poly := addOnto [] p q

@[csimp] theorem add_eq_addSafe : @add = @addSafe := by
  funext p q
  simp [addSafe, addOnto_eq]

def neg (p : Poly) : Poly := p.map fun t => {t with coefficient := -t.coefficient}

def sub (p q : Poly) : Poly := add p (neg q)

def scale (value : Rat) (p : Poly) : Poly :=
  if value == 0 then [] else p.map fun t => {t with coefficient := value * t.coefficient}

/-- Multiplication by one term. A monomial order is preserved by monomial
multiplication, so the result stays canonical. -/
def mulTerm (term : Term) (p : Poly) : Poly :=
  if term.coefficient == 0 then []
  else p.map fun t => ⟨t.monomial.mul term.monomial, t.coefficient * term.coefficient⟩

def mul (p q : Poly) : Poly := p.foldl (fun product t => add product (mulTerm t q)) []

def pow (arity : Nat) (p : Poly) : Nat → Poly
  | 0 => one arity
  | n + 1 => mul (pow arity p n) p

/-- `product` multiplied on the right by `p`, `n` times. Every recursive
call is a tail call. -/
def powOnto (p : Poly) : Nat → Poly → Poly
  | 0, product => product
  | n + 1, product => powOnto p n (mul product p)

theorem powOnto_pow (arity : Nat) (p : Poly) (n done : Nat) :
    powOnto p n (pow arity p done) = pow arity p (done + n) := by
  induction n generalizing done with
  | zero => rfl
  | succ n ih => rw [powOnto, ← pow, ih, Nat.succ_add_eq_add_succ]

/-- The `pow` of compiled code. It makes the same multiplications as `pow`
in the same order: `mul` is not known to be associative on polynomials that
are not canonical, so it does not square. -/
def powSafe (arity : Nat) (p : Poly) (n : Nat) : Poly := powOnto p n (one arity)

@[csimp] theorem pow_eq_powSafe : @pow = @powSafe := by
  funext arity p n
  rw [powSafe, ← pow, powOnto_pow, Nat.zero_add]

/-- Normalize an arbitrary finite list of terms. -/
def ofTerms (terms : List Term) : Poly :=
  terms.foldl (fun p t => add p (if t.coefficient == 0 then [] else [t])) []

def leading? (p : Poly) : Option Term := p.head?

/-- Strictly decreasing monomials, nonzero coefficients and the stated arity. -/
def canonical (arity : Nat) : Poly → Bool
  | [] => true
  | [t] => t.monomial.length == arity && t.coefficient != 0
  | s :: t :: rest =>
    s.monomial.length == arity && s.coefficient != 0 &&
      Monomial.compare s.monomial t.monomial == .gt && canonical arity (t :: rest)

/-- Substitute `images` (polynomials of arity `arity`) for the coordinates. -/
def evalMonomial (arity : Nat) (images : List Poly) (m : Monomial) : Poly :=
  (m.zip images).foldl (fun product (exponent, image) => mul product (pow arity image exponent))
    (one arity)

def subst (arity : Nat) (images : List Poly) (p : Poly) : Poly :=
  p.foldl (fun result t => add result (scale t.coefficient (evalMonomial arity images t.monomial)))
    []

def degreeBound (p : Poly) : Nat := (p.map fun t => t.monomial.degree).foldl max 0

end Poly

/-- One state of polynomial division by an ordered list of divisors. The
invariant `dividend = Σ quotients[i] * divisors[i] + remainder + rest` is
preserved by every step. -/
structure Division where
  quotients : List Poly
  remainder : Poly
  rest : Poly
  deriving Repr, DecidableEq, Inhabited

/-- The first divisor whose leading monomial divides `m`. -/
def findDivisor (divisors : List Poly) (m : Monomial) : Option (Nat × Poly × Term) :=
  go 0 divisors
where
  go : Nat → List Poly → Option (Nat × Poly × Term)
    | _, [] => none
    | index, g :: gs =>
      match g.leading? with
      | some lead => if lead.monomial.divides m then some (index, g, lead) else go (index + 1) gs
      | none => go (index + 1) gs

/-- One division step. It returns `none` when nothing remains to divide. -/
def Division.step (divisors : List Poly) (state : Division) : Option Division :=
  match state.rest with
  | [] => none
  | t :: rest =>
    match findDivisor divisors t.monomial with
    | some (index, g, lead) =>
      let q : Term := ⟨t.monomial.quotient lead.monomial, t.coefficient / lead.coefficient⟩
      some { state with
        quotients := state.quotients.modify index (fun quotient => Poly.add quotient [q])
        rest := Poly.sub (t :: rest) (Poly.mulTerm q g) }
    | none => some { state with remainder := Poly.add state.remainder [t], rest }

def Division.start (divisors : List Poly) (p : Poly) : Division :=
  ⟨divisors.map fun _ => [], [], p⟩

/-- Each step strictly lowers the leading monomial of `rest`. Every monomial
that appears is degLex-below the dividend's leading monomial, so encoding that
monomial bounds the number of steps. Exhausted fuel keeps the exact invariant,
and the result then only fails to be fully reduced. -/
def divisionFuel (p : Poly) : Nat :=
  match p.leading? with
  | some lead => lead.monomial.encode lead.monomial.degree + 1
  | none => 0

def divideWith : Nat → List Poly → Division → Division
  | 0, _, state => {state with remainder := Poly.add state.remainder state.rest, rest := []}
  | fuel + 1, divisors, state =>
    match Division.step divisors state with
    | some next => divideWith fuel divisors next
    | none => state

def divide (divisors : List Poly) (p : Poly) : Division :=
  divideWith (divisionFuel p) divisors (Division.start divisors p)

def normalForm (basis : List Poly) (p : Poly) : Poly := (divide basis p).remainder

/-- A ring map between presented affine objects, in pullback direction. For
`f : X → Y`, `images` are the normal forms in `X`'s ring of `Y`'s coordinates.
`arity` and `basis` describe `X`'s ring, so evaluation needs no environment. -/
structure Map where
  arity : Nat
  basis : List Poly
  images : List Poly
  deriving Repr, DecidableEq, Inhabited, BEq, ReflBEq, LawfulBEq

namespace Map

def identity (arity : Nat) (basis : List Poly) : Map :=
  ⟨arity, basis, (List.range arity).map fun index => normalForm basis (Poly.var arity index)⟩

/-- `compose after before` is the map `X → Z` from `before : X → Y` and
`after : Y → Z`. Its pullback substitutes `before` into `after`'s images. -/
def compose (after before : Map) : Map :=
  ⟨before.arity, before.basis,
    after.images.map fun image => normalForm before.basis (Poly.subst before.arity before.images image)⟩

/-- The pairing into a fiber product whose coordinates are the left factor's
followed by the right factor's. Both maps must have the same source. -/
def pair (left right : Map) : Map := ⟨left.arity, left.basis, left.images ++ right.images⟩

/-- Equality of maps with one checked source and target. -/
def same (left right : Map) : Bool := left.images == right.images

/-- The coefficient of `m` in the image of target coordinate `index`, as a
reduced numerator and positive denominator. -/
def coefficient (map : Map) (index : Nat) (m : Monomial) : Int × Int :=
  let value := ((map.images.getD index []).find? (·.monomial == m)).map (·.coefficient) |>.getD 0
  (value.num, value.den)

/-- A rational point of a free object over a coordinate-free base, from
integer coordinates. -/
def intPoint (values : List Int) : Map := ⟨0, [], values.map (fun value : Int => Poly.const 0 (Rat.ofInt value))⟩

end Map

end VastitasKernel.AlgebraRuntime
