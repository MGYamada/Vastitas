import VastitasKernel.ExactOperators
import VastitasKernel.MidIR.IR
import VastitasKernel.OperatorProfile

set_option autoImplicit false

/-! Constant folding is confined to closed, pure Nat/Int expressions.
The compiler keeps a structural witness over the very Core body that it
folds. No LLVM integer arithmetic encodes Vastitas arithmetic. -/
namespace VastitasKernel.MidIR.ExactFold
open Indexed

inductive Scalar where
  | nat (n : Nat)
  | int (n : Int)
  deriving DecidableEq

def Scalar.type : Scalar → Core.DataType
  | .nat _ => .pure .nat
  | .int _ => .pure .int

/-- Literal operands can be recognized inside a function with arbitrary
parameters. Their values are independent of the caller's environment. -/
inductive Literal : Core.Term → Scalar → Prop where
  | nat (n) : Literal (.natural n) (.nat n)
  | int (l : IntLiteral) : Literal l.term (.int l.value)
  | ascribe {t v} : Literal t v → Literal (.ascribe v.type t) v

def literal : (t : Core.Term) → Option {v // Literal t v}
  | .natural n => some ⟨.nat n, .nat n⟩
  | .ascribe ty t => do
    let ⟨v, h⟩ ← literal t
    if eq : ty = v.type then return ⟨v, eq ▸ Literal.ascribe h⟩ else none
  | t => do
    let ⟨l, h⟩ ← IntLiteral.inspect t
    return ⟨.int l.value, h ▸ Literal.int l⟩

def Scalar.compare : BinaryOp → Scalar → Scalar → Option Bool
  | .eq, .nat x, .nat y => some (x == y)
  | .ne, .nat x, .nat y => some (x != y)
  | .eq, .int x, .int y => some (x == y)
  | .ne, .int x, .int y => some (x != y)
  | _, _, _ => none

def literalComparison (op : BinaryOp) (left right : Core.Term) : Option Bool := do
  guard (op == .eq || op == .ne)
  let a ← literal left
  let b ← literal right
  Scalar.compare op a.val b.val

private def Scalar.bits : Scalar → Nat
  | .nat n => n.log2 + 1
  | .int n => n.natAbs.log2 + 1

def Scalar.binary : BinaryOp → Scalar → Scalar → Option Scalar
  | .add, .nat a, .nat b => some (.nat (a+b))
  | .sub, .nat a, .nat b => some (.nat (a-b))
  | .mul, .nat a, .nat b => some (.nat (a*b))
  | .div, .nat a, .nat b => some (.nat (a/b))
  | .add, .int a, .int b => some (.int (a+b))
  | .sub, .int a, .int b => some (.int (a-b))
  | .mul, .int a, .int b => some (.int (a*b))
  | .div, .int a, .int b => some (.int (a/b))
  | .div, .nat a, .int b => some (.int (Int.ofNat a/b))
  | .div, .int a, .nat b => some (.int (a/Int.ofNat b))
  | _, _, _ => none

abbrev Bindings := List (Nat × Scalar)

/-- A successful untrusted fold must exhibit a derivation for each subterm,
including the initializer of any unused binding. -/
inductive Folded : Bindings → Core.Term → Scalar → Prop where
  | nat {ctx n} : Folded ctx (.natural n) (.nat n)
  | int {ctx n} : Folded ctx (.integer n) (.int n)
  | var {ctx n r v} : ctx.lookup n = some v → Folded ctx (.variable n r) v
  | neg {ctx t r n} : Folded ctx t (.int n) → Folded ctx (.unary .neg t r) (.int (-n))
  | binary {ctx op a b r x y v} : Folded ctx a x → Folded ctx b y → Scalar.binary op x y = some v →
      Folded ctx (.binary op a b r) v
  | convert {ctx t n} : Folded ctx t (.nat n) → Folded ctx (.natToInt t) (.int (Int.ofNat n))
  | ascribe {ctx t ty v} : Folded ctx t v → Folded ctx (.ascribe ty t) v
  | scope {ctx t v} : Folded ctx t v → Folded ctx (.scope t) v
  | bind {ctx n a b x v} : Folded ctx a x → Folded ((n,x)::ctx) b v → Folded ctx (.letE n a b) v

/-- Bound the working bits by the encoded literals and the expression size.
Local variables can otherwise turn repeated squaring into exponential space.
This constrains a compile-time optimization, never the meaning of Int/Nat. -/
private def bitBudget : Core.Term → Nat
  | .natural n => (.nat n : Scalar).bits + 1
  | .integer n => (.int n : Scalar).bits + 1
  | .binary _ a b _ | .letE _ a b => 1 + bitBudget a + bitBudget b
  | .natToInt t | .scope t | .ascribe _ t | .unary _ t _ => 1 + bitBudget t
  | _ => 1

private def visit (budget : Nat) (ctx : Bindings) : (term : Core.Term) → Option {v // Folded ctx term v}
  | .natural n => some ⟨.nat n, .nat⟩
  | .integer n => some ⟨.int n, .int⟩
  | .variable n r => do
    match h : ctx.lookup n with
    | some v =>
      guard (r == ⟨v.type, none⟩)
      return ⟨v, .var h⟩
    | none => none
  | .unary .neg t r => do
    let ⟨.int n, h⟩ ← visit budget ctx t | none
    guard (r == ⟨.pure .int, none⟩)
    return ⟨.int (-n), .neg h⟩
  | .binary op a b r => do
    let ⟨x, hx⟩ ← visit budget ctx a
    let ⟨y, hy⟩ ← visit budget ctx b
    match h : Scalar.binary op x y with
    | some v =>
      guard (v.bits ≤ budget && r == ⟨v.type, none⟩)
      return ⟨v, .binary hx hy h⟩
    | none => none
  | .natToInt t => do
    let ⟨.nat n, h⟩ ← visit budget ctx t | none
    return ⟨.int (Int.ofNat n), .convert h⟩
  | .scope t => do
    let ⟨v, h⟩ ← visit budget ctx t
    return ⟨v, .scope h⟩
  | .ascribe ty t => do
    let ⟨v, h⟩ ← visit budget ctx t
    guard (ty == v.type)
    return ⟨v, .ascribe h⟩
  | .letE n a b => do
    let ⟨x, hx⟩ ← visit budget ctx a
    let ⟨v, hv⟩ ← visit budget ((n,x)::ctx) b
    return ⟨v, .bind hx hv⟩
  | _ => none

def integer (t : Core.Term) : Option {n : Int // Folded [] t (.int n)} := do
  let ⟨.int n, h⟩ ← visit (bitBudget t) [] t | none
  return ⟨n,h⟩

/-- The same family-local methods used in the wire revision. -/
abbrev candidates := ExactOperators.candidates

structure Method (selection : ExactOperators.Selection) where
  ordinal : Nat
  result : Core.DataType
  sole : candidates selection = [(ordinal, result)]

def resolve (s : ExactOperators.Selection) : Option (Method s) :=
  match h : candidates s with
  | [(i, ty)] => some ⟨i,ty,h⟩
  | _ => none

end VastitasKernel.MidIR.ExactFold
