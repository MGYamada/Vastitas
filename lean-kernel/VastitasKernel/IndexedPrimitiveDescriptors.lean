import VastitasKernel.IndexedPrimitiveShapes
import VastitasKernel.IndexedPrimitiveValues

set_option autoImplicit false

/-! One checked descriptor per indexed primitive (#622).

A `PrimitiveDescriptor` holds what the kernel derives for one bound primitive.
The registry (`IndexedPrimitiveRegistry`) builds one descriptor per
`PrimitiveBinding` constructor from the binding's own data; `IndexedPrimitives`
derives the binding validity contract, the operand association, result
inference, the operand count and whether a call allocates from it,
`IndexedCore` the argument hints, `IndexedSourceDiagnostics` the role table,
`IndexedSemantics` the two evaluators and `IndexedCodegen` the lowering of a
call and the literals a generated module shares. A binding's wire form comes
from its `PrimitiveFamily` in `IndexedPrimitiveFamilies`, which the decoder,
the resolver and the generated Rust table read; a binding without a family is
built by `resolveBody` or a stage pass.

The validity contract is a `Bool` that the checker runs together with the
`Prop` that the proofs use; the descriptor carries the proof that they agree,
so the two cannot drift apart. The association is a `Shape`, one datum for the
contract, the inference and the diagnostics. The evaluators match the operand
pattern of the shape and return `none` on any other pattern; a variadic entry
accepts any number of integer operands, and the checked operand count, not the
evaluator, fixes it. The logical evaluator builds the values of
`IndexedPrimitiveValues`, the erased one the runtime structures of generated
programs. The oracle states their obligations once,
for any descriptor (`VastitasOracle.IndexedPrimitiveSoundness`). The lowering
writes the generated Lean text of a call from its rendered operands, in the
vocabulary of `Lowering` (runtime names and exact literals of the checked
data, never source spellings), and rejects any other operand list; a variadic
entry renders any number of operands, and the checked operand count, not the
lowering, fixes it. The lowering reads the literals the module shares through
a `RenderContext`. A descriptor grants no authority: the all-body audits and
the public acceptance path are unchanged. -/
namespace VastitasKernel.Indexed
open VastitasKernel.Indexed.Core.Semantics (Value PrimitiveRuntimeValue)

/-- A literal that a generated module declares once and that the lowering of a
call names instead of repeating: the basis of a relative constant, declared as
`basis_k` and named by every map over it. -/
abbrev SharedLiteral := List AlgebraRuntime.Poly

/-- What the lowering of a call reads from the whole module: the distinct
literals its entries share, in declaration order, the `k`-th declared as
`basis_k`. -/
structure RenderContext where
  literals : List SharedLiteral

/-! ## The text of generated programs

The runtime names and the exact literals of the checked data that the registry
entries and `IndexedCodegen` write. No source spelling is used. -/
namespace Lowering

def runtime (name : String) : String := "VastitasKernel.IndexedRuntime." ++ name
def algebra (name : String) : String := "VastitasKernel.AlgebraRuntime." ++ name
def smooth (name : String) : String := "VastitasKernel.SmoothRuntime." ++ name

/-- `(name arg₁ … argₙ)`. -/
def application (name : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (name :: args) ++ ")"

/-- Exact rational literals of the checked map data; no source spelling is used. -/
def renderRat (value : Rat) : String := s!"(mkRat ({value.num} : Int) {value.den})"
def renderTerm (term : AlgebraRuntime.Term) : String :=
  s!"({algebra "Term.mk"} {term.monomial} {renderRat term.coefficient})"
def renderPoly (p : AlgebraRuntime.Poly) : String :=
  s!"([{String.intercalate ", " (p.map renderTerm)}] : {algebra "Poly"})"
def renderPolys (ps : List AlgebraRuntime.Poly) : String :=
  s!"([{String.intercalate ", " (ps.map renderPoly)}] : List {algebra "Poly"})"
/-- A checked metric matrix, row by row, with exact rational entries. -/
def renderMatrix (matrix : SmoothRuntime.Matrix) : String :=
  let rows := matrix.map fun row => s!"[{String.intercalate ", " (row.map renderRat)}]"
  s!"([{String.intercalate ", " rows}] : {smooth "Matrix"})"
/-- The name of the `index`-th literal a module shares. -/
def basisName (index : Nat) : String := s!"basis_{index}"
/-- A checked map: its basis by name when the module shares it, else in place. -/
def renderMap (ctx : RenderContext) (map : AlgebraRuntime.Map) : String :=
  let basis := match ctx.literals.idxOf? map.basis with
    | some index => basisName index
    | none => renderPolys map.basis
  s!"({algebra "Map.mk"} {map.arity} {basis} {renderPolys map.images})"
/-- A Jacobian table, column by column, with exact rational coefficients. -/
def renderJacobian (table : List (List AlgebraRuntime.Poly)) : String :=
  s!"([{String.intercalate ", " (table.map renderPolys)}] : List (List {algebra "Poly"}))"
/-- The lowering of a call whose rendered operands do not fit its entry. -/
def arityMismatch : Except String String := .error "closed primitive arity mismatch"

end Lowering

/-- The reverse passes that the kernel compiles into Core (#623). -/
inductive PassKind where
  /-- The pullback of a seed along a map at a point, with saved or recomputed
  forward values. Operands: map, point, seed. -/
  | pullback (mode : SmoothRuntime.PullbackMode)
  /-- The differential of a function to a line at a point: the pullback of the
  coordinate covector at the image. Operands: function, point. -/
  | differential
  /-- The reverse pass of a tape on a seed. Operands: tape, seed. -/
  | backward
  deriving Repr, Inhabited, DecidableEq

/-- The derivative rule of a primitive: what a call contributes when the
kernel compiles a reverse pass into Core (#623). The compilation reads these
rules only; it has no case per binding. -/
inductive ReverseRule where
  /-- The compilation does not open the call. A call of type `Smooth<X, Y>`
  with this rule is one opaque step of any reverse pass that reads it. The
  rule makes no claim about what the call computes: it may run a reverse pass
  itself, as the kernel's own `cotangentJacobian` step does, and the oracle's
  `ReverseSound` promises nothing for it. -/
  | none
  /-- The call is a declared map, with its exact data: one step whose backward
  evaluates the Jacobian table of `map`. -/
  | morphism (map : AlgebraRuntime.Map)
  /-- The call composes the maps at operand positions `after` and `before`:
  the forward runs `before` first, the backward runs `after` first. -/
  | chain (after before : Nat)
  /-- The call saves the forward values of a map at a point as a tape.
  Operands: map, point. -/
  | tape
  /-- The call is a reverse pass of kind `kind`, which the compilation
  replaces by generated forward and backward Core. -/
  | pass (kind : PassKind)
  deriving Repr, Inhabited, DecidableEq

structure PrimitiveDescriptor where
  /-- The operands, their agreements and the result type. -/
  shape : Shape
  /-- The binding contract as the proofs state it. -/
  validProp : Environment → Prop
  /-- The binding contract as the checker decides it. -/
  validBool : Environment → Bool
  /-- The two contracts agree; the registry entry proves it once. -/
  valid_iff : ∀ env, validBool env = true ↔ validProp env
  /-- The logical evaluator: the value of a call on operand values of the Core
  semantics, or `none` when they do not match the shape's operand pattern. -/
  eval : Environment → List Value → Option Value
  /-- The erased evaluator: the same call on the runtime structures that
  generated programs link. -/
  evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue
  /-- The lowering: the generated Lean text of a call from the literals the
  module shares and the rendered operands, or an error on any other operand
  list. A variadic entry renders any number of operands; the checked operand
  count fixes it. -/
  render : RenderContext → List String → Except String String
  /-- The literals a generated module declares once for this entry; none
  unless the entry names them. -/
  literals : List SharedLiteral := []
  /-- The derivative rule: what a call contributes to compiled reverse Core.
  Every entry states it; there is no default. -/
  reverse : ReverseRule

/-- A descriptor whose contract is one executable check; its calls share no
literal unless given. -/
def PrimitiveDescriptor.ofBool (shape : Shape) (check : Environment → Bool)
    (eval : Environment → List Value → Option Value)
    (evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue)
    (render : RenderContext → List String → Except String String)
    (reverse : ReverseRule)
    (literals : List SharedLiteral := []) : PrimitiveDescriptor where
  shape := shape
  validProp env := check env = true
  validBool := check
  valid_iff _ := Iff.rfl
  eval := eval
  evalRuntime := evalRuntime
  render := render
  literals := literals
  reverse := reverse

/-- The descriptor of an evidence binding: its contract is one executable
check, no call is well formed, none evaluates and none is lowered. -/
def PrimitiveDescriptor.evidence (check : Environment → Bool) : PrimitiveDescriptor :=
  .ofBool .uncallable check (fun _ _ => none) (fun _ => none) (fun _ _ => Lowering.arityMismatch) .none

/-- The distinct literals the entries share, in declaration order. -/
def PrimitiveDescriptor.sharedLiterals (entries : List PrimitiveDescriptor) : List SharedLiteral :=
  entries.foldl (fun found entry => entry.literals.foldl
    (fun found literal => if found.contains literal then found else found ++ [literal]) found) []

end VastitasKernel.Indexed
