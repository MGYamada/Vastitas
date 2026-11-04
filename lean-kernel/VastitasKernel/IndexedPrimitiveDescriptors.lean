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
call and the literals a generated module shares. The wire decoder is still a
per-constructor table; the next step of #622 moves it here, so a new
constructor today still needs a case in it.

The validity contract is a `Bool` that the checker runs together with the
`Prop` that the proofs use; the descriptor carries the proof that they agree,
so the two cannot drift apart. The association is a `Shape`, one datum for the
contract, the inference and the diagnostics. The evaluators take the operand
values the shape admits and return `none` on any other list: the logical one
builds the values of `IndexedPrimitiveValues`, the erased one the runtime
structures of generated programs. The oracle states their obligations once,
for any descriptor (`VastitasOracle.IndexedPrimitiveSoundness`). The lowering
writes the generated Lean text of a call from its rendered operands, in the
vocabulary of `Lowering` (runtime names and exact literals of the checked
data, never source spellings), and rejects any other operand list; it reads
the literals the module shares through a `RenderContext`. A descriptor grants
no authority: the all-body audits and the public acceptance path are
unchanged. -/
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
/-- The lowering of a call whose rendered operands do not fit its entry. -/
def arityMismatch : Except String String := .error "closed primitive arity mismatch"

end Lowering

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
  semantics, or `none` outside the shape. -/
  eval : Environment → List Value → Option Value
  /-- The erased evaluator: the same call on the runtime structures that
  generated programs link. -/
  evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue
  /-- The lowering: the generated Lean text of a call from the literals the
  module shares and the rendered operands, or an error on any other operand
  list. -/
  render : RenderContext → List String → Except String String
  /-- The literals a generated module declares once for this entry. -/
  literals : List SharedLiteral

/-- A descriptor whose contract is one executable check; its calls share no
literal unless given. -/
def PrimitiveDescriptor.ofBool (shape : Shape) (check : Environment → Bool)
    (eval : Environment → List Value → Option Value)
    (evalRuntime : List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue)
    (render : RenderContext → List String → Except String String)
    (literals : List SharedLiteral := []) : PrimitiveDescriptor where
  shape := shape
  validProp env := check env = true
  validBool := check
  valid_iff _ := Iff.rfl
  eval := eval
  evalRuntime := evalRuntime
  render := render
  literals := literals

/-- The descriptor of an evidence binding: its contract is one executable
check, no call is well formed, none evaluates and none is lowered. -/
def PrimitiveDescriptor.evidence (check : Environment → Bool) : PrimitiveDescriptor :=
  .ofBool .uncallable check (fun _ _ => none) (fun _ => none) (fun _ _ => Lowering.arityMismatch)

/-- The distinct literals the entries share, in declaration order. -/
def PrimitiveDescriptor.sharedLiterals (entries : List PrimitiveDescriptor) : List SharedLiteral :=
  entries.foldl (fun found entry => entry.literals.foldl
    (fun found literal => if found.contains literal then found else found ++ [literal]) found) []

end VastitasKernel.Indexed
