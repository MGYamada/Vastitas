import VastitasKernel.IndexedCore
import VastitasKernel.FunctionId
import VastitasKernel.IndexedFunctionState

set_option autoImplicit false

/-! The first, exact fragment of MidIR v1. It has no effectful instruction.
Each block receives an ordering token; exactly the taken edge, or the return,
forwards it. Values and token references occupy separate namespaces. -/
namespace VastitasKernel.MidIR

open Indexed

inductive Phase where
  | optimization | execution
  deriving DecidableEq

inductive Ty where
  | unit
  | bool
  | nat
  | int
  | pair (element : PairElem)
  | finite (carrier : FiniteSort)
  deriving BEq, DecidableEq, Repr

def Ty.valid (env : Environment) : Ty → Bool
  | .unit | .bool | .nat | .int | .pair _ => true
  | .finite c => (FiniteSort.tags env c).isSome

def Ty.ofCore : Core.DataType → Option Ty
  | .pure .unit => some .unit
  | .pure .bool => some .bool
  | .pure .nat => some .nat
  | .pure .int => some .int
  | .pure (.pair e) => some (.pair e)
  | .finite c => some (.finite c)
  | _ => none

/-- Only these same-kind arithmetic operations have an exact runtime ABI.
Mixed division has two distinct ordered signatures. -/
inductive Arithmetic where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def Arithmetic.ofCore : BinaryOp → Option Arithmetic
  | .add => some .add | .sub => some .sub | .mul => some .mul | .div => some .div
  | _ => none

def Arithmetic.name : Arithmetic → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"

inductive ExactOp where
  | nat (op : Arithmetic)
  | int (op : Arithmetic)
  | natIntDiv | intNatDiv | neg | natToInt
  | pair (element : PairElem)
  | project (element : PairElem) (first : Bool)
  deriving DecidableEq, Repr

def ExactOp.binary (op : BinaryOp) (left right : Core.DataType) : Option ExactOp := do
  let arith ← Arithmetic.ofCore op
  match left, right with
  | .pure .nat, .pure .nat => return .nat arith
  | .pure .int, .pure .int => return .int arith
  | .pure .nat, .pure .int => guard (arith = .div); return .natIntDiv
  | .pure .int, .pure .nat => guard (arith = .div); return .intNatDiv
  | _, _ => none

def pairScalar : PairElem → Ty | .nat => .nat | .int => .int

def ExactOp.operands : ExactOp → List Ty
  | .nat _ => [.nat, .nat] | .int _ => [.int, .int]
  | .natIntDiv => [.nat, .int] | .intNatDiv => [.int, .nat]
  | .neg => [.int] | .natToInt => [.nat]
  | .pair e => [pairScalar e, pairScalar e]
  | .project e _ => [.pair e]

def ExactOp.result : ExactOp → Ty
  | .nat _ => .nat
  | .int _ | .natIntDiv | .intNatDiv | .neg | .natToInt => .int
  | .pair e => .pair e
  | .project e _ => pairScalar e

def ExactOp.name : ExactOp → String
  | .nat op => "nat_" ++ op.name
  | .int op => "int_" ++ op.name
  | .natIntDiv => "nat_int_div" | .intNatDiv => "int_nat_div"
  | .neg => "int_neg" | .natToInt => "nat_to_int"
  | .pair .nat => "nat_pair" | .pair .int => "int_pair"
  | .project .nat true => "nat_pair_first" | .project .nat false => "nat_pair_second"
  | .project .int true => "int_pair_first" | .project .int false => "int_pair_second"

inductive Comparison where
  | eq | ne
  deriving DecidableEq, Repr

/-- A total table on one nominal carrier with a nominal result. The table
identity is retained even if another declaration has identical rows. -/
structure UnaryLookup where
  table : DeclId
  input : DeclId
  output : DeclId
  deriving BEq, DecidableEq, Repr

def UnaryLookup.site (s : UnaryLookup) : FiniteLookup :=
  ⟨s.table, none, [.carrier s.input], .carrier s.output⟩

/-- A first-order call carries its selected symbol and full nominal signature.
The enclosing module supplies the common declaration environment and revision. -/
structure CallTarget where
  family : Namespace.FunctionId
  symbol : Nat
  key : FunctionSource.Compiler.Key
  params : List Ty
  result : Ty
  deriving DecidableEq

def CallTarget.ofCore (f : Core.Function) (key : FunctionSource.Compiler.Key) : Option CallTarget := do
  let params ← f.parameters.mapM fun p => do
    guard p.result.reference.isNone
    Ty.ofCore p.result.type
  return ⟨⟨f.definition⟩, f.id, key, params, ← Ty.ofCore f.returnType⟩

/-- A negative source literal is elaborated as a negation of an Int literal.
Both spellings preserve an unbounded Int. No run-time operation is folded. -/
inductive IntLiteral where
  | integer (n : Int)
  | negated (n : Int)

def IntLiteral.term : IntLiteral → Core.Term
  | .integer n => .integer n
  | .negated n => .unary .neg (.integer n) ⟨.pure .int, none⟩

def IntLiteral.value : IntLiteral → Int
  | .integer n => n
  | .negated n => -n

def IntLiteral.inspect : (term : Core.Term) → Option { l : IntLiteral // term = l.term }
  | .integer n => some ⟨.integer n, rfl⟩
  | .unary .neg (.integer n) r =>
    if h : r = ⟨.pure .int, none⟩ then some ⟨.negated n, by subst r; rfl⟩ else none
  | _ => none

/-- The opcode constructor fixes its legal phases. These operations are
pure. Exact arithmetic has a boxed runtime ABI at the LLVM boundary. Equality compares values of one nominal type. -/
inductive Opcode : Phase → Type where
  | unit {p} : Opcode p
  | boolean {p} (value : Bool) : Opcode p
  | natural {p} (value : Nat) : Opcode p
  | exactOp {p} (op : ExactOp) : Opcode p
  | integer {p} (value : Int) : Opcode p
  | finiteTag (carrier : FiniteSort) (tag : String) : Opcode .optimization
  | finiteOrdinal (carrier : FiniteSort) (ordinal : Nat) : Opcode .execution
  | lookupTag (s : FiniteLookup) : Opcode .optimization
  | lookupOrdinal (s : FiniteLookup) : Opcode .execution
  | boolAnd {p} : Opcode p
  | boolOr {p} : Opcode p
  | boolNot {p} : Opcode p
  | compare {p} (kind : Comparison) (type : Ty) : Opcode p
  | call {p} (target : CallTarget) : Opcode p
  deriving DecidableEq

namespace Opcode
variable {p : Phase}

def tag : Opcode p → String
  | .unit => "unit.const.v1"
  | .boolean _ => "bool.const.v1"
  | .natural _ => "nat.const.v1"
  | .exactOp op => op.name ++ ".v1"
  | .integer _ => "int.const.v1"
  | .finiteTag .. => "finite.tag.v1"
  | .finiteOrdinal .. => "finite.ordinal.v1"
  | .lookupTag _ => "finite.lookup.tag.v1"
  | .lookupOrdinal _ => "finite.lookup.ordinal.v1"
  | .boolAnd => "bool.and.v1"
  | .boolOr => "bool.or.v1"
  | .boolNot => "bool.not.v1"
  | .compare .eq _ => "exact.eq.v1"
  | .compare .ne _ => "exact.ne.v1"
  | .call _ => "static.call.v1"

def operands : Opcode p → List Ty
  | .lookupTag s | .lookupOrdinal s => s.inputs.map Ty.finite
  | .boolAnd | .boolOr => [.bool, .bool]
  | .boolNot => [.bool]
  | .compare _ t => [t, t]
  | .exactOp op => op.operands
  | .call t => t.params
  | _ => []

def result : Opcode p → Ty
  | .finiteTag c _ | .finiteOrdinal c _ => .finite c
  | .lookupTag s | .lookupOrdinal s => .finite s.output
  | .boolean _ | .boolAnd | .boolOr | .boolNot | .compare .. => .bool
  | .unit => .unit
  | .natural _ => .nat
  | .exactOp op => op.result
  | .integer _ => .int
  | .call t => t.result

def valid (env : Environment) : Opcode p → Bool
  | .unit | .boolean _ | .natural _ | .exactOp _ | .integer _ | .boolAnd | .boolOr | .boolNot => true
  | .finiteTag c t => (FiniteSort.tags env c).any (·.contains t)
  | .finiteOrdinal c n => (FiniteSort.tags env c).any (n < ·.length)
  | .lookupTag s | .lookupOrdinal s => (s.plan? env).isSome
  | .compare _ .nat | .compare _ .int | .compare _ (.pair _) => false
  | .compare _ t => t.valid env
  | .call t => t.params.all (·.valid env) && t.result.valid env

/-- Resolve the ordinal from the exact carrier declaration, in declared order. -/
def execute (env : Environment) : Opcode .optimization → Option (Opcode .execution)
  | .unit => some .unit
  | .boolean b => some (.boolean b)
  | .natural n => some (.natural n)
  | .exactOp op => some (.exactOp op)
  | .integer n => some (.integer n)
  | .boolAnd => some .boolAnd
  | .boolOr => some .boolOr
  | .boolNot => some .boolNot
  | .compare k t => some (.compare k t)
  | .lookupTag s => some (.lookupOrdinal s)
  | .call t => some (.call t)
  | .finiteTag c tag => do
    let tags ← FiniteSort.tags env c
    let n := tags.idxOf tag
    if tags[n]? = some tag then return .finiteOrdinal c n else none

end Opcode

/-- A slot is either a block argument (first) or a following instruction
result. Definition identity is its position, so no two definitions can alias. -/
structure Ref where
  block : Nat
  slot : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Hashable

structure Op (p : Phase) where
  code : Opcode p
  args : List Ref
  deriving DecidableEq

/-- The unique token at the start of a block. No instruction in the pure
fragment consumes or produces tokens. -/
structure Token where
  block : Nat
  deriving BEq, DecidableEq, Repr

structure Edge where
  dest : Nat
  token : Token
  args : List Ref
  deriving Repr, DecidableEq

inductive Terminator where
  | ret (token : Token) (value : Ref)
  | jump (edge : Edge)
  | branch (condition : Ref) (yes no : Edge)
  deriving Repr, DecidableEq

structure Block (p : Phase) where
  params : Array Ty
  ops : Array (Op p)
  term : Terminator
  deriving DecidableEq

def UnaryLookup.code (s : UnaryLookup) : (p : Phase) → Opcode p
  | .optimization => .lookupTag s.site
  | .execution => .lookupOrdinal s.site

def UnaryLookup.block (s : UnaryLookup) (p : Phase) : Block p :=
  ⟨#[.finite (.carrier s.input)], #[⟨s.code p, [⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩

def IntLiteral.block (lit : IntLiteral) (p : Phase) : Block p :=
  ⟨#[], #[⟨.integer lit.value, []⟩], .ret ⟨0⟩ ⟨0,0⟩⟩

structure Function (p : Phase) where
  id : Namespace.FunctionId
  coreId : Nat
  specialization : FunctionSource.Compiler.Key
  params : Array Ty
  result : Ty
  blocks : Array (Block p)

def Function.target {p : Phase} (f : Function p) : CallTarget :=
  ⟨f.id, f.coreId, f.specialization, f.params.toList, f.result⟩

structure Module (p : Phase) where
  /-- The complete function revision for this exact input, shared across
  functions. No hash or printed function name substitutes for this evidence. -/
  revision : Lean.Json
  env : Environment
  functions : Array (Function p)
  entry : Option Nat

end VastitasKernel.MidIR
