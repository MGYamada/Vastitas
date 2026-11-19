import VastitasKernel.MidIR.IR
import VastitasKernel.StorageCodegen

set_option autoImplicit false

/-! Ordered effects of a static storage schedule. The optimization form retains
logical loans and owners. Only the existing storage checker can resolve them
to the allocation IDs and physical views of the execution form. -/
namespace VastitasKernel.MidIR.StorageEffects
open Storage

inductive Callee where
  | allocate | drop | fill | store | expect | copy | gemm
  deriving DecidableEq, BEq, Repr

def Callee.name : Callee → String
  | .allocate => "allocate" | .drop => "drop" | .fill => "fill"
  | .store => "store" | .expect => "expect" | .copy => "copy" | .gemm => "gemm"

def Callee.all : List Callee := [.allocate, .drop, .fill, .store, .expect, .copy, .gemm]

/-- All integer arguments use i64 at the C boundary. Layouts are flattened to
five words so the platform ABI for C struct values does not enter the IR. -/
inductive Operand where
  | allocation | extent | flag | scalar | bits | coefficientKind

private def viewSignature : List Operand := [.extent, .extent, .extent, .extent, .flag]

private def matrixSignature := [.allocation] ++ viewSignature
private def inputMatrixSignature := matrixSignature ++ [.flag]
private def coefficientSignature : List Operand :=
  [.coefficientKind, .scalar, .bits, .bits, .allocation, .extent]

def Callee.signature : Callee → List Operand
  | .allocate => [.allocation, .scalar, .extent]
  | .drop => [.allocation]
  | .fill => [.allocation] ++ viewSignature ++ [.scalar, .bits, .bits]
  | .store | .expect => [.allocation] ++ viewSignature ++ [.extent, .extent, .scalar, .bits, .bits]
  | .copy => matrixSignature ++ matrixSignature
  | .gemm => [.scalar] ++ inputMatrixSignature ++ inputMatrixSignature ++ matrixSignature ++
      [.flag] ++ coefficientSignature ++ coefficientSignature

def Callee.arity (f : Callee) := f.signature.length

def Operand.accepts : Operand → Nat → Bool
  | .allocation, n => n < 2^32
  | .extent, n => n ≤ Storage.byteLimit
  | .flag, n => n < 2
  | .coefficientKind, n => n < 3
  | .scalar, n => n < 4
  | .bits, n => n < 2^64

structure Call where
  target : Callee
  arguments : List Nat
  deriving DecidableEq, BEq, Repr

private def literalBits (scalar real imaginary : Nat) : Bool :=
  (scalar != 0 && scalar != 2 || imaginary == 0) &&
  (scalar < 2 || real < 2^32 && imaginary < 2^32)

private def validCoefficient (element : Nat) : List Nat → Bool
  | [0, 0, 0, 0, 0, 0] => true
  | [1, scalar, real, imaginary, 0, 0] => element == scalar && literalBits scalar real imaginary
  | [2, 0, 0, 0, _, _] => true
  | _ => false

private def validGemm (arguments : List Nat) : Bool := Id.run do
  let scalar :: operands := arguments | return false
  -- Only the two inputs may transpose. An overwrite never reads beta.
  let 0 :: mode :: coefficients := operands.drop (2 * inputMatrixSignature.length + matrixSignature.length - 1)
    | return false
  let beta := coefficients.drop coefficientSignature.length
  return validCoefficient scalar (coefficients.take coefficientSignature.length) &&
    validCoefficient scalar beta && (mode != 0 || beta.head? == some 0)

def Call.valid (c : Call) : Bool :=
  c.arguments.length == c.target.arity &&
    (c.target.signature.zip c.arguments).all (fun (ty, n) => ty.accepts n) &&
    (match c.target with
     | .fill | .store | .expect =>
       match c.arguments.reverse with
       | imaginary :: real :: scalar :: _ => literalBits scalar real imaginary
       | _ => false
     | .gemm => validGemm c.arguments
     | _ => true)

private def layout (v : Layout) : List Nat :=
  [v.offset, v.rows, v.columns, v.leading, v.transposed.toNat]

private def literal (value : Literal) : List Nat :=
  NativeText.scalar value.scalar :: (match value with
    | .f32 x => [x.toNat, 0] | .f64 x => [x.toNat, 0]
    | .complexF32 r i => [r.toNat, i.toNat] | .complexF64 r i => [r.toNat, i.toNat])

private def coefficient : ResolvedCoefficient → List Nat
  | .default => [0, 0, 0, 0, 0, 0]
  | .literal x => [1] ++ literal x ++ [0, 0]
  | .view allocation offset => [2, 0, 0, 0, allocation, offset]

private def coefficientFits (live : Std.HashMap Nat Scalar) (s : Scalar) : ResolvedCoefficient → Bool
  | .default => true
  | .literal value => value.scalar == s
  | .view allocation _ => live[allocation]? == some s

def resolveInstruction (live : Std.HashMap Nat Scalar) : Native.Instruction → Option Call
  | .allocate a s n => some ⟨.allocate, [a, NativeText.scalar s, n]⟩
  | .drop a => some ⟨.drop, [a]⟩
  | .fill a v x => some ⟨.fill, [a] ++ layout v ++ literal x⟩
  | .store a v r c x => some ⟨.store, [a] ++ layout v ++ [r,c] ++ literal x⟩
  | .expect a v r c x => some ⟨.expect, [a] ++ layout v ++ [r,c] ++ literal x⟩
  | .copy a v b w => some ⟨.copy, [a] ++ layout v ++ [b] ++ layout w⟩
  | .gemm a va ca b vb cb out vo mode .nativeFast alpha beta => do
    let scalar ← live[out]?
    if live[a]? = some scalar ∧ live[b]? = some scalar ∧
        coefficientFits live scalar alpha ∧ coefficientFits live scalar beta then
      return ⟨.gemm, [NativeText.scalar scalar, a] ++ layout va ++ [ca.toNat, b] ++ layout vb ++
        [cb.toNat, out] ++ layout vo ++ [NativeText.gemmMode mode] ++ coefficient alpha ++ coefficient beta⟩
    else none
  | _ => none

/-- Recover the physical element type of a matrix call from the allocations in
the independently checked instruction sequence. Drop removes its handle. -/
def resolveCalls (instructions : List Native.Instruction) : Option (List Call) := do
  let mut live : Std.HashMap Nat Scalar := {}
  let mut calls := []
  for op in instructions do
    let call ← resolveInstruction live op
    calls := call :: calls
    match op with
    | .allocate a s _ => live := live.insert a s
    | .drop a => live := live.erase a
    | _ => pure ()
  return calls.reverse

@[reducible] def Item : Phase → Type
  | .optimization => Action
  | .execution => Call

instance (p : Phase) : DecidableEq (Item p) := by
  cases p <;> unfold Item <;> infer_instance

structure Effect (p : Phase) where
  input : Nat
  operation : Item p
  output : Nat

abbrev Block (p : Phase) := List (Effect p)

def block {p : Phase} (items : List (Item p)) : Block p :=
  items.zipIdx.map fun (op, i) => ⟨i, op, i + 1⟩

def operations {p : Phase} (b : Block p) := b.map Effect.operation

def ordered {p : Phase} (b : Block p) : Bool :=
  b.zipIdx.all fun (step, i) => step.input == i && step.output == i + 1

/-- The transition retains the result of the independent checker on every
logical action. Reborrows, releases and other erased events still participate
in its source schedule and final state. -/
structure Translation (opt : Block .optimization) (exe : Block .execution) where
  logicalOrder : ordered opt = true
  physicalOrder : ordered exe = true
  instructions : List Native.Instruction
  ownership : CheckedPlan ((operations opt).map Statement.action)
  lowered : Native.lower 4096 {} ((operations opt).map Statement.action) =
    .ok (ownership.finalState, instructions)
  physicalCalls : resolveCalls instructions = some (operations exe)
  abi : (operations exe).all Call.valid = true

def verify (opt : Block .optimization) (exe : Block .execution) : Option (Translation opt exe) := do
  if hopt : ordered opt = true then
    if hexe : ordered exe = true then
      let source := (operations opt).map Statement.action
      let .ok ownership := checkPlan source | none
      match h : Native.lower 4096 {} source with
      | .error _ => none
      | .ok (after, instructions) =>
        if final : after = ownership.finalState then
          if calls : (resolveCalls instructions : Option (List Call)) = (some (operations exe) : Option (List Call)) then
            if abi : (operations exe).all Call.valid = true then
              return ⟨hopt, hexe, instructions, ownership, final ▸ h, calls, abi⟩
            else none
          else none
        else none
    else none
  else none

structure Lowered (actions : List Action) where
  opt : Block .optimization
  original : operations opt = actions
  exe : Block .execution
  checked : Translation opt exe

def lower (actions : List Action) : Option (Lowered actions) := do
  let opt := block (p := .optimization) actions
  let .ok (_, code) := Native.lower 4096 {} (actions.map Statement.action) | none
  let calls ← resolveCalls code
  let exe := block (p := .execution) calls
  have origin : operations opt = actions := by
    simp only [opt, operations, block, List.map_map, Function.comp_def]
    exact List.zipIdx_map_fst 0 actions
  return ⟨opt, origin, exe, ← verify opt exe⟩

end VastitasKernel.MidIR.StorageEffects
