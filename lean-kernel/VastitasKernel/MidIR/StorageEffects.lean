import VastitasKernel.MidIR.IR
import VastitasKernel.StorageCodegen

set_option autoImplicit false

/-! Ordered effects of a static storage schedule. The optimization form retains
logical loans and owners. Only the existing storage checker can resolve them
to the allocation IDs and physical views of the execution form. -/
namespace VastitasKernel.MidIR.StorageEffects
open Storage

inductive Callee where
  | allocate | drop | fill | store | expect | copy
  deriving DecidableEq, BEq, Repr

def Callee.name : Callee → String
  | .allocate => "allocate" | .drop => "drop" | .fill => "fill"
  | .store => "store" | .expect => "expect" | .copy => "copy"

def Callee.all : List Callee := [.allocate, .drop, .fill, .store, .expect, .copy]

/-- All integer arguments use i64 at the C boundary. Layouts are flattened to
five words so the platform ABI for C struct values does not enter the IR. -/
inductive Operand where
  | allocation | extent | transpose | scalar | bits

private def viewSignature : List Operand := [.extent, .extent, .extent, .extent, .transpose]

def Callee.signature : Callee → List Operand
  | .allocate => [.allocation, .scalar, .extent]
  | .drop => [.allocation]
  | .fill => [.allocation] ++ viewSignature ++ [.scalar, .bits, .bits]
  | .store | .expect => [.allocation] ++ viewSignature ++ [.extent, .extent, .scalar, .bits, .bits]
  | .copy => [.allocation] ++ viewSignature ++ [.allocation] ++ viewSignature

def Callee.arity (f : Callee) := f.signature.length

def Operand.accepts : Operand → Nat → Bool
  | .allocation, n => n < 2^32
  | .extent, n => n ≤ Storage.byteLimit
  | .transpose, n => n < 2
  | .scalar, n => n < 4
  | .bits, n => n < 2^64

structure Call where
  target : Callee
  arguments : List Nat
  deriving DecidableEq, BEq, Repr

def Call.valid (c : Call) : Bool :=
  c.arguments.length == c.target.arity &&
    (c.target.signature.zip c.arguments).all (fun (ty, n) => ty.accepts n) &&
    (match c.target with
     | .fill | .store | .expect =>
       match c.arguments.reverse with
       | imaginary :: real :: scalar :: _ =>
         (scalar != 0 && scalar != 2 || imaginary == 0) &&
           (scalar < 2 || real < 2^32 && imaginary < 2^32)
       | _ => false
     | _ => true)

private def layout (v : Layout) : List Nat :=
  [v.offset, v.rows, v.columns, v.leading, v.transposed.toNat]

private def literal (value : Literal) : List Nat :=
  NativeText.scalar value.scalar :: (match value with
    | .f32 x => [x.toNat, 0] | .f64 x => [x.toNat, 0]
    | .complexF32 r i => [r.toNat, i.toNat] | .complexF64 r i => [r.toNat, i.toNat])

def physical : Native.Instruction → Option Call
  | .allocate a s n => some ⟨.allocate, [a, NativeText.scalar s, n]⟩
  | .drop a => some ⟨.drop, [a]⟩
  | .fill a v x => some ⟨.fill, [a] ++ layout v ++ literal x⟩
  | .store a v r c x => some ⟨.store, [a] ++ layout v ++ [r,c] ++ literal x⟩
  | .expect a v r c x => some ⟨.expect, [a] ++ layout v ++ [r,c] ++ literal x⟩
  | .copy a v b w => some ⟨.copy, [a] ++ layout v ++ [b] ++ layout w⟩
  | _ => none

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
  physicalCalls : instructions.mapM physical = some (operations exe)
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
          if calls : (instructions.mapM physical : Option (List Call)) = (some (operations exe) : Option (List Call)) then
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
  let calls ← code.mapM physical
  let exe := block (p := .execution) calls
  have origin : operations opt = actions := by
    simp only [opt, operations, block, List.map_map, Function.comp_def]
    exact List.zipIdx_map_fst 0 actions
  return ⟨opt, origin, exe, ← verify opt exe⟩

end VastitasKernel.MidIR.StorageEffects
