import VastitasKernel.MidIR.IR
import VastitasKernel.StorageCodegen

set_option autoImplicit false

/-! Ordered effects of a static storage schedule. The optimization form retains
logical loans and owners. Only the existing storage checker can resolve them
to the allocation IDs and physical views of the execution form. -/
namespace VastitasKernel.MidIR.StorageEffects
open Storage

inductive Callee where
  | allocate | drop | fill | store | expect | copy | gemm | pack3 | regroup3
  | diagonalScale | diagonalAdjoint | diagonalPair
  deriving DecidableEq, BEq, Repr

def Callee.name : Callee → String
  | .allocate => "allocate" | .drop => "drop" | .fill => "fill"
  | .store => "store" | .expect => "expect" | .copy => "copy" | .gemm => "gemm"
  | .pack3 => "pack3" | .regroup3 => "regroup3"
  | .diagonalScale => "diagonal_scale" | .diagonalAdjoint => "diagonal_adjoint" | .diagonalPair => "diagonal_pair"

def Callee.all : List Callee := [.allocate, .drop, .fill, .store, .expect, .copy, .gemm, .pack3, .regroup3,
  .diagonalScale, .diagonalAdjoint, .diagonalPair]

def Callee.diagonalCount : Callee → Nat
  | .diagonalAdjoint => 2 | .diagonalScale | .diagonalPair => 1 | _ => 0

/-- All integer arguments use i64 at the C boundary. Layouts are flattened to
five words so the platform ABI for C struct values does not enter the IR. -/
inductive Operand where
  | allocation | extent | flag | scalar | bits | coefficientKind | dimension | grouping

private def viewSignature : List Operand := [.extent, .extent, .extent, .extent, .flag]

private def matrixSignature := [.allocation] ++ viewSignature
private def packingSignature := matrixSignature ++ matrixSignature ++ [.dimension, .dimension, .dimension]
private def inputMatrixSignature := matrixSignature ++ [.flag]
private def coefficientSignature : List Operand :=
  [.coefficientKind, .scalar, .bits, .bits, .allocation, .extent]

def Callee.signature : Callee → List Operand
  | .allocate => [.allocation, .scalar, .extent]
  | .drop => [.allocation]
  | .fill => [.allocation] ++ viewSignature ++ [.scalar, .bits, .bits]
  | .store | .expect => [.allocation] ++ viewSignature ++ [.extent, .extent, .scalar, .bits, .bits]
  | .copy => matrixSignature ++ matrixSignature
  | .pack3 => packingSignature
  | .regroup3 => packingSignature ++ [.grouping, .grouping]
  | .gemm => [.scalar] ++ inputMatrixSignature ++ inputMatrixSignature ++ matrixSignature ++
      [.flag] ++ coefficientSignature ++ coefficientSignature
  | .diagonalScale | .diagonalAdjoint => [.scalar] ++ matrixSignature ++ matrixSignature ++ [.flag]
  | .diagonalPair => [.scalar] ++ matrixSignature ++ matrixSignature ++ matrixSignature ++ matrixSignature ++ [.flag,.flag]

def Callee.arity (f : Callee) := f.signature.length

def Operand.accepts : Operand → Nat → Bool
  | .allocation, n => n < 2^32
  | .extent, n => n ≤ Storage.byteLimit
  | .flag, n => n < 2
  | .coefficientKind, n => n < 3
  | .scalar, n => n < 4
  | .bits, n => n < 2^64
  | .dimension, n => n ≤ Storage.dimensionLimit
  | .grouping, n => n < 54

structure Call where
  target : Callee
  arguments : List Nat
  diagonals : List Diagonal := []
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

private def matchesGrouping (dimensions : List Nat) (code rows columns : Nat) : Bool :=
  let g : Tensor.Grouping := ⟨[code % 3, code / 3 % 3, code / 9 % 3], code / 27 + 1⟩
  decide (g.Valid 3) && g.rows dimensions == rows && g.columns dimensions == columns

private def validPacking : List Nat → Bool
  | [_, _, rows, cols, _, 0, _, _, rows', cols', _, 0, i, k, j] =>
    rows == i && cols == k*j && rows' == i*j && cols' == k
  | [_, _, rows, cols, _, 0, _, _, rows', cols', _, 0, i, k, j, src, dst] =>
    matchesGrouping [i,k,j] src rows cols && matchesGrouping [i,k,j] dst rows' cols'
  | _ => false

private def readView : List Nat → Option (Layout × List Nat)
  | _id :: offset :: rows :: columns :: leading :: transposed :: rest =>
    some (⟨offset, rows, columns, leading, transposed == 1⟩, rest)
  | _ => none

/-- Interpret the physical view shapes exactly as the native calls do. The
logical resource checker supplies the ownership and nominal metric evidence. -/
private def validDiagonals (c : Call) : Bool := Id.run do
  if c.target.diagonalCount == 0 then return c.diagonals.isEmpty
  let tag :: args := c.arguments | return false
  let limit := if tag < 2 then 2^53 else 2^24
  let some (a, rest) := readView args | return false
  let some (b, rest) := readView rest | return false
  match c.target, c.diagonals with
  | .diagonalScale, [w] => return (!b.transposed && a.logicalColumns == 1 && b.columns == 1 &&
      a.logicalRows == b.rows && w.valid a.logicalRows limit)
  | .diagonalAdjoint, [source,target] => return (!b.transposed &&
      a.logicalRows == b.columns && a.logicalColumns == b.rows &&
      source.valid a.logicalColumns limit && target.valid a.logicalRows limit)
  | .diagonalPair, [w] =>
    let some (out, rest) := readView rest | return false
    let some (scratch, _) := readView rest | return false
    return (!out.transposed && !scratch.transposed && out.rows == 1 && out.columns == 1 &&
      a.logicalColumns == 1 && b.logicalColumns == 1 && scratch.columns == 1 &&
      a.logicalRows == scratch.rows && b.logicalRows == scratch.rows && w.valid scratch.rows limit)
  | _, _ => return false

def Call.valid (c : Call) : Bool :=
  c.arguments.length == c.target.arity && validDiagonals c &&
    (c.target.signature.zip c.arguments).all (fun (ty, n) => ty.accepts n) &&
    (match c.target with
     | .fill | .store | .expect =>
       match c.arguments.reverse with
       | imaginary :: real :: scalar :: _ => literalBits scalar real imaginary
       | _ => false
     | .gemm => validGemm c.arguments
     | .pack3 | .regroup3 => validPacking c.arguments
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

private def diagonalCall (target : Callee) (live : Std.HashMap Nat Scalar)
    (first : Nat × Layout) (rest : List (Nat × Layout)) (flags : List Bool)
    (tables : List Diagonal) : Option Call := do
  let scalar ← live[first.1]?
  guard (rest.all fun (id,_) => decide (live[id]? = some scalar))
  let operands := (first :: rest).flatMap fun (id,v) => id :: layout v
  return ⟨target, NativeText.scalar scalar :: operands ++ flags.map Bool.toNat, tables⟩

theorem diagonalCall_operands {target live first rest flags tables call}
    (resolved : diagonalCall target live first rest flags tables = some call) :
    ∃ scalar, live[first.1]? = some scalar ∧
      rest.all (fun (id,_) => decide (live[id]? = some scalar)) = true ∧
      call.target = target ∧ call.diagonals = tables ∧
      call.arguments = NativeText.scalar scalar ::
        (first :: rest).flatMap (fun (id,v) => id :: layout v) ++ flags.map Bool.toNat := by
  cases found : live[first.1]? with
  | none => simp [diagonalCall, found] at resolved
  | some scalar =>
    by_cases same : rest.all (fun (id,_) => decide (live[id]? = some scalar)) = true
    · simp [diagonalCall, found, same, guard] at resolved
      subst call
      exact ⟨scalar, rfl, same, rfl, rfl, by simp [List.append_assoc]⟩
    · simp [diagonalCall, found, same, guard] at resolved
      contradiction

def resolveInstruction (live : Std.HashMap Nat Scalar) : Native.Instruction → Option Call
  | .allocate a s n => some ⟨.allocate, [a, NativeText.scalar s, n], []⟩
  | .drop a => some ⟨.drop, [a], []⟩
  | .fill a v x => some ⟨.fill, [a] ++ layout v ++ literal x, []⟩
  | .store a v r c x => some ⟨.store, [a] ++ layout v ++ [r,c] ++ literal x, []⟩
  | .expect a v r c x => some ⟨.expect, [a] ++ layout v ++ [r,c] ++ literal x, []⟩
  | .copy a v b w => some ⟨.copy, [a] ++ layout v ++ [b] ++ layout w, []⟩
  | .pack3 a v b w i k j => some ⟨.pack3, [a] ++ layout v ++ [b] ++ layout w ++ [i,k,j], []⟩
  | .regroup3 a v b w dims src dst => do
    guard (dims.length == 3 && decide (src.Valid 3) && decide (dst.Valid 3))
    return ⟨.regroup3, [a] ++ layout v ++ [b] ++ layout w ++ dims ++ [src.code, dst.code], []⟩
  | .gemm a va ca b vb cb out vo mode .nativeFast alpha beta => do
    let scalar ← live[out]?
    if live[a]? = some scalar ∧ live[b]? = some scalar ∧
        coefficientFits live scalar alpha ∧ coefficientFits live scalar beta then
      return ⟨.gemm, [NativeText.scalar scalar, a] ++ layout va ++ [ca.toNat, b] ++ layout vb ++
        [cb.toNat, out] ++ layout vo ++ [NativeText.gemmMode mode] ++ coefficient alpha ++ coefficient beta, []⟩
    else none
  | .diagonalScale a va b vb w conj .nativeFast =>
    diagonalCall .diagonalScale live (a,va) [(b,vb)] [conj] [w]
  | .diagonalAdjoint a va b vb source target conj .nativeFast =>
    diagonalCall .diagonalAdjoint live (a,va) [(b,vb)] [conj] [source,target]
  | .diagonalPair a va b vb out vo scratch vs w cl cr .nativeFast =>
    diagonalCall .diagonalPair live (a,va) [(b,vb),(out,vo),(scratch,vs)] [cl,cr] [w]
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

/-- The normal successor of a call is the following block. Its error successor
is the common arena cleanup. Each control edge transfers the current storage
state to the destination block argument. The final index is the normal exit. -/
inductive Op where
  | call (operation : Call)
  | branch (condition : Bool) (otherwisePC : Nat)
  | jump (joinPC : Nat)
  deriving DecidableEq, BEq, Repr

instance : Inhabited Op := ⟨.jump 0⟩

def Op.call? : Op → Option Call
  | .call c => some c | _ => none

def validGraph (ops : List Op) : Bool :=
  let exit := ops.length
  ops.zipIdx.all fun (op,pc) => match op with
    | .call c => c.valid
    | .branch _ target | .jump target => pc < target && target ≤ exit

/-- The incoming storage state follows one successor of the current block.
The program counter advances on every edge of a checked graph. -/
def path (ops : Array Op) : Option (List Call) := Id.run do
  let mut trace := []
  let mut pc := 0
  for _ in [:ops.size] do
    let some op := ops[pc]? | break
    match op with
    | .call c => trace := c :: trace; pc := pc + 1
    | .branch condition target => pc := if condition then pc + 1 else target
    | .jump target => pc := target
  return if pc == ops.size then some trace.reverse else none

private inductive Arm where
  | first (start : Nat) (condition : Bool) (entry : Std.HashMap Nat Scalar)
  | second (jump : Nat)

/-- Resolve both branches from the live allocations at their common entry.
Only the authoritative storage checker decides whether the two exits join. -/
def resolveGraph (instructions : List Native.Instruction) : Option (List Op) := do
  let mut live : Std.HashMap Nat Scalar := {}
  let mut arms : List Arm := []
  let mut ops : Array Op := #[]
  let mut skipped := false
  for op in instructions do
    match op, skipped with
    | .branch condition, false =>
      arms := .first ops.size condition live :: arms
      ops := ops.push (.branch condition 0)
    | .skip, false => skipped := true
    | .otherwise, true =>
      let .first start condition entry :: outer := arms | none
      arms := .second ops.size :: outer
      ops := (ops.set! start (.branch condition (ops.size+1))).push (.jump 0)
      live := entry
      skipped := false
    | .finish, true =>
      let .second jump :: outer := arms | none
      arms := outer
      ops := ops.set! jump (.jump ops.size)
      skipped := false
    | _, false =>
      let c ← resolveInstruction live op
      ops := ops.push (.call c)
      match op with
      | .allocate a s _ => live := live.insert a s
      | .drop a => live := live.erase a
      | _ => pure ()
    | _, true => none
  guard (arms.isEmpty && !skipped)
  return ops.toList

/-- Independent structured interpretation of the storage checker's branch
markers. It neither uses block indices nor follows the generated jump table. -/
def selectedInstructions (instructions : List Native.Instruction) : Option (List Native.Instruction) := do
  let mut enabled := true
  let mut scopes : List (Bool × Option Bool) := []
  let mut result := []
  for op in instructions do
    match op with
    | .branch condition =>
      scopes := (enabled,some condition) :: scopes
      enabled := enabled && condition
    | .otherwise =>
      let (parent,some condition) :: outer := scopes | none
      scopes := (parent,none) :: outer
      enabled := parent && !condition
    | .finish =>
      let (parent,none) :: outer := scopes | none
      scopes := outer
      enabled := parent
    | .skip => pure ()
    | _ => if enabled then result := op :: result
  guard scopes.isEmpty
  return result.reverse

@[reducible] def Item : Phase → Type
  | .optimization => Storage.Statement
  | .execution => Op

instance (p : Phase) : DecidableEq (Item p) := by
  cases p <;> unfold Item <;> infer_instance

inductive Destination where
  | block (index : Nat)
  | failed
  deriving DecidableEq, BEq, Repr

/-- A transfer supplies the producing instruction's effect token as a block
argument. The two arms of a conditional are mutually exclusive. -/
structure Transfer where
  destination : Destination
  argument : Nat
  deriving DecidableEq, BEq, Repr

def successors (p : Phase) (op : Item p) (pc : Nat) : List Destination := match p with
  | .optimization => [.block (pc+1)]
  | .execution => match op with
    | .call _ => [.block (pc+1), .failed]
    | .branch _ target => [.block (pc+1), .block target]
    | .jump target => [.block target]

def transfers (p : Phase) (op : Item p) (pc : Nat) : List Transfer :=
  (successors p op pc).map fun target => ⟨target, pc+1⟩

structure Effect (p : Phase) where
  input : Nat
  operation : Item p
  output : Nat
  outgoing : List Transfer

abbrev Block (p : Phase) := List (Effect p)

def block {p : Phase} (items : List (Item p)) : Block p :=
  items.zipIdx.map fun (op, i) => ⟨i, op, i + 1, transfers p op i⟩

def operations {p : Phase} (b : Block p) := b.map Effect.operation

def ordered {p : Phase} (b : Block p) : Bool :=
  b.zipIdx.all fun (step, i) => step.input == i && step.output == i + 1 &&
    decide (step.outgoing = transfers p step.operation i)

/-- The transition retains the result of the independent checker on every
logical action. Reborrows, releases and other erased events still participate
in its source schedule and final state. -/
structure Translation (opt : Block .optimization) (exe : Block .execution) where
  logicalOrder : ordered opt = true
  physicalOrder : ordered exe = true
  instructions : List Native.Instruction
  ownership : CheckedPlan (operations opt)
  lowered : Native.lower 4096 {} (operations opt) =
    .ok (ownership.finalState, instructions)
  physicalGraph : resolveGraph instructions = some (operations exe)
  abi : validGraph (operations exe) = true
  trace : List Call
  fromInstructions : (selectedInstructions instructions).bind resolveCalls = some trace
  fromGraph : path (operations exe).toArray = some trace

def verify (opt : Block .optimization) (exe : Block .execution) : Option (Translation opt exe) := do
  if hopt : ordered opt = true then
    if hexe : ordered exe = true then
      let source := operations opt
      let .ok ownership := checkPlan source | none
      match h : Native.lower 4096 {} source with
      | .error _ => none
      | .ok (after, instructions) =>
        if final : after = ownership.finalState then
          if exactGraph : resolveGraph instructions = some (operations exe) then
            if abi : validGraph (operations exe) = true then
              match fromInstructions : (selectedInstructions instructions).bind resolveCalls with
              | none => none
              | some trace =>
                if fromGraph : path (operations exe).toArray = some trace then
                  return ⟨hopt, hexe, instructions, ownership, final ▸ h, exactGraph, abi,
                    trace, fromInstructions, fromGraph⟩
                else none
            else none
          else none
        else none
    else none
  else none

structure Lowered (statements : List Statement) where
  opt : Block .optimization
  original : operations opt = statements
  exe : Block .execution
  checked : Translation opt exe

def lower (statements : List Statement) : Option (Lowered statements) := do
  let opt := block (p := .optimization) statements
  let .ok (_, code) := Native.lower 4096 {} statements | none
  let graph ← resolveGraph code
  let exe := block (p := .execution) graph
  have origin : operations opt = statements := by
    simp only [opt, operations, block, List.map_map, Function.comp_def]
    exact List.zipIdx_map_fst 0 statements
  return ⟨opt, origin, exe, ← verify opt exe⟩

end VastitasKernel.MidIR.StorageEffects
