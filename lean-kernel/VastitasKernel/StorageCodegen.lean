import VastitasKernel.Storage

/-! Lower the exact checked resource schedule to synchronous native calls.
Logical owners/loans are reconstructed at compile time, not interpreted in the
element loop. A raw native plan is independently re-lowered before generation. -/
namespace VastitasKernel.Storage.Native

inductive Instruction where
  | allocate (allocation : Nat) (scalar : Scalar) (elements : Nat)
  | drop (allocation : Nat)
  | fill (allocation : Nat) (layout : Layout) (value : Literal)
  | store (allocation : Nat) (layout : Layout) (row column : Nat) (value : Literal)
  | expect (allocation : Nat) (layout : Layout) (row column : Nat) (value : Literal)
  | copy (source : Nat) (input : Layout) (target : Nat) (output : Layout)
  | pack3 (source : Nat) (input : Layout) (target : Nat) (output : Layout) (i k j : Nat)
  | regroup3 (source : Nat) (input : Layout) (target : Nat) (output : Layout)
      (dimensions : List Nat) (inputGrouping outputGrouping : Tensor.Grouping)
  | gemm (left : Nat) (leftView : Layout) (conjugateLeft : Bool)
      (right : Nat) (rightView : Layout) (conjugateRight : Bool)
      (output : Nat) (outputView : Layout) (mode : GemmMode) (policy : NumericalPolicy)
      (alpha beta : ResolvedCoefficient := .default)
  | diagonalAdjoint (input : Nat) (inputView : Layout) (output : Nat) (outputView : Layout)
      (source target : Diagonal) (conjugate : Bool) (policy : NumericalPolicy)
  | diagonalScale (input : Nat) (inputView : Layout) (output : Nat) (outputView : Layout)
      (diagonal : Diagonal) (conjugate : Bool) (policy : NumericalPolicy)
  | diagonalPair (left : Nat) (leftView : Layout) (right : Nat) (rightView : Layout)
      (output : Nat) (outputView : Layout) (scratch : Nat) (scratchView : Layout)
      (diagonal : Diagonal) (conjugateLeft conjugateRight : Bool) (policy : NumericalPolicy)
  | branch (condition : Bool)
  | otherwise | finish | skip
  deriving Repr, BEq, DecidableEq, Inhabited

private def reject (message : String) : Except Error α := .error ⟨"E_RESOURCE_CODEGEN", message⟩

def action (state : State) : Action → Except Error (List Instruction)
  | .allocate _ scalar elements => pure [.allocate state.nextAllocation scalar elements]
  | .drop owner => do
    let some allocation := state.owner? owner | reject "missing owner during native lowering"
    pure [.drop allocation.identity]
  | .fill name value => do
    let some loan := state.loan? name | reject "missing fill loan during native lowering"
    pure [.fill loan.allocation loan.layout value]
  | .store name row column value => do
    let some loan := state.loan? name | reject "missing store loan during native lowering"
    pure [.store loan.allocation loan.layout row column value]
  | .expect name row column value => do
    let some loan := state.loan? name | reject "missing read loan during native lowering"
    pure [.expect loan.allocation loan.layout row column value]
  | .copy source target => do
    let some input := state.loan? source | reject "missing copy source during native lowering"
    let some output := state.loan? target | reject "missing copy target during native lowering"
    pure [.copy input.allocation input.layout output.allocation output.layout]
  | .pack3 source target i k j => do
    let some input := state.loan? source | reject "missing packing source during native lowering"
    let some output := state.loan? target | reject "missing packing target during native lowering"
    pure [.pack3 input.allocation input.layout output.allocation output.layout i k j]
  | .regroup3 source target dimensions inputGrouping outputGrouping => do
    let some input := state.loan? source | reject "missing regrouping source during native lowering"
    let some output := state.loan? target | reject "missing regrouping target during native lowering"
    pure [.regroup3 input.allocation input.layout output.allocation output.layout dimensions inputGrouping outputGrouping]
  | .gemm request => do
    let checked ← checkGemm state request
    let args := checked.operands
    pure [.gemm args.left.allocation args.left.layout request.conjugateLeft
      args.right.allocation args.right.layout request.conjugateRight
      args.output.allocation args.output.layout request.mode request.policy checked.alpha.value checked.beta.value]
  | .diagonalAdjoint request => do
    let operands ← checkDiagonalAdjoint state request
    pure [.diagonalAdjoint operands.input.allocation operands.input.layout operands.output.allocation
      operands.output.layout request.source request.target request.conjugate request.policy]
  | .diagonalScale request => do
    let operands ← checkDiagonalScale state request
    pure [.diagonalScale operands.input.allocation operands.input.layout operands.output.allocation
      operands.output.layout request.diagonal request.conjugate request.policy]
  | .diagonalPair request => do
    let _ ← diagonalPairTransition state request
    let some left := state.loan? request.left | reject "missing diagonal pairing left input"
    let some right := state.loan? request.right | reject "missing diagonal pairing right input"
    let some output := state.loan? request.output | reject "missing diagonal pairing output"
    let some scratch := state.owner? request.scratch | reject "missing diagonal pairing scratch owner"
    pure [.diagonalPair left.allocation left.layout right.allocation right.layout
      output.allocation output.layout scratch.identity request.layout request.diagonal
      request.conjugateLeft request.conjugateRight request.policy]
  | .move .. | .borrow .. | .release .. | .transpose .. |
      .captureDependency .. | .requireDependency .. | .forgetDependency .. => pure []

def lower : Nat → State → List Statement → Except Error (State × List Instruction)
  | _, state, [] => pure (state, [])
  | 0, _, _ :: _ => .error ⟨"E_RESOURCE_CODEGEN", "native lowering exceeds traversal bound"⟩
  | fuel + 1, state, first :: rest => do
    let (after, instructions) ← match first with
      | .action operation => do
        let after ← checkAction state operation
        pure (after, ← action state operation)
      | .branch condition yes no => do
        let (left, yesCode) ← lower fuel state yes
        let (right, noCode) ← lower fuel {state with nextAllocation := left.nextAllocation} no
        let after ← join left right
        pure (after, [.branch condition] ++ yesCode ++ [.skip, .otherwise] ++ noCode ++ [.skip, .finish])
    let (finalState, restCode) ← lower fuel after rest
    pure (finalState, instructions ++ restCode)

structure Plan where
  input : List Statement
  instructions : List Instruction

structure Checked (plan : Plan) where
  source : CheckedPlan plan.input
  lowered : lower 4096 {} plan.input = .ok (source.finalState, plan.instructions)

/-- Reconstruct logical rights and every native operand from the source IR.
Changing a native allocation, offset, payload, branch or operation invalidates
the equality; there is no trusted native-instruction flag. -/
def audit (plan : Plan) : Except Error (Checked plan) := do
  let source ← checkPlan plan.input
  match lowered : lower 4096 {} plan.input with
  | .error diagnostic => .error diagnostic
  | .ok result =>
    if exactPlan : result = (source.finalState, plan.instructions) then
      .ok ⟨source, exactPlan ▸ lowered⟩
    else reject "native instructions differ from the exact checked resource schedule"

def compile (input : List Statement) : Except Error Plan := do
  let _ ← checkPlan input
  let (_, instructions) ← lower 4096 {} input
  let plan := {input, instructions}
  let _ ← audit plan
  pure plan

private def scalar : Scalar → Nat | .f64 => 0 | .complexF64 => 1
private def layout (view : Layout) : String :=
  s!"{view.offset} {view.rows} {view.columns} {view.leading} {view.transposed}"
private def literal : Literal → String
  | .f64 bits => s!"0 {bits.toNat} 0"
  | .complexF64 real imaginary => s!"1 {real.toNat} {imaginary.toNat}"

private def coefficient : ResolvedCoefficient → String
  | .default => "0 0 0 0 0 0"
  | .literal value => s!"1 {literal value} 0 0"
  | .view allocation offset => s!"2 0 0 0 {allocation} {offset}"

private def diagonal (value : Diagonal) : String :=
  let digits := #["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"]
  let bytes := value.entries.flatMap fun bits => (List.range 8).map fun index =>
    let byte := bits.toNat / 2^(8 * index) % 256
    digits[byte / 16]! ++ digits[byte % 16]!
  s!"{value.uniform} (VastitasStorageNative.diagonalData \"{String.join bytes}\")"

private def render (instructions : List Instruction) : Except Error String := do
  let mut indent := 4
  let mut result := ""
  for instruction in instructions do
    let spaces := String.ofList (List.replicate indent ' ')
    match instruction with
    | .branch condition =>
      result := result ++ spaces ++ s!"if {condition} then\n"
      indent := indent + 2
    | .otherwise =>
      if indent < 6 then reject "unbalanced native branch"
      result := result ++ String.ofList (List.replicate (indent - 2) ' ') ++ "else\n"
    | .finish =>
      if indent < 6 then reject "unbalanced native branch"
      indent := indent - 2
    | other =>
      let line := match other with
        | .allocate id type count => s!"allocate arena {id} {scalar type} {count}"
        | .drop id => s!"drop arena {id}"
        | .fill id view value => s!"fill arena {id} {layout view} {literal value}"
        | .store id view row column value => s!"store arena {id} {layout view} {row} {column} {literal value}"
        | .expect id view row column value => s!"expect arena {id} {layout view} {row} {column} {literal value}"
        | .copy source input target output => s!"copy arena {source} {layout input} {target} {layout output}"
        | .pack3 source input target output i k j => s!"pack3 arena {source} {layout input} {target} {layout output} {i} {k} {j}"
        | .diagonalAdjoint input inputView output outputView source target conjugate _ =>
          s!"VastitasStorageNative.diagonalAdjoint arena {input} {layout inputView} {output} {layout outputView} {diagonal source} {diagonal target} {conjugate}"
        | .diagonalScale input inputView output outputView weights conjugate _ =>
          s!"VastitasStorageNative.diagonalScale arena {input} {layout inputView} {output} {layout outputView} {diagonal weights} {conjugate}"
        | .diagonalPair left leftView right rightView output outputView scratch scratchView weights conjugateLeft conjugateRight _ =>
          s!"VastitasGemmNative.diagonalPair arena {left} {layout leftView} {right} {layout rightView} {output} {layout outputView} {scratch} {layout scratchView} {diagonal weights} {conjugateLeft} {conjugateRight}"
        | .regroup3 source input target output dimensions inputGrouping outputGrouping =>
          s!"regroup3 arena {source} {layout input} {target} {layout output} {(dimensions[0]?).getD 0} {(dimensions[1]?).getD 0} {(dimensions[2]?).getD 0} {inputGrouping.code} {outputGrouping.code}"
        | .gemm left leftView conjugateLeft right rightView conjugateRight output outputView mode _ alpha beta =>
          let mode := match mode with | .overwrite => 0 | .accumulate => 1
          let operands := s!"arena {left} {layout leftView} {conjugateLeft} {right} {layout rightView} {conjugateRight} {output} {layout outputView} {mode}"
          if alpha == .default && beta == .default then s!"VastitasGemmNative.gemm {operands}"
          else s!"VastitasGemmNative.gemmScaled {operands} {coefficient alpha} {coefficient beta}"
        | _ => "pure ()"
      result := result ++ spaces ++ line ++ "\n"
  if indent != 4 then reject "unclosed native branch"
  return result

/-- Checked operations for composition with another independently checked
executable body. This repeats the same full original-plan/instruction audit. -/
def generateBody (plan : Plan) : Except Error String := do
  let _ ← audit plan
  render plan.instructions

def Plan.needsNumerical (plan : Plan) : Bool :=
  plan.instructions.any fun instruction => match instruction with | .gemm .. | .diagonalPair .. => true | _ => false

/-- Generation accepts a raw plan only after independently auditing it again.
Cleanup is structured IO, including runtime assertion/allocation failures.
The optional reporting entry point is for native regression/cost fixtures. -/
def generate (plan : Plan) (report : Bool := false) (byteBudget : Nat := byteLimit) : Except Error String := do
  let _ ← audit plan
  if byteBudget > byteLimit then reject "native live-byte budget exceeds profile"
  let operations ← generateBody plan
  let reporting := if report then
    "    let counters ← stats arena\n    IO.println counters\n" else ""
  let numericalImport := if plan.needsNumerical then "import VastitasGemmNative\n" else ""
  return "import VastitasStorageNative\n" ++ numericalImport ++ "\nopen VastitasStorageNative\n\n" ++
    "def main : IO Unit := do\n" ++ s!"  let arena ← newArena {byteBudget}\n  try\n" ++
    operations ++ "    pure ()\n  finally\n    close arena\n" ++ reporting

end VastitasKernel.Storage.Native
