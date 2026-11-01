import VastitasKernel.StorageShapeFlow

/-! Direct arithmetic guards and native calls for the checked symbolic frame.
No symbolic frame, name table, initialization history or compiler checker is
linked into the program. Caller data is neither allocated nor copied by calls. -/
namespace VastitasKernel.Storage.Shapes.Native

structure Context where
  resources : Frame := {}
  slots : Slots := []
  narrowed : List Symbol := []
  deriving Repr, Inhabited

private def reject (message : String) : Except Error α := .error ⟨"E_RUNTIME_CODEGEN", message⟩
private def scalar : Scalar → Nat | .f64 => 0 | .complexF64 => 1
private def extent : Extent → String
  | .literal value => toString value
  | .slot name => s!"runtimeExtent_{name}"
private def layout (view : Layout) : String :=
  s!"0 {extent view.rows} {extent view.columns} {extent view.leading} {view.transposed}"
private def literal : Literal → String
  | .f64 bits => s!"0 {bits.toNat} 0"
  | .complexF64 real imaginary => s!"1 {real.toNat} {imaginary.toNat}"
private def coefficient : Option Coefficient → Except Error String
  | none => pure "0 0 0 0 0 0"
  | some (.literal value) => pure s!"1 {literal value} 0 0"
  | some (.loan _) => reject "runtime coefficient loan is unsupported"

def narrow (context : Context) (references : List Symbol) (indent : Nat) : Except Error (Context × String) := do
  let spaces := String.ofList (List.replicate indent ' ')
  let mut after := context
  let mut text := ""
  for name in references do
    if !after.narrowed.contains name then
      let helper ← match (after.slots.find? (·.1 == name)).map Prod.snd with
        | some .nat => pure "runtimeExtentNat"
        | some .int => pure "runtimeExtentInt"
        | _ => reject "runtime extent has no checked Nat/Int value slot"
      text := text ++ spaces ++ s!"let runtimeExtent_{name} ← {helper} resourceValue_{name}\n"
      after := {after with narrowed := name :: after.narrowed}
  return (after, text)

private def extentFits : Extent → Bool
  | .literal value => value < 2^64
  | .slot _ => true

def renderGuard (condition : Guard) (indent : Nat) : Except Error String := do
  let spaces := String.ofList (List.replicate indent ' ')
  let expression ← match condition with
    | .bound size maximum =>
      unless extentFits size && maximum < 2^64 do reject "guard constant exceeds native representation"
      pure s!"({extent size} : UInt64) ≤ {maximum}"
    | .equal left right =>
      if left == right then return ""
      unless extentFits left && extentFits right do reject "guard constant exceeds native representation"
      pure s!"({extent left} : UInt64) == {extent right}"
    | .layout type elements shape =>
      unless [elements, shape.rows, shape.columns, shape.leading].all extentFits do
        reject "layout constant exceeds native representation"
      pure s!"runtimeLayoutValid {scalar type} {extent elements} {extent shape.rows} {extent shape.columns} {extent shape.leading}"
    | .cell shape row column =>
      unless row < 2^64 && column < 2^64 &&
          [shape.rows, shape.columns, shape.leading].all extentFits do
        reject "cell guard constant exceeds native representation"
      pure s!"({row} : UInt64) < {extent shape.logicalRows} && ({column} : UInt64) < {extent shape.logicalColumns}"
  return spaces ++ s!"unless {expression} do\n" ++ spaces ++
    "  throw (IO.userError \"E_RUNTIME_GUARD: extent, layout or shape preflight failed\")\n"

def renderAction (before : Frame) (operation : Action) (indent : Nat) : Except Error String := do
  let spaces := String.ofList (List.replicate indent ' ')
  let text ← match operation with
    | .allocate _ type elements _ =>
      unless before.nextAllocation < 4096 && extentFits elements do reject "runtime allocation narrowing failed"
      pure s!"allocate shapeArena {before.nextAllocation} {scalar type} {extent elements}"
    | .drop name =>
      let allocation ← owner before name
      unless allocation.identity < 4096 do reject "runtime allocation identity exceeds native range"
      pure s!"drop shapeArena {allocation.identity}"
    | .fill name value =>
      let (_, allocation) ← usable before name true
      unless allocation.identity < 4096 do reject "runtime allocation identity exceeds native range"
      pure s!"fill shapeArena {allocation.identity} {layout allocation.layout} {literal value}"
    | .expect name row column value =>
      let (_, allocation) ← usable before name false
      unless allocation.identity < 4096 do reject "runtime allocation identity exceeds native range"
      pure s!"expect shapeArena {allocation.identity} {layout allocation.layout} {row} {column} {literal value}"
    | .gemm request =>
      let (_, a) ← usable before request.left false
      let (_, b) ← usable before request.right false
      let (_, c) ← usable before request.output true
      unless [a.identity, b.identity, c.identity].all (· < 4096) do reject "runtime allocation identity exceeds native range"
      let mode := match request.mode with | .overwrite => 0 | .accumulate => 1
      let operands := s!"shapeArena {a.identity} {layout a.layout} {request.conjugateLeft} {b.identity} {layout b.layout} {request.conjugateRight} {c.identity} {layout c.layout} {mode}"
      if request.alpha.isNone && request.beta.isNone then pure s!"VastitasGemmNative.gemm {operands}"
      else return spaces ++ s!"VastitasGemmNative.gemmScaled {operands} {← coefficient request.alpha} {← coefficient request.beta}\n"
    | .move .. | .borrow .. | .release .. => pure ""
  return if text.isEmpty then "" else spaces ++ text ++ "\n"

def generate (context : Context) (event : Event) (indent : Nat) : Except Error (Context × String) := do
  let (after, conditions, operation) ← match event with
    | .guard conditions => pure (context.resources, conditions, none)
    | .action operation => do
      let checked ← checkStep context.resources operation
      pure (checked.after, checked.guards, some operation)
  let references := event.references ++ conditions.flatMap Guard.references
  let (context, narrowed) ← narrow context references indent
  let guards ← conditions.mapM (renderGuard · indent)
  let operation ← match operation with
    | none => pure ""
    | some operation => renderAction context.resources operation indent
  return ({context with resources := after}, narrowed ++ String.join guards ++ operation)

end VastitasKernel.Storage.Shapes.Native
