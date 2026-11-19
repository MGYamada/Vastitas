import VastitasKernel.LLVM.ExactLibrary
import VastitasKernel.LLVM.ExitFunction
import VastitasKernel.MidIR.PackageObservation

set_option autoImplicit false

/-! A hosted module of boxed integer functions. Direct call symbols index the
already checked module and the callee borrows every argument, including aliases. -/
namespace VastitasKernel.LLVM.ExactProgram
open MidIR ExactLibrary

inductive Instruction where
  | primitive (step : Step)
  | invoke (target : Nat) (refs : List Nat)
  deriving DecidableEq

structure Function where
  params : List Kind
  output : Kind
  ops : List Instruction
  result : Nat
  deriving DecidableEq

structure Code where
  header : TargetHeader
  functions : Array Function
  entry : Nat
  deriving DecidableEq

private def fnName (i : Nat) := s!"@vq_f{i}"
private def scope (i : Nat) := s!"{i}_"

private def declaration : Instruction → Option String
  | .primitive s => some ("declare ptr " ++ symbol s.callee ++ "(" ++
    String.intercalate ", " (List.replicate s.argCount "ptr") ++ ")")
  | .invoke .. => none

private def body (f : Function) (id : Nat) : List String := Id.run do
  let ops := f.ops.zipIdx f.params.length
  let constants := ops.filterMap fun (op,i) => match op with
    | .primitive s => s.literal.map fun v => global v i (scope id)
    | _ => none
  let signature := "; boxed (" ++ String.intercalate ", " (f.params.map Kind.name) ++ ") -> " ++ f.output.name
  let params := String.intercalate ", " ((List.range f.params.length).map arg)
  let calls := ops.map fun (op,i) => match op with
    | .primitive s => call s i (scope id)
    | .invoke callee refs => "  " ++ slot i ++ " = call ptr " ++ fnName callee ++
      "(" ++ String.intercalate ", " (refs.map arg) ++ ")"
  let keep := if f.result < f.params.length then [rcCall "retain" f.result] else []
  let drops := (List.range' f.params.length f.ops.length).reverse.filter (· != f.result)
  return [signature] ++ constants ++ [s!"define internal ptr {fnName id}({params}) " ++ "{","entry:"] ++
    calls ++ keep ++ drops.map (rcCall "release") ++ ["  ret " ++ arg f.result,"}"]

def Code.bodyLines (c : Code) : List String :=
  let calls := (c.functions.toList.flatMap fun f => f.ops.filterMap declaration).eraseDups
  let declarations := ["declare void @vastitas_initialize_v1()", "declare i32 @vastitas_exit_status_v1(ptr)",
    "declare void @vastitas_retain_v1(ptr)", "declare void @vastitas_release_v1(ptr)"]
  let main := ["define i32 @main() {","entry:","  call void @vastitas_initialize_v1()",
    "  %result = call ptr " ++ fnName c.entry ++ "()", "  %status = call i32 @vastitas_exit_status_v1(ptr %result)",
    "  ret i32 %status","}"]
  declarations ++ calls ++ (c.functions.toList.zipIdx.flatMap fun (f,i) => body f i) ++ main

def Code.print (c : Code) : List UInt8 :=
  c.header.print ++ ("\n" ++ String.intercalate "\n" c.bodyLines ++ "\n").toUTF8.data.toList

private def typed (c : Code) (i : Nat) (f : Function) : Bool := Id.run do
  unless f.params.length + f.ops.length ≤ 4096 do return false
  let mut slots := (f.params.map Kind.type).toArray
  for op in f.ops do
    match op with
    | .primitive (.nat _) => slots := slots.push .nat
    | .primitive (.int _) => slots := slots.push .int
    | .primitive (.apply op refs) =>
      unless refs.mapM (slots[·]?) == some op.operands do return false
      slots := slots.push op.result
    | .invoke target refs =>
      let some callee := c.functions[target]? | return false
      unless target < i && refs.mapM (slots[·]?) == some (callee.params.map Kind.type) do return false
      slots := slots.push callee.output.type
  return slots[f.result]? == some f.output.type

def Code.valid (c : Code) : Bool := Id.run do
  let some main := c.functions[c.entry]? | return false
  unless main.params.isEmpty && main.output == .int && c.functions.size ≤ 4096 do return false
  return c.functions.toList.zipIdx.all fun (f,i) => typed c i f

private def readBody (chunk : String) (id : Nat) : Option Function := do
  let signature :: lines := chunk.splitOn "\n" | none
  let [args,ret] := signature.splitOn ") -> " | none
  let params ← (fields args).mapM Kind.read
  let output ← Kind.read ret
  let mut constants : Std.HashMap Nat String := {}
  let mut ops := #[]
  let mut result := none
  for line in lines do
    if line.startsWith "@c" then
      let (i,v) ← readGlobal line (scope id)
      constants := constants.insert i v
    else if line.startsWith "  %v" then
      let i := params.length + ops.size
      guard (i < 4096)
      match line.splitOn " = call ptr @vq_f" with
      | [dst,tail] =>
        guard (dst == "  " ++ slot i)
        let [callee,args] := tail.splitOn "(" | none
        let refs ← (fields (← strip args "" ")")).mapM (indexOf · "ptr %v")
        ops := ops.push (.invoke (← indexOf callee "") refs)
      | _ => ops := ops.push (.primitive (← readCall constants i line (scope id)))
    else if line.startsWith "  ret ptr %v" then
      result := some (← indexOf line "  ret ptr %v")
  return ⟨params,output,ops.toList,← result⟩

private def decode (bytes : List UInt8) : Option Code := do
  guard (bytes.length ≤ 16777216)
  let (header,tail) ← TargetHeader.readPrefix (bytes.take TargetHeader.maxBytes)
  let text ← String.fromUTF8? ⟨(tail ++ bytes.drop TargetHeader.maxBytes).toArray⟩
  let [functions,main] := text.splitOn "define i32 @main() {" | none
  let _ :: sections := functions.splitOn "; boxed (" | none
  guard (sections.length ≤ 4096)
  let functions ← sections.zipIdx.mapM fun (s,i) => readBody s i
  let [_,tail] := main.splitOn "  %result = call ptr @vq_f" | none
  let [id,_] := tail.splitOn "()\n" | none
  return ⟨header,functions.toArray,← indexOf id ""⟩

def parse (bytes : List UInt8) : Option Code :=
  match decode bytes with
  | some c => if c.valid = true ∧ bytes = c.print then some c else none
  | none => none

theorem parse_sound {bytes : List UInt8} {c : Code} (h : parse bytes = some c) :
    c.valid = true ∧ bytes = c.print := by
  unfold parse at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  next ok => cases h; exact ok

private def translateFn (f : MidIR.Function .execution) : Option Function := do
  let params ← f.params.toList.mapM Kind.ofTy
  let output ← Kind.ofTy f.result
  let [b] := f.blocks.toList | none
  guard (b.params == f.params && f.params.size + b.ops.size ≤ 4096)
  let .ret ⟨0⟩ ⟨0,result⟩ := b.term | none
  let ops ← b.ops.toList.mapM fun op => do
    guard (op.args.all (·.block == 0))
    let refs := op.args.map (·.slot)
    match op.code, refs with
    | .natural n, [] => pure (Instruction.primitive (.nat n))
    | .integer n, [] => pure (.primitive (.int n))
    | .exactOp op, args => pure (.primitive (.apply op args))
    | .call t, args => pure (.invoke t.symbol args)
    | _, _ => none
  return ⟨params,output,ops,result⟩

def translate (m : MidIR.Module .execution) (header : TargetHeader) : Option Code := do
  let entry ← m.entry
  guard (m.functions.size ≤ 4096 && validSymbols m)
  let fs ← m.functions.mapM translateFn
  let c := Code.mk header fs entry
  guard c.valid
  return c

open Indexed.Core.Semantics in
private def evalFn (functions : Array Function) : Nat → Nat → List Value → StateT Nat Option Value
  | 0, _, _ => failure
  | depth+1, i, args => do
    let f ← liftM (functions[i]?)
    let remaining ← get
    let cost := 1 + f.params.length + f.ops.length
    guard (cost ≤ remaining)
    set (remaining - cost)
    let mut values := args.toArray
    for op in f.ops do
      let v ← match op with
        | .primitive (.nat n) => pure (.natural n)
        | .primitive (.int n) => pure (.integer n)
        | .primitive (.apply op refs) => liftM (do Evaluation.exactValue op (← refs.mapM (values[·]?)))
        | .invoke idx refs => evalFn functions depth idx (← liftM (refs.mapM (values[·]?)))
      -- Every operand has already passed this bound before multiplication.
      let bounded : Bool := match v with
        | .natural n => n.log2 < 4096 | .integer n => n.natAbs.log2 < 4096 | _ => false
      guard bounded
      values := values.push v
    liftM (values[f.result]?)

def Code.entryValue (c : Code) : Option Int := do
  let .integer n ← (evalFn c.functions c.functions.size c.entry []).run' 32768 | none
  return n

open ResourceSource in
structure Artifact {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main)
    (header : TargetHeader) extends ExitFunction.CheckedSites req where
  linked : PackageLink.Artifact req
  model : Code
  lowered : translate linked.exe header = some model
  target : model.header = header
  fuel : Nat
  cost : FiniteCost.entryWith true (PackageLink.core req) = some fuel
  value : Int
  modeled : model.entryValue = some value
  core : FiniteCost.coreEntry (PackageLink.core req) fuel = some (.integer value)
  opt : PackageLink.runEntry linked.opt fuel = some (.integer value)
  exe : PackageLink.runEntry linked.exe fuel = some (.integer value)

open ResourceSource UnaryFunction in
def compile {json : Lean.Json} {main : Bool} (req : Wire.CheckedInput json main) (header : TargetHeader) :
    Option (Artifact req header) := do
  let linked ← PackageLink.compile req
  let ⟨model,lowered⟩ ← getChecked (translate linked.exe header)
  -- A root declaration or a sealed family can require a linked body even when
  -- the entry has no calls. Single-function entries use the scalar profile.
  guard (model.functions.size > 1)
  let ⟨target⟩ ← confirm (model.header = header)
  let ⟨fuel,cost⟩ ← getChecked (FiniteCost.entryWith true (PackageLink.core req))
  let ⟨value,modeled⟩ ← getChecked model.entryValue
  let ⟨core⟩ ← confirm (FiniteCost.coreEntry (PackageLink.core req) fuel = some (.integer value))
  let ⟨opt⟩ ← confirm (PackageLink.runEntry linked.opt fuel = some (.integer value))
  let ⟨exe⟩ ← confirm (PackageLink.runEntry linked.exe fuel = some (.integer value))
  return {
    toCheckedSites := ← ExitFunction.checkSites req, linked, model, lowered, target, fuel, cost,
    value, modeled, core, opt, exe}

end VastitasKernel.LLVM.ExactProgram
