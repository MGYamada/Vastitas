import VastitasKernel.LLVM.ExitMain
import VastitasKernel.MidIR.StorageEffects

set_option autoImplicit false

/-! A hosted LLVM entry over the fixed synchronous storage ABI. Each effect
checks its returned status before the next call. All paths that acquired an
arena release it exactly once. Scalar operands carry integer payloads. -/
namespace VastitasKernel.LLVM.StorageModule
open MidIR.StorageEffects

structure Code where
  header : TargetHeader
  calls : List Call
  status : UInt8
  deriving DecidableEq

private def symbol (f : Callee) := "@vq_storage_" ++ f.name

private def prototype (f : Callee) :=
  "declare i32 " ++ symbol f ++ "(" ++ String.intercalate ", " ("ptr" :: List.replicate f.arity "i64") ++ ")"

private def callLine (call : Call) (i : Nat) :=
  let arguments := "ptr %arena" :: call.arguments.map (fun a => "i64 " ++ toString a)
  s!"  %status{i} = call i32 {symbol call.target}(" ++ String.intercalate ", " arguments ++ ")"

/-- The checked call sequence has one normal exit, a first-error exit, and an
allocation-failure exit. Only paths that acquired an arena own a cleanup. -/
inductive Exit where
  | immediate (status : UInt8)
  | success (status : UInt8)
  | failed
  | unavailable
  deriving DecidableEq

def Exit.releases : Exit → Bool
  | .success _ | .failed => true
  | .immediate _ | .unavailable => false

def Exit.status : Exit → UInt8
  | .success n | .immediate n => n
  | .failed | .unavailable => 1

private def Exit.lines (e : Exit) : List String :=
  (if e.releases then ["  call void @vstorage_delete(ptr %arena)"] else []) ++
    [s!"  ret i32 {e.status.toNat}"]

/-- The foreign call determines its own resulting state and status. The
modeled control flow stops at the first nonzero status. -/
def runCalls {σ : Type} (invoke : σ → Call → σ × Bool) (result : UInt8) :
    σ → List Call → List Call × Exit
  | _, [] => ([], .success result)
  | state, op :: rest =>
    match invoke state op with
    | (next, true) =>
      let (performed, exit) := runCalls invoke result next rest
      (op :: performed, exit)
    | (_, false) => ([op], .failed)

def Code.run {σ : Type} (c : Code) (arena : Option σ) (invoke : σ → Call → σ × Bool) : List Call × Exit :=
  if c.calls.isEmpty then ([], .immediate c.status) else
    match arena with
    | none => ([], .unavailable)
    | some state => runCalls invoke c.status state c.calls

private def body (c : Code) : List String :=
  if c.calls.isEmpty then ["define i32 @main() {", "entry:"] ++ (Exit.immediate c.status).lines ++ ["}"] else
    let headers := ["declare ptr @vq_storage_new(i64)", "declare void @vstorage_delete(ptr)"] ++
      (Callee.all.filter (fun f => c.calls.any (·.target == f))).map prototype
    let steps := c.calls.zipIdx.flatMap fun (op,i) =>
      [s!"next{i}:", callLine op i, s!"  %ok{i} = icmp eq i32 %status{i}, 0",
       s!"  br i1 %ok{i}, label %next{i+1}, label %failed"]
    headers ++ ["", "define i32 @main() {", "entry:",
      s!"  %arena = call ptr @vq_storage_new(i64 {Storage.byteLimit})",
      "  %created = icmp ne ptr %arena, null", "  br i1 %created, label %next0, label %unavailable"] ++
      steps ++ [s!"next{c.calls.length}:"] ++ (Exit.success c.status).lines ++
      ["failed:"] ++ Exit.failed.lines ++ ["unavailable:"] ++ Exit.unavailable.lines ++ ["}"]

def Code.print (c : Code) : List UInt8 :=
  c.header.print ++ ("\n" ++ String.intercalate "\n" (body c) ++ "\n").toUTF8.data.toList

private def readCall (line : String) : Option Call := do
  let [_, call] := line.splitOn " = call i32 @vq_storage_" | none
  let [name, args] := call.splitOn "(ptr %arena, " | none
  let f ← Callee.all.find? (·.name == name)
  let raw ← args.dropSuffix? ")"
  let arguments ← (raw.toString.splitOn ", ").mapM fun arg => do
    let word ← arg.dropPrefix? "i64 "
    word.toString.toNat?
  let op := Call.mk f arguments
  guard op.valid
  return op

private def decode (bytes : List UInt8) : Option Code := do
  guard (bytes.length ≤ 16777216)
  let (header, tail) ← TargetHeader.readPrefix (bytes.take TargetHeader.maxBytes)
  let text ← String.fromUTF8? ⟨(tail ++ bytes.drop TargetHeader.maxBytes).toArray⟩
  let lines := text.splitOn "\n"
  let calls ← (lines.filter (·.startsWith "  %status")).mapM readCall
  let exit ← lines.find? (·.startsWith "  ret i32 ")
  let token ← exit.dropPrefix? "  ret i32 "
  let value ← token.toString.toNat?
  guard (value < 256)
  return ⟨header,calls,value.toUInt8⟩

def parse (bytes : List UInt8) : Option Code :=
  match decode bytes with
  | some c => if bytes = c.print then some c else none
  | none => none

theorem parse_sound {bytes : List UInt8} {c : Code} (accepted : parse bytes = some c) :
    bytes = c.print := by
  unfold parse at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  cases accepted
  assumption

end VastitasKernel.LLVM.StorageModule
