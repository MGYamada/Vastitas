import VastitasKernel.LLVM.ExitMain
import VastitasKernel.LLVM.DiagonalConstant
import VastitasKernel.MidIR.StorageEffects

set_option autoImplicit false

/-! A hosted LLVM entry over the fixed synchronous storage ABI. Each effect
checks its returned status before the next call. All paths that acquired an
arena release it exactly once. Scalar operands carry integer payloads. -/
namespace VastitasKernel.LLVM.StorageModule
open MidIR.StorageEffects

structure Code where
  header : TargetHeader
  steps : List Op
  status : UInt8
  deriving DecidableEq

def Code.linear (header : TargetHeader) (calls : List Call) (status : UInt8) : Code :=
  ⟨header, calls.map Op.call, status⟩

def Code.calls (c : Code) := c.steps.filterMap Op.call?

private def symbol (f : Callee) := "@vq_storage_" ++ f.name

private def prototype (f : Callee) :=
  let tables := (List.replicate f.diagonalCount ["ptr", "i64", "i64"]).flatten
  "declare i32 " ++ symbol f ++ "(" ++ String.intercalate ", " ("ptr" :: List.replicate f.arity "i64" ++ tables) ++ ")"

private def constants (c : Code) : DiagonalConstant.Pool :=
  c.calls.foldl (fun pool call => call.diagonals.foldl (fun p d => p.add d.entries) pool) {}

private def callLine (pool : DiagonalConstant.Pool) (call : Call) (i : Nat) :=
  let arguments := "ptr %arena" :: call.arguments.map (fun a => "i64 " ++ toString a) ++
    call.diagonals.flatMap (DiagonalConstant.operands pool)
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
  if c.steps.isEmpty then ([], .immediate c.status) else
    match arena with
    | none => ([], .unavailable)
    | some state => match path c.steps.toArray with
      | some selected => runCalls invoke c.status state selected
      | none => ([], .failed)

private def body (c : Code) (pool : DiagonalConstant.Pool) : List String :=
  if c.steps.isEmpty then ["define i32 @main() {", "entry:"] ++ (Exit.immediate c.status).lines ++ ["}"] else
    let headers := ["declare ptr @vq_storage_new(i64)", "declare void @vstorage_delete(ptr)"] ++
      (Callee.all.filter (fun f => c.calls.any (·.target == f))).map prototype
    let steps := c.steps.zipIdx.flatMap fun (op,i) =>
      s!"next{i}:" :: (match op with
        | .call call => [callLine pool call i, s!"  %ok{i} = icmp eq i32 %status{i}, 0",
            s!"  br i1 %ok{i}, label %next{i+1}, label %failed"]
        | .branch condition target => [s!"  br i1 {condition}, label %next{i+1}, label %next{target}"]
        | .jump target => [s!"  br label %next{target}"])
    let globals := pool.entries.toList.zipIdx.map fun (entries,i) => DiagonalConstant.line i entries
    globals ++ headers ++ ["", "define i32 @main() {", "entry:",
      s!"  %arena = call ptr @vq_storage_new(i64 {Storage.byteLimit})",
      "  %created = icmp ne ptr %arena, null", "  br i1 %created, label %next0, label %unavailable"] ++
      steps ++ [s!"next{c.steps.length}:"] ++ (Exit.success c.status).lines ++
      ["failed:"] ++ Exit.failed.lines ++ ["unavailable:"] ++ Exit.unavailable.lines ++ ["}"]

private def bodyText (c : Code) (pool : DiagonalConstant.Pool) : String :=
  "\n" ++ String.intercalate "\n" (body c pool) ++ "\n"

def Code.print (c : Code) : List UInt8 :=
  c.header.print ++ (bodyText c (constants c)).toUTF8.data.toList

private def byteLimit := 16777216

/-- Intern the coefficient tables once. Check the payload budget before
escaping any words and the full byte budget before building the parser input. -/
def Code.render (c : Code) : Option String := do
  let pool := constants c
  guard (24 * pool.words ≤ byteLimit)
  let header ← String.fromUTF8? ⟨c.header.print.toArray⟩
  let text := bodyText c pool
  guard (header.utf8ByteSize + text.utf8ByteSize ≤ byteLimit)
  return header ++ text

private def readCall (tables : Array (List UInt64)) (line : String) : Option Call := do
  let [_, call] := line.splitOn " = call i32 @vq_storage_" | none
  let [name, args] := call.splitOn "(ptr %arena, " | none
  let f ← Callee.all.find? (·.name == name)
  let raw ← args.dropSuffix? ")"
  let tokens := raw.toString.splitOn ", "
  guard (tokens.length == f.arity + 3 * f.diagonalCount)
  let arguments ← (tokens.take f.arity).mapM fun arg => do
    let word ← arg.dropPrefix? "i64 "
    word.toString.toNat?
  let mut rest := tokens.drop f.arity
  let mut diagonals := []
  for _ in [:f.diagonalCount] do
    let ptr :: length :: uniform :: tail := rest | none
    diagonals := (← DiagonalConstant.readOperand tables ptr length uniform) :: diagonals
    rest := tail
  let op := Call.mk f arguments diagonals.reverse
  return op

private def decode (bytes : List UInt8) : Option Code := do
  guard (bytes.length ≤ byteLimit)
  let (header, tail) ← TargetHeader.readPrefix (bytes.take TargetHeader.maxBytes)
  let text ← String.fromUTF8? ⟨(tail ++ bytes.drop TargetHeader.maxBytes).toArray⟩
  let lines := text.splitOn "\n"
  let mut tables := #[]
  for line in lines do
    if line.startsWith "@vq_diag" then
      tables := tables.push (← DiagonalConstant.readLine tables.size line)
  let mut reversed := []
  for line in lines do
    if line.startsWith "  %status" then
      reversed := .call (← readCall tables line) :: reversed
    else if line.startsWith "  br i1 true," || line.startsWith "  br i1 false," then
      let [_,_,target] := line.splitOn ", label %next" | none
      guard (target.utf8ByteSize ≤ 8)
      reversed := .branch (line.startsWith "  br i1 true,") (← target.toNat?) :: reversed
    else if let some target := line.dropPrefix? "  br label %next" then
      guard (target.toString.utf8ByteSize ≤ 8)
      reversed := .jump (← target.toString.toNat?) :: reversed
  let steps : List Op := reversed.reverse
  guard (validGraph steps)
  let exit ← lines.find? (·.startsWith "  ret i32 ")
  let token ← exit.dropPrefix? "  ret i32 "
  let value ← token.toString.toNat?
  guard (value < 256)
  return ⟨header,steps,value.toUInt8⟩

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
