import VastitasKernel.LLVM.ExactFlowPrint

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExactFlow
open ExactLibrary

private abbrev PhiInputs := Std.HashMap (Nat × Nat) (Array Nat)
private abbrev Constants := Std.HashMap Nat (Std.HashMap Nat String)

private def readSlot (i : Nat) (s : String) := indexOf s (s!"%b{i}v")

private def readArg (i : Nat) (s : String) : Option Nat := do
  let [ty,arg] := s.splitOn " " | none
  guard (ty == "ptr" || ty == "i32")
  readSlot i arg

private def readPhi (i : Nat) (inputs : PhiInputs) (rhs : String) : Option PhiInputs := do
  let fields ← strip rhs (if rhs.startsWith "ptr" then "ptr [ " else "i32 [ ") " ]"
  let mut inputs := inputs
  for part in fields.splitOn " ], [ " do
    let [value,label] := part.splitOn ", %e" | none
    let [origin,target] := label.splitOn "_" | none
    let pred ← indexOf origin ""
    guard (pred < i && (← indexOf target "") == i)
    let arg ← readSlot pred value
    inputs := inputs.insert (pred,i) ((inputs.getD (pred,i) #[]).push arg)
  return inputs

private def readOp (consts : Std.HashMap Nat String) (fn i dst : Nat) (line rhs : String) : Option Op := do
  if rhs.startsWith "or i32 0, " then
    match ← strip rhs "or i32 0, " "" with
    | "0" => return .boolean false | "1" => return .boolean true | _ => none
  if rhs.startsWith "xor i32 " then
    return .boolNot (← readSlot i (← strip rhs "xor i32 " ", 1"))
  if rhs.startsWith "and i32 " || rhs.startsWith "or i32 " then
    let [a,b] := (← strip rhs (if rhs.startsWith "and " then "and i32 " else "or i32 ") "").splitOn ", " | none
    let a ← readSlot i a
    let b ← readSlot i b
    return if rhs.startsWith "and " then .boolAnd a b else .boolOr a b
  if let [ty,tail] := rhs.splitOn " @vq_f" then
    guard (ty == "call ptr" || ty == "call i32")
    let [id,args] := tail.splitOn "(" | none
    return .invoke (← indexOf id "") (← (fields (← strip args "" ")")).mapM (readArg i))
  return .exact (← readCall consts dst (line.replace (s!"%b{i}v") "%v") (constantScope fn i))

private def readBlock (c : Constants) (fn i : Nat) (s : String) (inputs : PhiInputs) :
    Option (Block × PhiInputs) := do
  let signature :: label :: lines := s.splitOn "\n" | none
  let params ← (fields (← strip signature "" ")")).mapM Kind.read
  guard (label == s!"b{i}:")
  let mut ops := #[]
  let mut comparison : Option Op := none
  let mut cond := none
  let mut inputs := inputs
  let dest := fun str => indexOf str (s!"label %e{i}_")
  for line in lines do
    if let some op := comparison then
      let dst := params.length + ops.size
      guard (line == s!"  {reg i dst} = zext i1 {cmpReg i dst} to i32")
      ops := ops.push op
      comparison := none
    else if line.startsWith "  %cmp" then
      let dst := params.length + ops.size
      guard (dst < 4096)
      let expr ← strip line (s!"  {cmpReg i dst} = icmp ") ""
      let [predicate,args] := expr.splitOn " i32 " | none
      let [left,right] := args.splitOn ", " | none
      let a ← readSlot i left
      let b ← readSlot i right
      match predicate with
      | "eq" => comparison := some (.boolEq a b)
      | "ne" => comparison := some (.boolNe a b)
      | _ => return ← none
    else if line.startsWith (s!"  %b{i}v") then
      let [lhs,rhs] := line.splitOn " = " | none
      let slot ← readSlot i (← strip lhs "  " "")
      if rhs.startsWith "phi " then
        guard (i != 0 && slot < params.length)
        inputs ← readPhi i inputs (← strip rhs "phi " "")
      else
        guard (slot == params.length + ops.size && slot < 4096)
        ops := ops.push (← readOp (c.getD i {}) fn i slot line rhs)
    else if line.startsWith "  %cond" then
      cond := some (← readSlot i (← strip line (s!"  %cond{i} = icmp ne i32 ") ", 0"))
    else if line.startsWith "  br label " then
      return (⟨params,ops.toList,.jump ⟨← dest (← strip line "  br " ""),[]⟩⟩, inputs)
    else if line.startsWith "  br i1 " then
      let [yes,no] := (← strip line (s!"  br i1 %cond{i}, ") "").splitOn ", " | none
      return (⟨params,ops.toList,.branch (← cond) ⟨← dest yes,[]⟩ ⟨← dest no,[]⟩⟩, inputs)
    else if line.startsWith "  ret " then
      return (⟨params,ops.toList,.ret (← readArg i (← strip line "  ret " ""))⟩, inputs)
  none

private def function (s : String) (fn : Nat) : Option Func := do
  let heading :: sections := s.splitOn "; block (" | none
  guard (0 < sections.length && sections.length ≤ 4096)
  let ret :: lines := heading.splitOn "\n" | none
  let result ← Kind.read ret
  let mut constants : Constants := {}
  for line in lines do
    if line.startsWith "@c" then
      let block :: _ := (← strip line (s!"@c{fn}_") "").splitOn "_" | none
      let i ← indexOf block ""
      let (slot,value) ← readGlobal line (constantScope fn i)
      constants := constants.insert i ((constants.getD i {}).insert slot value)
  let mut blocks := #[]
  let mut wires := {}
  for part in sections do
    let (b,more) ← readBlock constants fn blocks.size part wires
    blocks := blocks.push b
    wires := more
  let connected := blocks.mapIdx fun i b =>
    let attach (e : Edge) := { e with args := (wires.getD (i,e.dest) #[]).toList }
    { b with exit := match b.exit with
      | .ret r => .ret r | .jump e => .jump (attach e) | .branch r y n => .branch r (attach y) (attach n) }
  return ⟨result,connected⟩

private def decode (bytes : List UInt8) : Option Code := do
  guard (bytes.length ≤ 16777216)
  let (header,rest) ← TargetHeader.readPrefix (bytes.take TargetHeader.maxBytes)
  let text ← String.fromUTF8? ⟨(rest ++ bytes.drop TargetHeader.maxBytes).toArray⟩
  let [body,main] := text.splitOn "define i32 @main() {" | none
  let _ :: sections := body.splitOn "; flow -> " | none
  guard (sections.length ≤ 4096)
  let funcs ← sections.zipIdx.mapM fun (s,i) => function s i
  let [_,tail] := main.splitOn "  %result = call ptr @vq_f" | none
  let [entry,_] := tail.splitOn "()\n" | none
  return ⟨header,funcs.toArray,← indexOf entry ""⟩

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

end VastitasKernel.LLVM.ExactFlow
