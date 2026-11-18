import VastitasKernel.LLVM.FiniteModuleCheck

set_option autoImplicit false

/-! Whole-byte printing and decoding of bounded finite LLVM modules. The
decoder reads LLVM instructions, named operands and actual control-flow
labels. A fresh decode and reprint binds every accepted byte. -/
namespace VastitasKernel.LLVM.FiniteModule

private def width : Width → String | .bit => "i1" | .word => "i32"
private def binaryName : Binary → String
  | .band => "and" | .bor => "or" | .add => "add" | .mul => "mul"
private def predicate : Predicate → String | .eq => "eq" | .ne => "ne" | .ult => "ult"
private def operand : Operand → String | .reg n => "%" ++ n | .literal n => toString n.toNat
private def arg (a : Arg) := width a.ty ++ " " ++ operand a.value
private def paramsText (xs : List (Width × String)) :=
  String.intercalate " , " (xs.map (fun (t,n) => width t ++ " %" ++ n))
private def parens (s : String) := if s.isEmpty then "( )" else "( " ++ s ++ " )"
private def brackets (s : String) := if s.isEmpty then "[ ]" else "[ " ++ s ++ " ]"

private def instr : Instr → String
  | .binary dst k t x y =>
    s!"  %{dst} = {binaryName k} {width t} {operand x} , {operand y}"
  | .compare dst k t x y =>
    s!"  %{dst} = icmp {predicate k} {width t} {operand x} , {operand y}"
  | .call dst t name args =>
    s!"  %{dst} = call {width t} @{name} {parens (String.intercalate " , " (args.map arg))}"
  | .phi dst t pairs =>
    let incoming := pairs.map fun (v,n) => brackets (operand v ++ " , %" ++ n)
    s!"  %{dst} = phi {width t} {String.intercalate " , " incoming}"

private def exitText : Exit → String
  | .ret a => "  ret " ++ arg a
  | .jump n => "  br label %" ++ n
  | .branch c y n => s!"  br i1 {operand c} , label %{y} , label %{n}"
  | .switch v miss cases =>
    let arms := cases.map fun (k,n) => s!"i32 {k.toNat} , label %{n}"
    s!"  switch i32 {operand v} , label %{miss} {brackets (String.intercalate " " arms)}"

private def printFn (f : Func) : String :=
  let link := if f.internal then "internal " else ""
  let start := s!"define {link}{width f.result} @{f.name} {parens (paramsText f.params)} " ++ "{"
  let lines := f.blocks.flatMap fun b => [b.label ++ ":"] ++ b.ops.map instr ++ [exitText b.exit]
  String.intercalate "\n" ([start] ++ lines ++ ["}"])

def Code.print (c : Code) : List UInt8 :=
  c.header.print ++ (("\n" ++ String.intercalate "\n\n" (c.functions.map printFn) ++ "\n").toUTF8.data.toList)

def maxBytes : Nat := 8 * 1024 * 1024

private def readWidth : String → Option Width | "i1" => some .bit | "i32" => some .word | _ => none
private def readBinary : String → Option Binary
  | "and" => some .band | "or" => some .bor | "add" => some .add | "mul" => some .mul | _ => none
private def readPredicate : String → Option Predicate
  | "eq" => some .eq | "ne" => some .ne | "ult" => some .ult | _ => none

private def name (s : String) : Option String := do
  guard (s.utf8ByteSize ≤ 64 && s.toList.head?.any Char.isAlpha &&
    s.toList.all (fun c => c.isAlphanum || c == '_'))
  return s

private def sigil (c : Char) (s : String) : Option String := do
  guard (s.startsWith (String.singleton c))
  name (s.drop 1).toString

private def number (s : String) : Option UInt32 := do
  guard (s.utf8ByteSize ≤ 10)
  let n ← s.toNat?
  guard (n < 2^32)
  return n.toUInt32

private def readOperand (s : String) : Option Operand :=
  if s.startsWith "%" then .reg <$> sigil '%' s else .literal <$> number s

private def readArg : List String → Option Arg
  | [t,v] => return ⟨← readWidth t, ← readOperand v⟩
  | _ => none

private def commaList {α : Type} (read : List String → Option α) (ts : List String) : Option (List α) :=
  if ts.isEmpty then some [] else (ts.splitOn ",").mapM read

private def close (last : String) (ts : List String) : Option (List String) := do
  guard (ts.getLast? == some last)
  return ts.dropLast

private def readIncoming (ts : List String) : Option (List (Operand × String)) :=
  go ts [] 32768
where
  go : List String → List (Operand × String) → Nat → Option (List (Operand × String))
    | ["[",v,",",n,"]"], acc, _ + 1 => do
      return ((← readOperand v, ← sigil '%' n) :: acc).reverse
    | "[" :: v :: "," :: n :: "]" :: "," :: more, acc, k+1 => do
      go more ((← readOperand v, ← sigil '%' n) :: acc) k
    | _, _, _ => none

private def readInstr (ts : List String) : Option Instr := do
  let dst :: "=" :: ts := ts | none
  let d ← sigil '%' dst
  match ts with
  | ["icmp",k,t,x,",",y] => return .compare d (← readPredicate k) (← readWidth t) (← readOperand x) (← readOperand y)
  | "call" :: t :: fn :: "(" :: more =>
    return .call d (← readWidth t) (← sigil '@' fn) (← commaList readArg (← close ")" more))
  | "phi" :: t :: more => return .phi d (← readWidth t) (← readIncoming more)
  | [k,t,x,",",y] => return .binary d (← readBinary k) (← readWidth t) (← readOperand x) (← readOperand y)
  | _ => none

private def readCases (ts : List String) : Option (List (UInt32 × String)) :=
  go ts [] 4096
where
  go : List String → List (UInt32 × String) → Nat → Option (List (UInt32 × String))
    | [], acc, _ => some acc.reverse
    | "i32" :: k :: "," :: "label" :: n :: rest, acc, fuel+1 => do
      go rest ((← number k, ← sigil '%' n) :: acc) fuel
    | _, _, _ => none

private def readExit : List String → Option Exit
  | ["ret",t,x] => return .ret (← readArg [t,x])
  | ["br","label",n] => return .jump (← sigil '%' n)
  | ["br","i1",v,",","label",yes,",","label",no] => return .branch (← readOperand v) (← sigil '%' yes) (← sigil '%' no)
  | "switch" :: "i32" :: v :: "," :: "label" :: miss :: "[" :: more =>
    return .switch (← readOperand v) (← sigil '%' miss) (← readCases (← close "]" more))
  | _ => none

private def header (ts : List String) : Option (String × Bool × Width × List (Width × String)) := do
  let "define" :: ts := ts | none
  let internal := ts.head? == some "internal"
  let t :: fn :: "(" :: more := if internal then ts.drop 1 else ts | none
  let ps ← commaList readArg (← close ")" (← close "{" more))
  let names ← ps.mapM fun a => do
    let .reg n := a.value | none
    return (a.ty,n)
  return (← sigil '@' fn, internal, ← readWidth t, names)

private def readFn (s : String) : Option Func := do
  let first :: lines := s.splitOn "\n" | none
  let (fn,internal,ret,params) ← header (first.splitOn " ")
  let mut blocks : Array Block := #[]
  let mut label : Option String := none
  let mut ops : Array Instr := #[]
  for line in ← close "}" lines do
    if line.endsWith ":" then
      guard label.isNone
      label := some (← name (line.dropEnd 1).toString)
    else
      let some labelName := label | none
      let tokens := (line.trimAsciiStart.toString).splitOn " "
      if tokens.head?.any (·.startsWith "%") then
        ops := ops.push (← readInstr tokens)
      else
        blocks := blocks.push ⟨labelName,ops.toList,← readExit tokens⟩
        label := none
        ops := #[]
  guard (label.isNone && !blocks.isEmpty)
  return ⟨fn,internal,ret,params,blocks.toList⟩

def decode (xs : List UInt8) : Option Code := do
  guard (xs.length ≤ maxBytes)
  let (target,remaining) ← TargetHeader.readPrefix (xs.take TargetHeader.maxBytes)
  let rest := remaining ++ xs.drop TargetHeader.maxBytes
  let text ← String.fromUTF8? ⟨rest.toArray⟩
  guard (text.startsWith "\n" && text.endsWith "\n")
  let body := ((text.drop 1).dropEnd 1).toString
  return ⟨target,← (body.splitOn "\n\n").mapM readFn⟩

structure Module where
  code : Code
  checked : code.valid = true
  decoded : decode code.print = some code
  deriving DecidableEq

def certify (code : Code) : Option Module :=
  if t : code.valid = true then
    if h : decode code.print = some code then some ⟨code,t,h⟩ else none
  else none

def print (m : Module) : List UInt8 := m.code.print

def parse (xs : List UInt8) : Option Module :=
  match d : decode xs with
  | none => none
  | some c =>
    if bytes : xs = c.print then
      if checked : c.valid = true then some ⟨c,checked,bytes ▸ d⟩ else none
    else none

theorem parse_iff (xs : List UInt8) (m : Module) : parse xs = some m ↔ xs = print m := by
  constructor
  · intro h
    unfold parse at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    next bytes =>
      split at h <;> try contradiction
      cases h
      exact bytes
  · rintro rfl
    rcases m with ⟨c,v,d⟩
    change parse c.print = _
    unfold parse
    split
    next h => rw [d] at h; contradiction
    next code h =>
      have same := Option.some.inj (h.symm.trans d)
      subst code
      simp [v]

end VastitasKernel.LLVM.FiniteModule
