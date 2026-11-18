import VastitasKernel.LLVM.ExitMain

set_option autoImplicit false

/-! One statically selected Bool method, its checked sibling bodies, and an
executable caller. The call passes the Bool unchanged. Both branches enter
the exit block and supply exactly one incoming i32 value to its phi. -/
namespace VastitasKernel.LLVM.DispatchBool

inductive Body where
  | argument
  | constant (value : Bool)
  deriving DecidableEq, Repr

def Body.eval : Body → Bool → Bool
  | .argument, b => b
  | .constant c, _ => c

structure Module where
  header : TargetHeader
  selectedPublic : Bool
  selected : Body
  siblings : List Body
  bounded : siblings.length ≤ 4096
  argument : Bool
  yes : UInt8
  no : UInt8
  deriving DecidableEq

def evaluate (m : Module) : UInt32 :=
  (if m.selected.eval m.argument then m.yes else m.no).toUInt32

private abbrev ascii (s : String) := s.toUTF8.data.toList
private def main := ascii "\ndefine i32 @main() {\nentry:\n  %choice = call i1 @vq_selected(i1 "
private def branch := ascii ")\n  br i1 %choice, label %yes, label %no\nyes:\n  br label %exit\nno:\n  br label %exit\nexit:\n  %status = phi i32 [ u0x"
private def incoming := ascii ", %yes ], [ u0x"
private def joined := ascii ", %no ]\n  ret i32 %status\n}\n"
private def defineFn := ascii "\ndefine "
private def linkage : Bool → List UInt8 | true => [] | false => ascii "internal "
private def selected := ascii "i1 @vq_selected(i1 %arg) {\nentry:\n  ret i1 "
private def sibling := ascii "\ndefine internal i1 @vq_method"
private def parameter := ascii "(i1 %arg) {\nentry:\n  ret i1 "
private def endBody := ascii "\n}\n"

private def bit : Bool → UInt8 | false => 48 | true => 49
private def boolByte : UInt8 → Option Bool
  | 48 => some false | 49 => some true | _ => none

private def hex (n : UInt8) := [Bytes.hexDigit (n.toNat / 16), Bytes.hexDigit (n.toNat % 16)]
private def symbol (i : Nat) :=
  [Bytes.hexDigit (i / 4096), Bytes.hexDigit ((i / 256) % 16),
   Bytes.hexDigit ((i / 16) % 16), Bytes.hexDigit (i % 16)]

private def printBody : Body → List UInt8
  | .argument => ascii "%arg" ++ endBody
  | .constant b => bit b :: endBody

private def others (i : Nat) : List Body → List UInt8
  | [] => []
  | b :: bs => sibling ++ symbol i ++ parameter ++ printBody b ++ others (i+1) bs

def print (m : Module) : List UInt8 :=
  m.header.print ++ main ++ [bit m.argument] ++ branch ++ hex m.yes ++ incoming ++ hex m.no ++ joined ++
    defineFn ++ linkage m.selectedPublic ++ selected ++ printBody m.selected ++ others 0 m.siblings

private def readBit (xs : List UInt8) : Option (Bool × List UInt8) := do
  let v :: rest := xs | none
  return (← boolByte v, rest)

private def readHex (xs : List UInt8) : Option (UInt8 × List UInt8) := do
  let h :: l :: rest := xs | none
  return (← Bytes.parseByte h l, rest)

private def readBody : List UInt8 → Option (Body × List UInt8)
  | 37 :: rest => do return (.argument, ← Bytes.consume (ascii "arg" ++ endBody) rest)
  | v :: rest => do return (.constant (← boolByte v), ← Bytes.consume endBody rest)
  | [] => none

private theorem readBody_append (b : Body) (xs : List UInt8) :
    readBody (printBody b ++ xs) = some (b,xs) := by
  cases b with
  | argument =>
    change (Bytes.consume (ascii "arg" ++ endBody) ((ascii "arg" ++ endBody) ++ xs) >>= _) = _
    rw [Bytes.consume_append]
    rfl
  | constant b => cases b <;> simp [printBody, bit, readBody, boolByte, Bytes.consume_append]

private def readOthers : Nat → Nat → List UInt8 → Option (List Body)
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel+1, i, a :: as => do
    let xs ← Bytes.consume (sibling ++ symbol i ++ parameter) (a :: as)
    let (b, rest) ← readBody xs
    return b :: (← readOthers fuel (i+1) rest)

private theorem readOthers_print (bs : List Body) (fuel i : Nat) (limit : bs.length ≤ fuel) :
    readOthers fuel i (others i bs) = some bs := by
  induction bs generalizing fuel i with
  | nil => simp [others,readOthers]
  | cons b bs ih =>
    cases fuel with
    | zero => simp at limit
    | succ fuel =>
      change ((Bytes.consume (sibling ++ symbol i ++ parameter)
        (((sibling ++ symbol i ++ parameter) ++ printBody b) ++ others (i+1) bs)) >>= _) = _
      rw [List.append_assoc (sibling ++ symbol i ++ parameter) (printBody b) (others (i+1) bs), Bytes.consume_append]
      simp [readBody_append, ih fuel (i+1) (by simpa using limit)]

private def readLinkage : List UInt8 → Option (Bool × List UInt8)
  | 105 :: 49 :: rest => some (true,105 :: 49 :: rest)
  | xs => do return (false, ← Bytes.consume (ascii "internal ") xs)

private theorem readLinkage_append (pub : Bool) (xs : List UInt8) :
    readLinkage (linkage pub ++ (selected ++ xs)) = some (pub,selected ++ xs) := by
  cases pub with
  | true => rfl
  | false =>
    change (Bytes.consume (ascii "internal ") ((ascii "internal ") ++ (selected ++ xs)) >>= _) = _
    rw [Bytes.consume_append]
    rfl

private def decode (bytes : List UInt8) : Option Module := do
  let (header, xs) ← TargetHeader.readPrefix bytes
  let (argument, xs) ← readBit (← Bytes.consume main xs)
  let (yes, xs) ← readHex (← Bytes.consume branch xs)
  let (no, xs) ← readHex (← Bytes.consume incoming xs)
  let (pub,xs) ← readLinkage (← Bytes.consume defineFn (← Bytes.consume joined xs))
  let xs ← Bytes.consume selected xs
  let (winner, xs) ← readBody xs
  let siblings ← readOthers 4096 0 xs
  if bounded : siblings.length ≤ 4096 then
    return ⟨header, pub, winner, siblings, bounded, argument, yes, no⟩
  else none

private theorem readBit_cons (b : Bool) (xs : List UInt8) :
    readBit (bit b :: xs) = some (b,xs) := by cases b <;> rfl

private theorem readHex_append (v : UInt8) (xs : List UInt8) :
    readHex (hex v ++ xs) = some (v,xs) := by
  simp [hex, readHex, Bytes.parseByte_hexDigits]

private theorem decode_print (m : Module) : decode (print m) = some m := by
  simp [decode, print, List.append_assoc, TargetHeader.readPrefix_append, Bytes.consume_append, readBit_cons,
    readHex_append, readLinkage_append, readBody_append, readOthers_print _ _ _ m.bounded, m.bounded]

private theorem body_length (b : Body) : (printBody b).length ≤ 7 := by
  cases b with
  | argument => decide
  | constant b => cases b <;> decide

private theorem others_length (bs : List Body) (i : Nat) : (others i bs).length ≤ 128 * bs.length := by
  induction bs generalizing i with
  | nil => simp [others]
  | cons b bs ih =>
    have tailBound := ih (i+1)
    have bodyBound := body_length b
    have overhead : sibling.length + 4 + parameter.length ≤ 121 := by decide
    simp only [others,List.length_append,symbol,List.length_cons,List.length_nil] <;> omega

private theorem print_length_le (m : Module) : (print m).length ≤ TargetHeader.maxBytes + 512 + 128*4096 := by
  have h := TargetHeader.print_length_le m.header
  have b := body_length m.selected
  have o := others_length m.siblings 0
  have s := m.bounded
  have overhead : main.length + branch.length + incoming.length + joined.length +
      defineFn.length + selected.length ≤ 480 := by decide
  have linkageLength : (linkage m.selectedPublic).length ≤ 9 := by cases m.selectedPublic <;> decide
  simp only [print,hex,List.length_append,List.length_cons,List.length_nil]
  omega

def parse (bytes : List UInt8) : Option Module := do
  guard (bytes.length ≤ TargetHeader.maxBytes + 512 + 128*4096)
  let m ← decode bytes
  guard (bytes == print m)
  return m

theorem parse_iff (bytes : List UInt8) (m : Module) : parse bytes = some m ↔ bytes = print m := by
  constructor
  · intro h
    simp only [parse, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, out, _, _, checked, result⟩ := h
    cases Option.some.inj result
    by_cases same : bytes = print m
    · exact same
    · simp [guard, same, failure] at checked
  · rintro rfl
    have within : (print m).length ≤ TargetHeader.maxBytes + 512 + 524288 := print_length_le m
    simp [parse, within, decode_print, guard]

end VastitasKernel.LLVM.DispatchBool
