import VastitasKernel.LLVM.TableSwitch

set_option autoImplicit false

/-! Two independent foreign ordinals select a row in product order. Each axis
has its own unsigned bounds check before address arithmetic. This also covers
empty products and differently sized nominal Hom fibers. -/
namespace VastitasKernel.LLVM.BinaryTable
open TableSwitch (Tag ascii digits readDigits readDigits_append printCases readCases)

abbrev Width := Fin 4097

structure Module where
  header : TargetHeader
  height : Width
  width : Width
  outputs : List Tag
  rectangular : outputs.length = height.val * width.val
  bounded : outputs.length ≤ 4096
  swapped : Bool := false
  deriving DecidableEq

def atRowCol (m : Module) (row col : UInt32) : UInt32 :=
  if row < m.height.val.toUInt32 && col < m.width.val.toUInt32 then
    let i := row * m.width.val.toUInt32 + col
    ((m.outputs[i.toNat]?).map (fun t => t.val.toUInt32)).getD 0xFFFFFFFF
  else 0xFFFFFFFF

def evaluate (m : Module) (a b : UInt32) : UInt32 :=
  if m.swapped then atRowCol m b a else atRowCol m a b

private def start := ascii "\ndefine i32 @vq_lookup2(i32 %"
private def names : Bool → List UInt8
  | false => ascii "row, i32 %col"
  | true => ascii "col, i32 %row"
private def readNames (xs : List UInt8) : Option (Bool × List UInt8) := do
  let swapped := xs.head? == some 99
  return (swapped, ← Bytes.consume (names swapped) xs)

private theorem readNames_append (swapped : Bool) (rest : List UInt8) :
    readNames (names swapped ++ rest) = some (swapped, rest) := by
  have first : ((names swapped ++ rest).head? == some 99) = swapped := by cases swapped <;> rfl
  simp only [readNames, first, Bytes.consume_append]
  rfl

private def entry := ascii ") {\nentry:\n  %r = icmp ult i32 %row, u0x"
private def second := ascii "\n  %c = icmp ult i32 %col, u0x"
private def guardBlock := ascii
  "\n  %ok = and i1 %r, %c\n  br i1 %ok, label %lookup, label %miss\nlookup:\n  %base = mul i32 %row, u0x"
private def lookup := ascii "\n  %index = add i32 %base, %col\n  switch i32 %index, label %miss [\n"

def print (m : Module) : List UInt8 :=
  m.header.print ++ start ++ names m.swapped ++ entry ++ digits m.height.val ++ second ++ digits m.width.val ++
    guardBlock ++ digits m.width.val ++ lookup ++ printCases m.outputs

def maxBytes := TargetHeader.maxBytes + start.length + 13 + entry.length + second.length + guardBlock.length +
  lookup.length + 37 + 4096 * 55

private theorem bytes_bound (header maximum n pre a b c d : Nat) (h : header ≤ maximum) (bound : n ≤ 4096) :
    header + pre + 13 + a + 4 + b + 4 + c + 4 + d + (n * 55 + 25) ≤
      maximum + pre + 13 + a + b + c + d + 37 + 4096 * 55 := by omega

private def assemble (header pre names a h b w c d cases : List UInt8) :=
  header ++ pre ++ names ++ a ++ h ++ b ++ w ++ c ++ w ++ d ++ cases

private theorem assembled_bound (header pre names a h b w c d cases : List UInt8) (n : Nat)
    (headerBound : header.length ≤ TargetHeader.maxBytes)
    (nameSize : names.length = 13) (digitsH : h.length = 4) (digitsW : w.length = 4)
    (count : cases.length = n * 55 + 25) (bound : n ≤ 4096) :
    (assemble header pre names a h b w c d cases).length ≤
        TargetHeader.maxBytes + pre.length + 13 + a.length + b.length + c.length + d.length + 37 + 4096 * 55 := by
  simp only [assemble, List.length_append, nameSize, digitsH, digitsW, count]
  exact bytes_bound _ _ _ _ _ _ _ _ headerBound bound

theorem print_length_le (m : Module) : (print m).length ≤ maxBytes :=
  assembled_bound m.header.print start (names m.swapped) entry (digits m.height.val) second (digits m.width.val)
    guardBlock lookup (printCases m.outputs) m.outputs.length (TargetHeader.print_length_le m.header)
    (by cases m.swapped <;> rfl) rfl rfl (TableSwitch.printCases_length _) m.bounded

private def decode (xs : List UInt8) : Option Module := do
  let (header, xs) ← TargetHeader.readPrefix xs
  let xs ← Bytes.consume start xs
  let (swapped,xs) ← readNames xs
  let xs ← Bytes.consume entry xs
  let (h, xs) ← readDigits xs
  let xs ← Bytes.consume second xs
  let (w, xs) ← readDigits xs
  if limits : h < 4097 ∧ w < 4097 ∧ h * w ≤ 4096 then
    let xs ← Bytes.consume guardBlock xs
    let xs ← Bytes.consume (digits w) xs
    let xs ← Bytes.consume lookup xs
    let outputs ← readCases (h * w) xs
    if rect : outputs.length = h * w then
      return ⟨header, ⟨h, limits.1⟩, ⟨w, limits.2.1⟩, outputs, rect, rect ▸ limits.2.2, swapped⟩
    else none
  else none

private theorem decode_print (m : Module) : decode (print m) = some m := by
  have h := m.height.isLt
  have w := m.width.isLt
  have bound := m.bounded
  have rect := m.rectangular
  simp [decode, print, List.append_assoc, TargetHeader.readPrefix_append, Bytes.consume_append, readNames_append,
    readDigits_append _ (by omega : m.height.val < 65536),
    readDigits_append _ (by omega : m.width.val < 65536), h, w, ← rect, bound,
    TableSwitch.readCases_print _ bound]

/-- Only the exact spelling of this module is admitted, including both
comparisons, the stride, every affine case and its return value. -/
def parse (xs : List UInt8) : Option Module := do
  guard (xs.length ≤ maxBytes)
  let m ← decode xs
  if xs == print m then return m else none

theorem parse_iff (xs : List UInt8) (m : Module) : parse xs = some m ↔ xs = print m := by
  constructor
  · intro ok
    by_cases small : xs.length ≤ maxBytes
    · cases model : decode xs with
      | none => simp [parse, small, model, guard] at ok
      | some n =>
        have ⟨same, eq⟩ : xs = print n ∧ n = m := by simpa [parse, small, model, guard] using ok
        exact eq ▸ same
    · simp [parse, small, guard, failure] at ok
  · rintro rfl
    simp [parse, print_length_le, decode_print, guard]

end VastitasKernel.LLVM.BinaryTable
