import VastitasKernel.LLVM.Syntax

set_option autoImplicit false

/-! An argc/argv-independent hosted i32 entry point. The sole result is an
eight-bit process status zero-extended to i32; this is an entry ABI projection
of a source Int and does not specify an integer arithmetic instruction. -/
namespace VastitasKernel.LLVM.ExitMain

structure Module where
  header : TargetHeader
  status : UInt8
  deriving DecidableEq

/-- Match the public entry-point convention, Euclidean remainder modulo 256. -/
def statusOf (n : Int) : UInt8 := ((n % 256).toNat).toUInt8

theorem statusOf_exact (n : Int) : (statusOf n).toNat = (n % 256).toNat := by
  have low := Int.emod_nonneg n (by decide : (256 : Int) ≠ 0)
  have high := Int.emod_lt_of_pos n (by decide : (0 : Int) < 256)
  have bound : (n % 256).toNat < 256 := by omega
  simp [statusOf, Nat.mod_eq_of_lt bound]

def evaluate (m : Module) : UInt32 := m.status.toUInt32

private def introBytes := "\ndefine i32 @main() {\nentry:\n  ret i32 u0x".toUTF8.data.toList
private def finish := "\n}\n".toUTF8.data.toList

private def body (v : UInt8) : List UInt8 :=
  introBytes ++ [Bytes.hexDigit (v.toNat / 16), Bytes.hexDigit (v.toNat % 16)] ++ finish

def print (m : Module) := m.header.print ++ body m.status

private def bodySize := introBytes.length + 2 + finish.length

private theorem body_length (v : UInt8) : (body v).length = bodySize := by
  simp [body, bodySize]
  omega

private def decodeBody (xs : List UInt8) : Option UInt8 := do
  let hi :: lo :: rest ← Bytes.consume introBytes xs | none
  guard (rest == finish)
  Bytes.parseByte hi lo

private theorem decodeBody_print (v : UInt8) : decodeBody (body v) = some v := by
  simp [decodeBody, body, List.append_assoc, Bytes.consume_append, guard, Bytes.parseByte_hexDigits]

private def decode (xs : List UInt8) : Option Module := do
  let headerSize := xs.length - bodySize
  return ⟨← TargetHeader.parseBounded (xs.take headerSize), ← decodeBody (xs.drop headerSize)⟩

private theorem decode_print (m : Module) : decode (print m) = some m := by
  simp [decode, print, body_length, TargetHeader.parseBounded_print, decodeBody_print]

/-- Check the complete target header and return statement, including the upper
bound on size, hexadecimal spelling, whitespace and final byte. -/
def parse (xs : List UInt8) : Option Module := do
  guard (xs.length ≤ TargetHeader.maxBytes + bodySize)
  let m ← decode xs
  guard (xs == print m)
  return m

theorem parse_iff (xs : List UInt8) (m : Module) : parse xs = some m ↔ xs = print m := by
  constructor
  · intro h
    simp only [parse, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, out, _, _, comparison, result⟩ := h
    cases Option.some.inj result
    by_cases same : xs = print m
    · exact same
    · simp [guard, same, failure] at comparison
  · rintro rfl
    have round := decode_print m
    have within : (print m).length ≤ TargetHeader.maxBytes + bodySize := by
      simp [print, body_length, TargetHeader.print_length_le]
    simp [parse, within, round, guard]

end VastitasKernel.LLVM.ExitMain
