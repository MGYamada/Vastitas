import VastitasKernel.LLVM.Bytes

set_option autoImplicit false

/-! Initial LLVM lexical syntax, independent of public compiler acceptance.
There are no instruction, attribute, calling-convention or semantic claims
here. In particular, lexical target text is not evidence that LLVM recognizes
the target or that its ABI matches a runtime. -/

namespace VastitasKernel.LLVM

inductive ValueType where
  | i1 | i8 | i32 | i64 | ptr
  deriving DecidableEq, Repr

namespace ValueType

def print : ValueType → List UInt8
  | .i1 => [105, 49]
  | .i8 => [105, 56]
  | .i32 => [105, 51, 50]
  | .i64 => [105, 54, 52]
  | .ptr => [112, 116, 114]

def parse : List UInt8 → Option ValueType
  | [105, 49] => some .i1
  | [105, 56] => some .i8
  | [105, 51, 50] => some .i32
  | [105, 54, 52] => some .i64
  | [112, 116, 114] => some .ptr
  | _ => none

theorem parse_print (ty : ValueType) : parse (print ty) = some ty := by
  cases ty <;> decide

end ValueType

/-- Void is a result spelling, never a first-class value type. -/
inductive ResultType where
  | void
  | value (ty : ValueType)
  deriving DecidableEq, Repr

namespace ResultType

def print : ResultType → List UInt8
  | .void => [118, 111, 105, 100]
  | .value ty => ty.print

def parse (input : List UInt8) : Option ResultType :=
  if input = [118, 111, 105, 100] then some .void
  else .value <$> ValueType.parse input

theorem parse_print (ty : ResultType) : parse (print ty) = some ty := by
  cases ty with
  | void => decide
  | value ty => cases ty <;> decide

end ResultType

inductive TargetField where
  | triple | dataLayout
  deriving DecidableEq, Repr

def targetByte (field : TargetField) (b : UInt8) : Bool :=
  let n := b.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    n == 45 || n == 46 || n == 95 || (field == .dataLayout && n == 58)

/-- A bounded, nonempty ASCII lexical atom. Actual target and layout admission
must additionally bind a qualified target machine and ABI; it is not supplied
by this predicate. -/
def TargetTextValid (field : TargetField) (bytes : List UInt8) : Prop :=
  bytes ≠ [] ∧ bytes.length ≤ 4096 ∧ bytes.all (targetByte field) = true

instance (field : TargetField) (bytes : List UInt8) : Decidable (TargetTextValid field bytes) :=
  inferInstanceAs (Decidable (bytes ≠ [] ∧ bytes.length ≤ 4096 ∧
    bytes.all (targetByte field) = true))

structure TargetText (field : TargetField) where
  bytes : List UInt8
  valid : TargetTextValid field bytes
  deriving DecidableEq

def checkTargetText (field : TargetField) (bytes : List UInt8) : Option (TargetText field) :=
  if valid : TargetTextValid field bytes then some ⟨bytes, valid⟩ else none

theorem checkTargetText_bytes {field : TargetField} (text : TargetText field) :
    checkTargetText field text.bytes = some text := by
  simp [checkTargetText, text.valid]

theorem checkTargetText_sound (field : TargetField) (bytes : List UInt8)
    (text : TargetText field) (h : checkTargetText field bytes = some text) :
    bytes = text.bytes := by
  unfold checkTargetText at h
  split at h
  · exact congrArg TargetText.bytes (Option.some.inj h)
  · contradiction

structure TargetHeader where
  triple : TargetText .triple
  dataLayout : TargetText .dataLayout
  deriving DecidableEq

namespace TargetHeader

def triplePrefix : List UInt8 := "target triple = ".toUTF8.data.toList
def layoutPrefix : List UInt8 := "\ntarget datalayout = ".toUTF8.data.toList

def print (header : TargetHeader) : List UInt8 :=
  triplePrefix ++ Bytes.quote header.triple.bytes ++ layoutPrefix ++
    Bytes.quote header.dataLayout.bytes ++ [10]

def readPrefix (input : List UInt8) : Option (TargetHeader × List UInt8) := do
  let xs ← Bytes.consume TargetHeader.triplePrefix input
  let (triple, xs) ← Bytes.parseQuoted xs
  let xs ← Bytes.consume TargetHeader.layoutPrefix xs
  let (layout, xs) ← Bytes.parseQuoted xs
  let xs ← Bytes.consume [10] xs
  return (⟨← checkTargetText .triple triple, ← checkTargetText .dataLayout layout⟩, xs)

theorem readPrefix_append (h : TargetHeader) (xs : List UInt8) :
    readPrefix (h.print ++ xs) = some (h, xs) := by
  simp [TargetHeader.print, readPrefix, List.append_assoc, Bytes.consume_append,
    Bytes.parseQuoted_quote_suffix, checkTargetText_bytes]
  rfl

/-- Consumes the entire two-line header. It grants only lexical admission. -/
def parse (input : List UInt8) : Option TargetHeader := do
  let rest ← Bytes.consume triplePrefix input
  let (triple, rest) ← Bytes.parseQuoted rest
  let rest ← Bytes.consume layoutPrefix rest
  let (layout, rest) ← Bytes.parseQuoted rest
  if rest ≠ [10] then none
  else
    let triple ← checkTargetText .triple triple
    let dataLayout ← checkTargetText .dataLayout layout
    return ⟨triple, dataLayout⟩

theorem parse_sound (input : List UInt8) (header : TargetHeader)
    (h : parse input = some header) : input = print header := by
  simp only [parse, bind, Option.bind_eq_some_iff] at h
  obtain ⟨rest0, h0, ⟨triple, rest1⟩, h1, rest2, h2, ⟨layout, rest3⟩, h3, h⟩ := h
  change Bytes.consume layoutPrefix rest1 = some rest2 at h2
  split at h
  · contradiction
  · rename_i hrest
    have rest_eq : rest3 = [10] := by simpa using hrest
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨tripleText, ht, layoutText, hl, h⟩ := h
    change some (TargetHeader.mk tripleText layoutText) = some header at h
    have header_eq := Option.some.inj h
    rw [Bytes.consume_sound _ _ _ h0, Bytes.parseQuoted_sound _ _ _ h1,
      Bytes.consume_sound _ _ _ h2, Bytes.parseQuoted_sound _ _ _ h3, rest_eq,
      checkTargetText_sound _ _ _ ht, checkTargetText_sound _ _ _ hl, ← header_eq]
    simp [print, List.append_assoc]

theorem parse_print (header : TargetHeader) : parse (print header) = some header := by
  simp [print, parse, List.append_assoc, Bytes.consume_append,
    Bytes.parseQuoted_quote_suffix, checkTargetText_bytes]

theorem parse_print_suffix (header : TargetHeader) (suffix : List UInt8) :
    parse (print header ++ suffix) = if suffix = [] then some header else none := by
  simp [print, parse, List.append_assoc, Bytes.consume_append,
    Bytes.parseQuoted_quote_suffix, checkTargetText_bytes]

theorem print_injective : Function.Injective print := by
  intro a b h
  have decoded := congrArg parse h
  simpa [parse_print] using decoded

/-- The lexical field bounds imply this complete-header byte bound. -/
def maxBytes : Nat := 24618

theorem print_length_le (header : TargetHeader) : (print header).length ≤ maxBytes := by
  have ht := header.triple.valid.2.1
  have hl := header.dataLayout.valid.2.1
  simp only [print, List.length_append, Bytes.quote_length, List.length_cons,
    List.length_nil, maxBytes]
  have htlen : triplePrefix.length = 16 := by decide
  have hllen : layoutPrefix.length = 21 := by decide
  rw [htlen, hllen]
  omega

/-- Reject overlong input before recursively parsing its escaped fields. -/
def parseBounded (input : List UInt8) : Option TargetHeader :=
  if input.length ≤ maxBytes then parse input else none

theorem parseBounded_print (header : TargetHeader) :
    parseBounded (print header) = some header := by
  simp [parseBounded, print_length_le, parse_print]

theorem parseBounded_sound (input : List UInt8) (header : TargetHeader)
    (h : parseBounded input = some header) : input = print header := by
  unfold parseBounded at h
  split at h
  · exact parse_sound input header h
  · contradiction

theorem parseBounded_iff (input : List UInt8) (header : TargetHeader) :
    parseBounded input = some header ↔ input = print header := by
  constructor
  · exact parseBounded_sound input header
  · intro h
    rw [h, parseBounded_print]

theorem parseBounded_print_suffix (header : TargetHeader) (suffix : List UInt8) :
    parseBounded (print header ++ suffix) = if suffix = [] then some header else none := by
  by_cases h : suffix = []
  · simp [h, parseBounded_print]
  · simp [parseBounded, parse_print_suffix, h]

end TargetHeader

end VastitasKernel.LLVM
