import Std

set_option autoImplicit false

/-! Canonical LLVM quoted-byte syntax. This component is not called by the
public compiler route. It gives no target, identifier or instruction validity
to the bytes it quotes. All bytes use LLVM's two-uppercase-hex-digit escape,
so decoding is independent of the host's Unicode and string representations. -/

namespace VastitasKernel.LLVM.Bytes

def hexDigit (n : Nat) : UInt8 :=
  UInt8.ofNat (if n < 10 then 48 + n else 55 + n)

def parseHex (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48)
  else if 65 ≤ b.toNat ∧ b.toNat ≤ 70 then some (b.toNat - 55)
  else none

theorem parseHex_hexDigit (n : Nat) (h : n < 16) :
    parseHex (hexDigit n) = some n := by
  unfold hexDigit
  split <;> rename_i hn
  · have hbound : 48 + n < 256 := by omega
    simp only [parseHex, UInt8.toNat_ofNat_of_lt' hbound]
    simp only [show 48 ≤ 48 + n ∧ 48 + n ≤ 57 by omega]
    simp
  · have hbound : 55 + n < 256 := by omega
    simp only [parseHex, UInt8.toNat_ofNat_of_lt' hbound]
    simp only [show ¬(48 ≤ 55 + n ∧ 55 + n ≤ 57) by omega, ite_false,
      show 65 ≤ 55 + n ∧ 55 + n ≤ 70 by omega]
    simp

theorem parseHex_sound {b : UInt8} {n : Nat} (h : parseHex b = some n) :
    n < 16 ∧ hexDigit n = b := by
  unfold parseHex at h
  split at h
  · rename_i range
    have hn := Option.some.inj h
    constructor
    · omega
    · have hlt : n < 10 := by omega
      have heq : 48 + n = b.toNat := by omega
      simp [hexDigit, hlt, heq]
  · split at h
    · rename_i range
      have hn := Option.some.inj h
      constructor
      · omega
      · have hlt : ¬n < 10 := by omega
        have heq : 55 + n = b.toNat := by omega
        simp [hexDigit, hlt, heq]
    · contradiction

def parseByte (hi lo : UInt8) : Option UInt8 := do
  let h ← parseHex hi
  let l ← parseHex lo
  return UInt8.ofNat (h * 16 + l)

theorem parseByte_hexDigits (b : UInt8) :
    parseByte (hexDigit (b.toNat / 16)) (hexDigit (b.toNat % 16)) = some b := by
  have h := b.toNat_lt_size
  have hhi : b.toNat / 16 < 16 := by change b.toNat < 256 at h; omega
  have hlo : b.toNat % 16 < 16 := by omega
  unfold parseByte
  rw [parseHex_hexDigit _ hhi]
  change (do
    let l ← parseHex (hexDigit (b.toNat % 16))
    pure (UInt8.ofNat (b.toNat / 16 * 16 + l))) = some b
  rw [parseHex_hexDigit _ hlo]
  change some (UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16)) = some b
  have heq : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
  rw [heq, UInt8.ofNat_toNat]

theorem parseByte_sound {hi lo b : UInt8} (h : parseByte hi lo = some b) :
    hi = hexDigit (b.toNat / 16) ∧ lo = hexDigit (b.toNat % 16) := by
  unfold parseByte at h
  cases hh : parseHex hi with
  | none => simp [hh] at h
  | some nh =>
    cases hl : parseHex lo with
    | none => simp [hh, hl] at h
    | some nl =>
      rw [hh] at h
      change (do
        let l ← parseHex lo
        pure (UInt8.ofNat (nh * 16 + l))) = some b at h
      rw [hl] at h
      change some (UInt8.ofNat (nh * 16 + nl)) = some b at h
      have heq := Option.some.inj h
      obtain ⟨nhlt, nhi⟩ := parseHex_sound hh
      obtain ⟨nllt, nlo⟩ := parseHex_sound hl
      have bound : nh * 16 + nl < 256 := by omega
      have hb : b.toNat = nh * 16 + nl := by
        rw [← heq, UInt8.toNat_ofNat_of_lt' bound]
      have hdiv : b.toNat / 16 = nh := by omega
      have hmod : b.toNat % 16 = nl := by omega
      simp [hdiv, hmod, ← nhi, ← nlo]

def escape : List UInt8 → List UInt8
  | [] => []
  | b :: rest => 92 :: hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: escape rest

def quote (bytes : List UInt8) : List UInt8 := 34 :: (escape bytes ++ [34])

/-- Recursive parsing consumes the closing quote and returns the exact suffix.
Only the canonical uppercase escaped form is accepted. -/
def parseBody : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
    if b = 34 then some ([], rest)
    else if b = 92 then
      match rest with
      | hi :: lo :: tail => do
        let value ← parseByte hi lo
        let (bytes, suffix) ← parseBody tail
        return (value :: bytes, suffix)
      | _ => none
    else none

def parseQuoted : List UInt8 → Option (List UInt8 × List UInt8)
  | 34 :: rest => parseBody rest
  | _ => none

def parseQuotedComplete (input : List UInt8) : Option (List UInt8) := do
  let (bytes, suffix) ← parseQuoted input
  if suffix = [] then some bytes else none

theorem parseBody_cons (b : UInt8) (rest : List UInt8) :
    parseBody (b :: rest) =
      if b = 34 then some ([], rest)
      else if b = 92 then
        match rest with
        | hi :: lo :: tail => do
          let value ← parseByte hi lo
          let (bytes, suffix) ← parseBody tail
          pure (value :: bytes, suffix)
        | _ => none
      else none := by
  cases rest with
  | nil => rfl
  | cons hi tail => cases tail <;> rfl

theorem parseBody_sound (input bytes suffix : List UInt8)
    (h : parseBody input = some (bytes, suffix)) :
    input = escape bytes ++ 34 :: suffix := by
  cases input with
  | nil => simp [parseBody] at h
  | cons b rest =>
    rw [parseBody_cons] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [escape, hb]
    · split at h
      · rename_i hb
        cases rest with
        | nil => contradiction
        | cons hi tail =>
          cases tail with
          | nil => contradiction
          | cons lo tail =>
            cases he : parseByte hi lo with
            | none => simp [he] at h
            | some value =>
              cases hp : parseBody tail with
              | none => simp [he, hp] at h
              | some result =>
                obtain ⟨decoded, remain⟩ := result
                simp [he, hp] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hhi, hlo⟩ := parseByte_sound he
                have tail_eq := parseBody_sound tail decoded remain hp
                simp [escape, hb, hhi, hlo, tail_eq]
      · contradiction
termination_by input.length

theorem parseQuoted_sound (input bytes suffix : List UInt8)
    (h : parseQuoted input = some (bytes, suffix)) :
    input = quote bytes ++ suffix := by
  cases input with
  | nil => simp [parseQuoted] at h
  | cons b rest =>
    by_cases hb : b = 34
    · subst b
      have inner : parseBody rest = some (bytes, suffix) := by simpa [parseQuoted] using h
      rw [parseBody_sound rest bytes suffix inner]
      simp [quote, List.append_assoc]
    · simp [parseQuoted, hb] at h

theorem parseQuotedComplete_sound (input bytes : List UInt8)
    (h : parseQuotedComplete input = some bytes) : input = quote bytes := by
  unfold parseQuotedComplete at h
  cases hp : parseQuoted input with
  | none => simp [hp] at h
  | some result =>
    obtain ⟨decoded, suffix⟩ := result
    simp [hp] at h
    obtain ⟨hs, rfl⟩ := h
    subst suffix
    simpa using parseQuoted_sound input decoded [] hp

theorem parseBody_escape (bytes suffix : List UInt8) :
    parseBody (escape bytes ++ (34 :: suffix)) = some (bytes, suffix) := by
  induction bytes with
  | nil =>
    simp only [escape, List.nil_append]
    cases suffix with
    | nil => simp [parseBody]
    | cons hi tail =>
      cases tail <;> simp [parseBody]
  | cons b bytes ih => simp [escape, parseBody, parseByte_hexDigits, ih]

theorem parseQuoted_quote_suffix (bytes suffix : List UInt8) :
    parseQuoted (quote bytes ++ suffix) = some (bytes, suffix) := by
  simp [quote, parseQuoted, List.append_assoc, parseBody_escape]

theorem parseQuotedComplete_quote_suffix (bytes suffix : List UInt8) :
    parseQuotedComplete (quote bytes ++ suffix) =
      if suffix = [] then some bytes else none := by
  simp [parseQuotedComplete, parseQuoted_quote_suffix]

theorem parseQuotedComplete_quote (bytes : List UInt8) :
    parseQuotedComplete (quote bytes) = some bytes := by
  simpa using parseQuotedComplete_quote_suffix bytes []

theorem parseQuotedComplete_iff (input bytes : List UInt8) :
    parseQuotedComplete input = some bytes ↔ input = quote bytes := by
  constructor
  · exact parseQuotedComplete_sound input bytes
  · intro h
    rw [h, parseQuotedComplete_quote]

theorem quote_injective : Function.Injective quote := by
  intro a b h
  have decoded := congrArg parseQuotedComplete h
  simpa [parseQuotedComplete_quote] using decoded

theorem escape_length (bytes : List UInt8) : (escape bytes).length = 3 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b bytes ih => simp [escape, ih, Nat.mul_add, Nat.add_assoc]

theorem quote_length (bytes : List UInt8) : (quote bytes).length = 3 * bytes.length + 2 := by
  simp [quote, escape_length, Nat.add_assoc]

/-- A caller must choose a finite input bound before invoking this parser. -/
def parseQuotedBounded (limit : Nat) (input : List UInt8) : Option (List UInt8) :=
  if input.length ≤ limit then parseQuotedComplete input else none

theorem parseQuotedBounded_quote (limit : Nat) (bytes : List UInt8) :
    parseQuotedBounded limit (quote bytes) =
      if 3 * bytes.length + 2 ≤ limit then some bytes else none := by
  simp [parseQuotedBounded, quote_length, parseQuotedComplete_quote]

theorem parseQuotedBounded_sound (limit : Nat) (input bytes : List UInt8)
    (h : parseQuotedBounded limit input = some bytes) :
    input = quote bytes ∧ input.length ≤ limit := by
  unfold parseQuotedBounded at h
  split at h
  · rename_i bound
    exact ⟨parseQuotedComplete_sound input bytes h, bound⟩
  · contradiction

/-- Consume an exact literal prefix; no whitespace normalization is performed. -/
def consume : List UInt8 → List UInt8 → Option (List UInt8)
  | [], input => some input
  | _ :: _, [] => none
  | b :: literal, c :: input => if b = c then consume literal input else none

theorem consume_append (literal suffix : List UInt8) :
    consume literal (literal ++ suffix) = some suffix := by
  induction literal with
  | nil => rfl
  | cons b literal ih => simp [consume, ih]

theorem consume_sound (literal input suffix : List UInt8)
    (h : consume literal input = some suffix) : input = literal ++ suffix := by
  induction literal generalizing input with
  | nil => simpa [consume] using h
  | cons b literal ih =>
    cases input with
    | nil => simp [consume] at h
    | cons c rest =>
      simp only [consume] at h
      split at h
      · rename_i heq
        rw [ih rest h, heq]
        rfl
      · contradiction

end VastitasKernel.LLVM.Bytes
