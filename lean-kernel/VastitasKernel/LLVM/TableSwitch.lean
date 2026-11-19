import VastitasKernel.LLVM.Syntax

set_option autoImplicit false

/-! Complete LLVM modules for a single dense unary ordinal lookup. The
exported symbol and ABI are fixed. Case labels and edges are implicit in
their positions, so an AST cannot contain a duplicate case, a missing block,
or an out-of-range i32 constant. No general LLVM parser or optimizer. -/
namespace VastitasKernel.LLVM.TableSwitch

abbrev Tag := Fin 4096
abbrev ascii (s : String) := s.toUTF8.data.toList

structure Module where
  header : TargetHeader
  outputs : List Tag
  withinLimit : outputs.length ≤ 4096
  deriving DecidableEq

/-- ABI sentinel is outside every admitted carrier, including the empty one. -/
def evaluate (m : Module) (input : UInt32) : UInt32 :=
  match m.outputs[input.toNat]? with
  | some tag => tag.val.toUInt32
  | none => 0xFFFFFFFF

def digits (n : Nat) : List UInt8 :=
  [Bytes.hexDigit (n / 4096), Bytes.hexDigit ((n / 256) % 16),
   Bytes.hexDigit ((n / 16) % 16), Bytes.hexDigit (n % 16)]

def readDigits : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: xs => do
    return ((← Bytes.parseHex a) * 4096 + (← Bytes.parseHex b) * 256 +
      (← Bytes.parseHex c) * 16 + (← Bytes.parseHex d), xs)
  | _ => none

theorem readDigits_append (n : Nat) (small : n < 65536) (xs : List UInt8) :
    readDigits (digits n ++ xs) = some (n, xs) := by
  have a : n / 4096 < 16 := by omega
  simp only [digits, List.cons_append, List.nil_append, readDigits,
    Bytes.parseHex_hexDigit _ a, Bytes.parseHex_hexDigit _ (Nat.mod_lt _ (by decide : 0 < 16)),
    bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq, and_true]
  omega

private def introLine := ascii "\n; rows "
private def entry := ascii "\ndefine i32 @vq_lookup(i32 %tag) {\nentry:\n  switch i32 %tag, label %miss [\n"
private def miss := ascii "  ]\nmiss:\n  ret i32 -1\n"
private def finish := ascii "}\n"

private def edge (i : Nat) :=
  ascii "    i32 u0x" ++ digits i ++ ascii ", label %k" ++ digits i ++ [10]

private def edges (count : Nat) := (List.range count).flatMap edge

private def rowPrefix (i : Nat) := ascii "k" ++ digits i ++ ascii ":\n  ret i32 u0x"

private def blocks : Nat → List Tag → List UInt8
  | _, [] => []
  | i, t :: ts => rowPrefix i ++ digits t.val ++ [10] ++ blocks (i+1) ts

/-- The cases, miss block, result blocks and final closing brace. Both unary
and multidimensional ordinal lookups use this same byte representation. -/
def printCases (ts : List Tag) : List UInt8 :=
  edges ts.length ++ miss ++ blocks 0 ts ++ finish

def print (m : Module) : List UInt8 :=
  m.header.print ++ introLine ++ digits m.outputs.length ++ entry ++ edges m.outputs.length ++
    miss ++ blocks 0 m.outputs ++ finish

/-- Each case uses a fixed-width edge, block label and result literal. -/
private theorem edges_length (n : Nat) : (edges n).length = n * 30 := by
  have size (i : Nat) : (edge i).length = 30 := by rfl
  simp [edges, List.length_flatMap, size, List.map_const', List.sum_replicate_nat]

private theorem blocks_length (ts : List Tag) (i : Nat) :
    (blocks i ts).length = ts.length * 25 := by
  induction ts generalizing i with
  | nil => rfl
  | cons v vs ih =>
    have row : (rowPrefix i).length = 20 := by rfl
    simp [blocks, row, ih, digits]
    omega

theorem printCases_length (ts : List Tag) : (printCases ts).length = ts.length * 55 + 25 := by
  simp only [printCases, List.length_append, edges_length, blocks_length]
  have fixed : miss.length + finish.length = 25 := by decide
  omega

def maxBytes : Nat := TargetHeader.maxBytes + 4096 * 55 + 256

private theorem module_size (header rows a b c d : Nat)
    (hh : header ≤ TargetHeader.maxBytes) (hr : rows ≤ 4096) (fixed : a + 4 + b + c + d ≤ 256) :
    header + a + 4 + b + rows * 30 + c + rows * 25 + d ≤ maxBytes := by
  unfold maxBytes
  omega

private theorem fixed_size : introLine.length + 4 + entry.length + miss.length + finish.length ≤ 256 := by
  decide

theorem print_length_le (m : Module) : (print m).length ≤ maxBytes := by
  simp only [print, List.length_append, edges_length, blocks_length]
  exact module_size _ _ _ _ _ _ (TargetHeader.print_length_le m.header) m.withinLimit fixed_size

private def readBlocks : Nat → Nat → List UInt8 → Option (List Tag × List UInt8)
  | 0, _, xs => some ([], xs)
  | n+1, i, xs => do
    let xs ← Bytes.consume (rowPrefix i) xs
    let (v, xs) ← readDigits xs
    if small : v < 4096 then
      let xs ← Bytes.consume [10] xs
      let (vs, rest) ← readBlocks n (i+1) xs
      return (⟨v, small⟩ :: vs, rest)
    else none

private theorem readBlocks_append (ts : List Tag) (i : Nat) (suffix : List UInt8) :
    readBlocks ts.length i (blocks i ts ++ suffix) = some (ts, suffix) := by
  induction ts generalizing i with
  | nil => rfl
  | cons v vs ih =>
    have small := v.isLt
    simp [blocks, readBlocks, List.append_assoc, Bytes.consume_append,
      readDigits_append _ (by omega : v.val < 65536), small]
    change (readBlocks vs.length (i+1) (blocks (i+1) vs ++ suffix) >>= _) = _
    rw [ih]
    rfl

def readCases (count : Nat) (xs : List UInt8) : Option (List Tag) := do
  guard (count ≤ 4096)
  let xs ← Bytes.consume (edges count) xs
  let xs ← Bytes.consume miss xs
  let (ts, rest) ← readBlocks count 0 xs
  guard (rest == finish)
  return ts

theorem readCases_print (ts : List Tag) (bound : ts.length ≤ 4096) :
    readCases ts.length (printCases ts) = some ts := by
  simp [readCases, printCases, List.append_assoc, Bytes.consume_append, bound, readBlocks_append]
  rfl

private def decode (xs : List UInt8) : Option Module := do
  let (header, xs) ← TargetHeader.readPrefix xs
  let xs ← Bytes.consume introLine xs
  let (count, xs) ← readDigits xs
  guard (count ≤ 4096)
  let xs ← Bytes.consume entry xs
  let xs ← Bytes.consume (edges count) xs
  let xs ← Bytes.consume miss xs
  let (ts, rest) ← readBlocks count 0 xs
  guard (rest == finish)
  if h : ts.length ≤ 4096 then return ⟨header, ts, h⟩ else none

private theorem decode_print (m : Module) : decode (print m) = some m := by
  have small := m.withinLimit
  simp [decode, print, List.append_assoc, TargetHeader.readPrefix_append, Bytes.consume_append,
    readDigits_append _ (by omega : m.outputs.length < 65536), small, readBlocks_append]
  rfl

/-- Reprinting the decoded AST rules out noncanonical spellings, trailing
bytes, and any byte not accounted for by the model. -/
private def canonical (xs : List UInt8) : Option Module := do
  let m ← decode xs
  if xs == print m then return m else none

private theorem canonical_iff (xs : List UInt8) (m : Module) :
    canonical xs = some m ↔ xs = print m := by
  constructor
  · intro h
    cases decoded : decode xs with
    | none => simp [canonical, decoded] at h
    | some m' =>
      have ⟨same, eq⟩ : xs = print m' ∧ m' = m := by simpa [canonical, decoded] using h
      exact eq ▸ same
  · rintro rfl
    simp [canonical, decode_print]

def parse (xs : List UInt8) : Option Module :=
  if xs.length ≤ maxBytes then canonical xs else none

theorem parse_iff (xs : List UInt8) (m : Module) :
    parse xs = some m ↔ xs = print m := by
  by_cases small : xs.length ≤ maxBytes
  · simp [parse, small, canonical_iff]
  · have different : xs ≠ print m := fun same => small (same ▸ print_length_le m)
    simp [parse, small, different]

end VastitasKernel.LLVM.TableSwitch
