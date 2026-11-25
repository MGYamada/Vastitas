import VastitasKernel.LLVM.Bytes
import VastitasKernel.StorageDiagonalData

set_option autoImplicit false

namespace VastitasKernel.LLVM.DiagonalConstant

/-- Number constants by their first use, independently of map traversal.
The same bits can be used in either a uniform or an explicit descriptor. -/
structure Pool where
  ids : Std.TreeMap (List UInt64) Nat := {}
  entries : Array (List UInt64) := #[]
  words : Nat := 0

def Pool.add (pool : Pool) (entries : List UInt64) : Pool :=
  if pool.ids.contains entries then pool else
    ⟨pool.ids.insert entries pool.entries.size, pool.entries.push entries, pool.words + entries.length⟩

def name (index : Nat) := "@vq_diag" ++ toString index

private def escapeWord (word : UInt64) : String :=
  let bytes := (List.range 8).map fun i => (word >>> (8*i).toUInt64).toUInt8
  String.fromUTF8! ⟨(Bytes.escape bytes).toArray⟩

def line (index : Nat) (entries : List UInt64) : String :=
  name index ++ s!" = private constant [{8 * entries.length} x i8] c\"" ++
    String.join (entries.map escapeWord) ++ "\""

def operands (pool : Pool) (d : Storage.Diagonal) : List String :=
  ["ptr " ++ name (pool.ids.getD d.entries pool.entries.size),
   "i64 " ++ toString (8 * d.entries.length), "i64 " ++ toString d.uniform.toNat]

/-- Read at most 4096 words. Each word is eight little-endian bytes encoded
as uppercase LLVM byte escapes; the host endianness is irrelevant. -/
def readLine (index : Nat) (line : String) : Option (List UInt64) := do
  let rest ← line.dropPrefix? (name index ++ " = private constant [")
  let [size, quoted] := rest.toString.splitOn " x i8] c\"" | none
  guard (size.utf8ByteSize ≤ 5)
  let size ← size.toNat?
  let payload ← quoted.dropSuffix? "\""
  let data := payload.toString.toUTF8
  guard (size ≤ 8 * 4096 && size % 8 == 0 && data.size == 3 * size)
  let mut words := []
  for i in [:size / 8] do
    let mut word : UInt64 := 0
    for j in [:8] do
      let p := 24*i + 3*j
      guard (data[p]? == some 92)
      let byte ← Bytes.parseByte (← data[p+1]?) (← data[p+2]?)
      word := word ||| (byte.toUInt64 <<< (8*j).toUInt64)
    words := word :: words
  return words.reverse

def readOperand (pool : Array (List UInt64)) (pointer length uniform : String) : Option Storage.Diagonal := do
  let id ← pointer.dropPrefix? "ptr @vq_diag"
  guard (id.toString.utf8ByteSize ≤ 8)
  let entries ← pool[← id.toString.toNat?]?
  guard (length == "i64 " ++ toString (8 * entries.length))
  let flag ← match uniform with
    | "i64 0" => some false | "i64 1" => some true | _ => none
  return ⟨flag, entries⟩

end VastitasKernel.LLVM.DiagonalConstant
