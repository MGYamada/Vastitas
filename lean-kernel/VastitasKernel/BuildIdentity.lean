import Lean.Elab.Term

/-! Build identity of the kernel executable. Protocol numbers stay fixed across
releases, so the driver compares this digest with the one it computed (in its
`build.rs`) from the same files, and rejects a checker built from other ones.

The digest covers the files that the executable is elaborated from: `Main.lean`,
the kernel modules that it imports, and `elaborationInputs`. Lake elaborates
`Main` again when its text, an option, the `.olean` of an imported module or a
target that the executable `needs` changes. A change of a source that leaves
every `.olean` as it was, such as a comment after the last declaration, does
not reach `Main` through its imports. Neither does a change of the limits file
that changes no limit of `Limits.lean`. So `lakefile.toml` names every digested
file as an input that the executable needs, by its bytes (`text = false`), and
the embedded digest cannot go stale. -/
namespace VastitasKernel.BuildIdentity

open Lean Elab Term

/-- FNV-1a, 64-bit. The driver's `build.rs` implements the same function. -/
def fnv1a (hash : UInt64) (bytes : ByteArray) : UInt64 :=
  bytes.foldl (fun hash byte => (hash ^^^ byte.toUInt64) * 1099511628211) hash

def hex16 (value : UInt64) : String :=
  let digits := Nat.toDigits 16 value.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

/-- Files beside `Main.lean`, other than Lean sources, that a module of the
executable reads while it is elaborated: `Limits.lean` reads the compiler
limits (`compiler_limit%`). The driver holds the same list (`ELABORATION_INPUTS`
in `src/runtime_inputs.rs`). -/
def elaborationInputs : List String := ["compiler-limits.json"]

/-- Digest of the file being elaborated, of every module it imports, directly
or transitively, whose source lies beside it, and of `elaborationInputs`. Each
entry is hashed in path order as `path NUL size NUL bytes`. Use it only in the
package's root-level `Main`. -/
elab "kernel_source_digest%" : term => do
  let file := System.FilePath.mk (← readThe Core.Context).fileName
  let root := file.parent.getD "."
  let some main := file.fileName | throwError "kernel_source_digest% needs a source file"
  let mut entries : Array (String × ByteArray) := #[(main, ← IO.FS.readBinFile file)]
  for name in (← getEnv).allImportedModuleNames do
    let relative := ((name.toString (escape := false)).replace "." "/") ++ ".lean"
    let path := root / relative
    if ← path.pathExists then
      entries := entries.push (relative, ← IO.FS.readBinFile path)
  for input in elaborationInputs do
    entries := entries.push (input, ← IO.FS.readBinFile (root / input))
  let mut hash : UInt64 := 14695981039346656037
  for (relative, bytes) in entries.qsort (fun left right => left.1 < right.1) do
    hash := fnv1a hash relative.toUTF8
    hash := fnv1a hash (ByteArray.mk #[0])
    hash := fnv1a hash (toString bytes.size).toUTF8
    hash := fnv1a hash (ByteArray.mk #[0])
    hash := fnv1a hash bytes
  return mkStrLit (hex16 hash)

end VastitasKernel.BuildIdentity
