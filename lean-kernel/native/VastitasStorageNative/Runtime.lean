/-! Minimal synchronous storage runtime. No compiler, oracle, mathlib or BLAS
dependency. Native functions validate physical preflight; initialized reads and
loan authority must come from the independently checked resource schedule. -/
namespace VastitasStorageNative

private opaque Arena.type : NonemptyType
def Arena : Type := Arena.type.type
instance : Nonempty Arena := Arena.type.property

@[extern "vastitas_storage_new"]
opaque newArena (byteBudget : UInt64) : IO Arena
@[extern "vastitas_storage_close"]
opaque close (arena : @& Arena) : IO Unit
@[extern "vastitas_storage_stats"]
opaque stats (arena : @& Arena) : IO (Array UInt64)
@[extern "vastitas_storage_allocate"]
opaque allocate (arena : @& Arena) (id : UInt32) (scalar : UInt8) (elements : UInt64) : IO Unit
@[extern "vastitas_storage_drop"]
opaque drop (arena : @& Arena) (id : UInt32) : IO Unit
@[extern "vastitas_storage_fill"]
opaque fill (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_store"]
opaque store (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (row column : UInt64) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_expect"]
opaque expect (arena : @& Arena) (id : UInt32) (offset rows columns leading : UInt64)
  (transposed : Bool) (row column : UInt64) (scalar : UInt8) (real imaginary : UInt64) : IO Unit
@[extern "vastitas_storage_copy"]
opaque copy (arena : @& Arena) (source : UInt32) (sourceOffset sourceRows sourceColumns sourceLeading : UInt64)
  (sourceTransposed : Bool) (target : UInt32) (targetOffset targetRows targetColumns targetLeading : UInt64)
  (targetTransposed : Bool) : IO Unit
@[extern "vastitas_storage_pack3"]
opaque pack3 (arena : @& Arena) (source : UInt32) (sourceOffset sourceRows sourceColumns sourceLeading : UInt64)
  (sourceTransposed : Bool) (target : UInt32) (targetOffset targetRows targetColumns targetLeading : UInt64)
  (targetTransposed : Bool) (i k j : UInt64) : IO Unit
@[extern "vastitas_storage_regroup3"]
opaque regroup3 (arena : @& Arena) (source : UInt32) (sourceOffset sourceRows sourceColumns sourceLeading : UInt64)
  (sourceTransposed : Bool) (target : UInt32) (targetOffset targetRows targetColumns targetLeading : UInt64)
  (targetTransposed : Bool) (d0 d1 d2 inputGrouping outputGrouping : UInt64) : IO Unit

end VastitasStorageNative
