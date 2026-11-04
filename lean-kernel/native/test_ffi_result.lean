import VastitasStorageNative

@[extern "vastitas_test_result_gate"] opaque gate : IO Unit
@[extern "vastitas_test_result_probe"] opaque probe : IO Unit
@[extern "vastitas_test_result_validate"] opaque validate (expected : UInt32) : IO Unit

-- This continuation must not reset the shared Unit constructor to another value.
@[noinline] def valueAfterUnit (value : UInt64) : IO UInt64 := do
  probe
  pure (value + 1)

def main : IO Unit := do
  let tasks ← (List.range 8).mapM fun _ => IO.asTask (do
    gate
    for index in [:1000] do
      probe
      unless (← valueAfterUnit index.toUInt64) == index.toUInt64 + 1 do
        throw (IO.userError "shared Unit result changed the returned value")) Task.Priority.dedicated
  for task in tasks do
    match task.get with
    | .ok _ => pure ()
    | .error error => throw error
  let caught ← try
    try throw (IO.userError "original error") finally probe
    pure false
  catch error =>
    unless error.toString == "original error" do throw error
    pure true
  unless caught do throw (IO.userError "finally lost the error")
  validate 16001

  -- Results owning arenas remain fresh, and physical errors retain their data.
  let first ← VastitasStorageNative.newArena 8
  let second ← VastitasStorageNative.newArena 8
  let third ← VastitasStorageNative.newArena 64
  -- A failed expect names its view-relative cell and both exact payloads.
  let failsWith (action : IO Unit) (message : String) : IO Unit := do
    let failed ← try
      action
      pure false
    catch error =>
      unless error.toString == message do throw error
      pure true
    unless failed do throw (IO.userError "native error was lost")
  try
    VastitasStorageNative.allocate first 0 0 1
    VastitasStorageNative.allocate second 0 0 1
    VastitasStorageNative.allocate third 0 1 4
    VastitasStorageNative.fill first 0 0 1 1 1 false 0 4607182418800017408 0
    VastitasStorageNative.fill second 0 0 1 1 1 false 0 4611686018427387904 0
    VastitasStorageNative.expect first 0 0 1 1 1 false 0 0 0 4607182418800017408 0
    VastitasStorageNative.expect second 0 0 1 1 1 false 0 0 0 4611686018427387904 0
    failsWith (VastitasStorageNative.expect first 0 0 1 1 1 false 0 0 0 0 0)
      ("E_NATIVE_EXPECT: stored bit pattern differs at cell (0, 0): holds f64(0x1p0) " ++
        "[bits 4607182418800017408]; expected f64_bits(0)")
    -- Complex: signed zero and a NaN payload in a padded transposed view.
    VastitasStorageNative.store third 0 16 2 1 3 true 0 1 1 9223372036854775808 9221120237041090561
    VastitasStorageNative.expect third 0 16 2 1 3 true 0 1 1 9223372036854775808 9221120237041090561
    failsWith (VastitasStorageNative.expect third 0 16 2 1 3 true 0 1 1 0 9221120237041090561)
      ("E_NATIVE_EXPECT: stored bit pattern differs at cell (0, 1): holds complex(" ++
        "f64_bits(9223372036854775808), f64_bits(9221120237041090561)); expected complex(" ++
        "f64_bits(0), f64_bits(9221120237041090561))")
    failsWith (VastitasStorageNative.expect third 0 16 2 1 3 true 0 1 1 9223372036854775808 4602678819172646912)
      ("E_NATIVE_EXPECT: stored bit pattern differs at cell (0, 1): holds complex(" ++
        "f64_bits(9223372036854775808), f64_bits(9221120237041090561)); expected complex(" ++
        "f64_bits(9223372036854775808), f64(0x1p-1) [bits 4602678819172646912])")
    -- Other statuses keep their fixed messages and precedence.
    failsWith (VastitasStorageNative.expect third 0 16 2 1 3 true 1 0 1 0 0)
      "E_NATIVE_BOUNDS: cell index is outside the view"
    failsWith (VastitasStorageNative.expect third 0 16 2 1 3 true 0 1 0 0 0)
      "E_NATIVE_SCALAR: scalar representation mismatch"
  finally
    VastitasStorageNative.close first
    VastitasStorageNative.close second
    VastitasStorageNative.close third
  unless (← VastitasStorageNative.stats first)[2]! == 0 &&
      (← VastitasStorageNative.stats second)[2]! == 0 &&
      (← VastitasStorageNative.stats third)[2]! == 0 do
    throw (IO.userError "closed arena retained data")
  validate 16001
  IO.println "shared FFI Unit: concurrent first use, value continuation, error/finally and fresh arenas passed"
