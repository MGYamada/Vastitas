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
  try
    VastitasStorageNative.allocate first 0 0 1
    VastitasStorageNative.allocate second 0 0 1
    VastitasStorageNative.fill first 0 0 1 1 1 false 0 4607182418800017408 0
    VastitasStorageNative.fill second 0 0 1 1 1 false 0 4611686018427387904 0
    VastitasStorageNative.expect first 0 0 1 1 1 false 0 0 0 4607182418800017408 0
    VastitasStorageNative.expect second 0 0 1 1 1 false 0 0 0 4611686018427387904 0
    let failed ← try
      VastitasStorageNative.expect first 0 0 1 1 1 false 0 0 0 0 0
      pure false
    catch error =>
      unless error.toString == "E_NATIVE_EXPECT: stored bit pattern differs" do throw error
      pure true
    unless failed do throw (IO.userError "native error was lost")
  finally
    VastitasStorageNative.close first
    VastitasStorageNative.close second
  unless (← VastitasStorageNative.stats first)[2]! == 0 &&
      (← VastitasStorageNative.stats second)[2]! == 0 do
    throw (IO.userError "closed arena retained data")
  validate 16001
  IO.println "shared FFI Unit: concurrent first use, value continuation, error/finally and fresh arenas passed"
