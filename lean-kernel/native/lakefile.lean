import Lake
open Lake DSL System

package vastitas_storage_native where
  version := v!"0.1.0"

input_file storageHeader where path := "storage.h"
input_file storageSource where path := "storage.c"
input_file ffiSource where path := "ffi.c"
input_file diagonalSource where path := "diagonal.c"
input_file diagonalHeader where path := "diagonal.h"

target storageObject pkg : FilePath := do
  let source ← storageSource.fetch
  let header ← storageHeader.fetch
  let source ← source.bindM fun path => header.mapM fun _ => pure path
  buildO (pkg.buildDir / "storage.o") source #[] #["-std=c11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"]

target diagonalObject pkg : FilePath := do
  let source ← diagonalSource.fetch
  let headers := #[← storageHeader.fetch, ← diagonalHeader.fetch]
  let source ← source.bindM fun path => (Job.collectArray headers).mapM fun _ => pure path
  buildO (pkg.buildDir / "diagonal.o") source #[] #["-std=c11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"]

target ffiObject pkg : FilePath := do
  let source ← ffiSource.fetch
  let headers := #[← storageHeader.fetch, ← diagonalHeader.fetch]
  let source ← source.bindM fun path => (Job.collectArray headers).mapM fun _ => pure path
  buildLeanO (pkg.buildDir / "ffi.o") source #[] #["-std=c11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror"]

extern_lib storageNative pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "vastitas_storage_native")
    #[← storageObject.fetch, ← diagonalObject.fetch, ← ffiObject.fetch]

@[default_target]
lean_lib VastitasStorageNative
