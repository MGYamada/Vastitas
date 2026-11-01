import Lake
open Lake DSL System

def openblasPrefix : FilePath := (get_config? openblas).getD ""

package vastitas_gemm_native where
  version := v!"0.1.0"

require vastitas_storage_native from "../native"

input_file gemmHeader where path := "gemm.h"
input_file gemmSource where path := "gemm.c"
input_file ffiSource where path := "ffi.c"
input_file ffiResultHeader where path := "../native/ffi_result.h"
input_file storageHeader where path := "../native/storage.h"
input_file diagonalHeader where path := "../native/diagonal.h"
input_file cblasHeader where path := openblasPrefix / "include/cblas.h"
input_file configHeader where path := openblasPrefix / "include/openblas_config.h"
input_file blasArchive where path := openblasPrefix / "lib/libopenblas.a"

target gemmObject pkg : FilePath := do
  if openblasPrefix.toString.isEmpty then
    error "explicit pinned OpenBLAS prefix required: lake -Kopenblas=/path/to/prefix build"
  let source ← gemmSource.fetch
  let headers := #[← gemmHeader.fetch, ← storageHeader.fetch, ← diagonalHeader.fetch, ← cblasHeader.fetch,
    ← configHeader.fetch, ← blasArchive.fetch]
  let source ← source.bindM fun path => (Job.collectArray headers).mapM fun _ => pure path
  buildO (pkg.buildDir / "gemm.o") source #[]
    #["-std=c11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror",
      s!"-I{pkg.dir / "../native"}", s!"-I{openblasPrefix / "include"}"]

target ffiObject pkg : FilePath := do
  let source ← ffiSource.fetch
  let headers := #[← gemmHeader.fetch, ← storageHeader.fetch, ← diagonalHeader.fetch,
    ← ffiResultHeader.fetch]
  let source ← source.bindM fun path => (Job.collectArray headers).mapM fun _ => pure path
  buildLeanO (pkg.buildDir / "ffi.o") source #[]
    #["-std=c11", "-O3", "-fPIC", "-Wall", "-Wextra", "-Werror", s!"-I{pkg.dir / "../native"}"]

extern_lib gemmNative pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "vastitas_gemm_native")
    #[← gemmObject.fetch, ← ffiObject.fetch]

/-- Export the exact archive as a transitive native dependency. Package-local
link flags alone do not reach a downstream generated executable. -/
extern_lib pinnedOpenblas _pkg := blasArchive.fetch

@[default_target]
lean_lib VastitasGemmNative
