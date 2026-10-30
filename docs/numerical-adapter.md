# Optional native GEMM adapter

`lean-kernel/numerical` is the initial **internal C backend** for the planned
typed numerical path. It uses the actual native storage arena and its independent
physical layout validation. It is not yet callable from `.vast`, protocol 8,
the logical resource checker or the Lean proof oracle. Endpoint/frame/metric
checking, checked GEMM initialization transitions and source/native lowering are
still required by [#91](https://github.com/MGYamada/Vastitas/issues/91).
Neither [#92](https://github.com/MGYamada/Vastitas/issues/92) nor Stage 1 is complete.

## Build and dependency boundary

Build this optional dependency explicitly with Python 3.12+, Make and a host C
toolchain:

```sh
python3 scripts/build_openblas.py --prefix /tmp/vastitas-openblas --jobs 4
python3 scripts/check_gemm_native.py --prefix /tmp/vastitas-openblas
```

The builder downloads the [OpenBLAS 0.3.34 release](https://github.com/OpenMathLib/OpenBLAS/releases/tag/v0.3.34)
and verifies SHA-256
`cd7e129868320cc2d033afa920e31202dfe0b8066a5b66661900ccc0f197dfed`.
`--archive path` permits an offline build of that exact archive. An existing
nonempty prefix is rejected. The profile is a host-specific static BLAS/CBLAS
archive, LP64 (signed 32-bit BLAS integers), sequential execution with locking,
no LAPACK/Fortran dependency, and no shared library. This is a build-host artifact,
not a portable prebuilt distribution. `vastitas-openblas.json` records the source
pin and build options; the prefix also contains the upstream BSD-3-Clause notice.
Redistributing linked binaries requires retaining that notice.

The ordinary compiler, checking kernel, storage-only runtime and nonnumerical
programs do not invoke this builder or link OpenBLAS. The numerical CI job is
separate from both no-mathlib compiler jobs. The adapter includes the installed
CBLAS header and checks the linked library's version, integer ABI and threading
before any GEMM. It rejects ILP64 and unsupported threaded builds; it never changes
process-wide thread settings inside an operation. LP64 and alternate integer ABIs
are distinct interfaces in the [upstream distribution contract](https://www.openmathlib.org/OpenBLAS/docs/distributing/).

Linux numerical CI selects the explicit `HASWELL`/AVX2 target for Valgrind's
[documented instruction support](https://valgrind.org/docs/manual/manual-core.html).
macOS CI uses its build host's target. This does not extend memory-check evidence
to untested CPU kernels. The builder also accepts the conservative `ARMV8` target.

## Initial operation contract

`vgemm_execute` receives arena allocation IDs and physical view descriptors.
`vstorage_prepare_dense` reconstructs each ephemeral descriptor from the actual
live allocation; no supplied pointer or claimed capacity is accepted. The
descriptor must not survive an intervening drop or concurrent arena mutation.
An arena is used synchronously by one resource operation at a time.

The initial `NativeFast` operation fixes alpha to one:

| Mode | Numerical action | Required logical authority at future integration |
| --- | --- | --- |
| `VGEMM_OVERWRITE` | `C := A B`, beta zero, no old-C dependency | Exclusive write; output may be uninitialized |
| `VGEMM_ACCUMULATE` | `C := C + A B`, beta one | Exclusive read/write; all logical output cells initialized |

The C adapter checks live handles, scalar representation, stored and logical
dimensions, offsets/alignment, leading dimensions, bounds, overflow, LP64
narrowing and conservative accessed-region overlap before writing. Inputs may
alias one another; output must be disjoint from both. Disjoint views in one
allocation are permitted only when their physical bounding byte intervals do not
overlap. Unsupported layouts are rejected; no implicit packing or alias-repair
copy is introduced. CBLAS receives column-major buffers through one direct
`dgemm` or `zgemm` call for nondegenerate compatible operands.

Transposed layouts select T without conjugation. An explicit conjugation request
with a transposed complex view selects C. Conjugation without transpose and
transposed output are rejected by this initial adapter. These flags do not confer
mathematical dual/adjoint authority: direct adjoints still need checked endpoint,
basis and orthonormal metric evidence before the future caller can select C.
Real conjugate-transpose uses T. Complex scalars and arrays use two adjacent
binary64 components; alpha/beta use the CBLAS pointer convention.

An empty output performs no element access and no kernel call. For nonempty
output and zero inner dimension, overwrite explicitly fills zero and accumulate
preserves the output without a kernel call. Any preflight failure leaves output
bytes, write counters and the returned operation report unchanged. The native
BLAS routine has no recoverable partial-write result; crashes and violations of
its contract are outside this guarantee.

## Evidence and remaining obligations

Tests cover the real and complex 2×3 by 3×2 examples, transpose combinations,
padded/shifted views, T versus C on `[i]`, read aliases, output reuse, empty shapes,
input/output alias rejection, scalar mismatch, bounds and narrowing failures.
Overwrite is exercised with genuinely uninitialized malloc-backed output and
with old NaNs. NaN/Inf inputs are accepted; no implicit finite scan occurs.
The adapter adds no data allocation or copy. Reports count calls and written
logical bytes; storage counters exclude OpenBLAS's internal workspace/packing
and allocator/Lean overhead, so they are not an end-to-end cost measurement.

ASan/UBSan cover the shim and storage runtime. Linux numerical CI additionally
uses Valgrind on the actual linked OpenBLAS machine code to detect observable
uninitialized-value use. Compile-time ILP64 rejection and simulated linked-library
version/ABI/threading mismatches exercise rejection before output mutation.
These are regression evidence, not a proof that arbitrary native implementations
never read uninitialized memory or always compute the ideal mathematical product.

The selected kernel may use FMA, blocking and its own reduction order. It does
not promise cross-backend bitwise equality, finite results, exact field laws or
a certified error bound. Mathematical smoothness concerns the ideal operation,
not the discrete bit-pattern function. Broader alpha/beta scaling and LAPACK
operations need separate typed contracts.

The adapter currently trusts its caller's logical initialization and read/write
rights, as the existing native storage layer does. Nominal numerical types,
resource-checker transitions/proofs, source integration, optional generated-program
linking, finite networks and equivalent-C performance measurements remain work.
This increment does not establish **Fast like C**; use the
[storage performance gate](storage-ownership.md#713-performance-evidence-and-acceptance).
