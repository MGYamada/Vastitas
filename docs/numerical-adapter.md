# Optional native GEMM adapter

`lean-kernel/numerical` is the optional **internal C backend** for the
typed numerical path. It uses the actual native storage arena and its independent
physical layout validation. The internal resource checker now checks GEMM access,
initialization and separation, and lowers that exact schedule through a separate
optional Lean FFI package. The [public numerical path](numerical-values.md) now
supplies nominal endpoint/basis checks through protocol 8; dual/conjugate/metric
operations and the broader contract of [#91](https://github.com/MGYamada/Vastitas/issues/91)
remain incomplete.
Neither [#92](https://github.com/MGYamada/Vastitas/issues/92) nor Stage 1 is complete.

## Build and dependency boundary

Build this optional dependency explicitly with Python 3.12+, Make and a host C
toolchain. The checked executable tests also require the pinned Lean toolchain:

```sh
python3 scripts/build_openblas.py --prefix /tmp/vastitas-openblas --jobs 4
python3 scripts/check_gemm_native.py --prefix /tmp/vastitas-openblas
```

On Linux run
`python3 scripts/check_gemm_checked.py --prefix /tmp/vastitas-openblas --lean-cc cc`.
On macOS run
`python3 scripts/check_gemm_checked.py --prefix /tmp/vastitas-openblas`.

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

Linux numerical consumers select the host compiler with Lake's `LEAN_CC=cc`
override, matching the libc used to build OpenBLAS. The regression script's
`--lean-cc cc` applies this override only to generated consumers and adds
`-L <lean-prefix>/lib` to their link arguments. This retains Lean's matching
C++ ABI and support archives instead of substituting an incompatible host
libc++ version; it does **not** add `<lean-prefix>/lib/glibc`. Lean's
[portable toolchain](https://github.com/leanprover/lean4/blob/v4.35.0/script/prepare-llvm-linux.sh)
bundles an older libc for linking and only minimal C headers, not a full C SDK.
A host-built archive can reference newer libc symbols such as `__isoc23_strtol`
that the bundled linker libraries lack.
macOS CI tests the existing bundled Lean linker against its host-built archive.
These are host-specific linked programs; no broader deployment ABI is claimed.

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

`vgemm_execute` preserves the original alpha-one/beta-zero-or-one entry.
`vgemm_execute_scaled` adds explicit binary64 coefficients and actual scalar-view
reads. Default alpha is one; default beta is zero for overwrite and one for
accumulate. Both entries use the same preflight and execution path.

| Mode | Numerical action | Required logical resource authority |
| --- | --- | --- |
| `VGEMM_OVERWRITE` | `C := alpha A B`, beta zero, no old-C dependency; an explicit beta is rejected | Exclusive write; output may be uninitialized |
| `VGEMM_ACCUMULATE` | `C := alpha A B + beta C` | Exclusive read/write; all logical output cells initialized even for beta zero |

`VGemmCoefficient` selects default, explicit scalar bits, or one scalar at a
live allocation/byte offset. Views undergo bounds/alignment/scalar and output
separation checks, then their values are read before any output mutation. They
may alias input reads and each other. Logical read rights and initialization
come from `Storage.checkCoefficient`; physical preflight does not manufacture
them. Coefficients use stack scalars, with no additional data allocation or
implicit packing/copy. The Lean FFI retains the original `gemm` entry and adds
`gemmScaled`; exact native lowering chooses the latter for explicit coefficients.

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

An empty output performs no matrix element access and no kernel call; explicit
coefficient views are still checked and read. For nonempty output and zero inner
dimension, the defined operation is beta*C independently of alpha, including
nonfinite alpha. Zero beta fills zero without reading C, one beta preserves C,
and other beta values scale C in place, without a BLAS call. Any preflight failure leaves output
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
not the discrete bit-pattern function. General scalar expressions and LAPACK
operations need separate typed contracts.

The C API trusts its caller's logical initialization and read/write rights, as
the existing native storage layer does. The checked internal path below supplies
those rights. The public path separately supplies nominal numerical types and
source integration. Finite networks, dual/metric operations and equivalent-C
GEMM performance measurements remain work.
This increment does not establish **Fast like C**; use the
[storage performance gate](storage-ownership.md#713-performance-evidence-and-acceptance).

## Checked internal resource execution

`Storage.Action.gemm` names existing loans, explicit `native_fast` policy,
`overwrite`/`accumulate` mode and explicit input conjugation flags. The strict
Rust/Lean component decoders reject missing/unknown policy and mode fields.
This component is not a public wire envelope or a mathematical map constructor.
Public resource source rejects the raw action and uses the independently checked
numerical operation instead. Raw flags cannot provide transformed endpoint,
basis or metric authority.

`Storage.checkGemm` reconstructs each loan and its allocation from the actual
state, rejects suspended parents, requires initialized readable inputs and a
writable output, and checks scalar representations, logical dimensions and the
supported native orientation. Accumulate additionally requires readable,
initialized output. Explicit input/output separation is checked even when the
same read/write handle is reused in multiple operand roles. Read inputs may
alias; disjoint views of the same allocation may use checked byte envelopes.
No allocation, packing, copy or metric selection is inserted.

A successful resource transition records exactly the output rectangle and
advances its logical version. Zero-inner overwrite initializes zeros in native
execution; zero-inner accumulate scales previously initialized output by beta. Empty
regions contain no bytes. These logical guarantees apply to successful completion;
a failed native call throws and the generated `finally` closes the arena. Earlier
completed writes are not rolled back. Native backend faults remain trusted-boundary
failures, not recoverable checked transitions.

`Storage.Native` retains the exact allocation IDs, physical views, flags, mode and
policy, and repeats original schedule/lowering comparison before generation.
GEMM plans import `VastitasGemmNative`; other plans import only the storage runtime.
The numerical Lake package depends solely on the sibling storage package and an
explicit pinned OpenBLAS prefix. The archive is a transitive native dependency,
including downstream generated executables; no system BLAS fallback is selected.
For a direct package build use
`lake -d lean-kernel/numerical -Kopenblas=/path/to/prefix build`;
on Linux set `LEAN_CC=cc` for that build and each downstream executable build,
and give the downstream package `moreLinkArgs := #["-L", "<lean-prefix>/lib"]`
using its actual `lean --print-prefix` output.
The regression consumer demonstrates a dependency-specific `openblas` Lake option.

`VastitasOracle.StorageGemm` imports the actual checker. It proves the exact
accepted transition, input initialization, accumulate's old-output requirement,
input/output byte separation and initialized output bytes in the actual logical
post-state. Existing exact-lowering and closed-exit theorems cover these actions.
It does not prove nominal map typing, ideal matrix multiplication, floating-point
results, native no-read behavior or source/native refinement.

The shared Rust/Lean fixture executes real and complex rectangular products,
overwrite into uninitialized output and accumulate in reused output. Native tests
also cover T versus C on `[i]`, empty output, zero inner dimension, failure cleanup,
and header dependency rebuilding. Forged native IDs/layouts/flags/modes, unavailable
or suspended loans, wrong shapes, input/output aliases, uninitialized reads and
branch-only initialization are rejected. Numerical CI runs the actual generated
consumer on both supported operating systems; it remains separate from no-BLAS
compiler/storage jobs. Runtime counters exclude backend workspace and Lean overhead.


The [public numerical path](numerical-values.md) now checks local nominal
spaces/bases and map views before using this adapter. Public `gemm` does not
accept the raw component flags or resource-only authority above. Use
`vastitas build --manifest-path ... --openblas-prefix /path/to/prefix -o OUTPUT`,
with `--native-cc cc` on Linux when OpenBLAS uses the host libc. Ordinary builds
and public `check` do not need OpenBLAS. Generative numerical result packages, general dynamic shape/scalar interfaces,
dual/conjugate/metric operations, networks and native refinement remain pending.
