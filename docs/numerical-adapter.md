# Optional native GEMM adapter

Public protocol 8 can execute real and complex GEMM from `.vast` package
`resource fn` bodies. The [public numerical path](numerical-values.md) connects
unresolved source names to independently checked nominal spaces, bases and live
map views, then to the checked resource/native schedule and OpenBLAS execution.
`lean-kernel/numerical` is its optional **internal C backend and Lean FFI package**;
the internal API is distinct from the already implemented public source entry.

## Responsibilities along the implemented path

| Layer | Responsibility | Boundary |
| --- | --- | --- |
| Public syntax and protocol 8 | The Rust frontend parses numerical statements; `ResourceProtocol` independently decodes unresolved paths, local names, modes and coefficients in Lean. | Frontend acceptance is not semantic acceptance. Public input cannot supply checked IDs, product receipts or raw resource GEMM actions. |
| Actual Lean checking | `ResourceSource` supplies the same declaration environment accepted by the full authority/Fn/dispatch checker. `StorageNumerical` checks nominal endpoints, bases and live map views; `StorageFunctions` checks every body and each actual call. `Storage.checkGemm` checks access, initialization, scalar/shape compatibility, coefficients and output separation. | Raw resource access or matching dimensions alone cannot authorize a mathematical map or metric. All-body probes remain separate from executable call checks. |
| Checked native lowering | `ResourceCodegen` and `StorageCodegen` recheck the source components, exact resource schedule and native instructions, retaining actual allocation/layout, mode, coefficients and explicit transform flags. | Only a checked entry whose schedule contains GEMM requests the optional numerical runtime. |
| Native execution | The C adapter reconstructs physical views from the live storage arena, checks layout/alias/ABI conditions before writes, and calls pinned OpenBLAS `dgemm` or `zgemm` for nondegenerate products. | It relies on the checked caller for logical initialization, permissions and nominal authority. Empty and zero-inner operations use the explicit conventions below. |

The separate `lean/` proof oracle imports the actual checker definitions and
proves structural acceptance, provenance and exact-lowering facts. Ordinary
compilation and generated programs do not invoke it. Those facts and native
regression results do not prove floating-point field laws, ideal matrix results,
certified numerical error bounds or source/native refinement; see the
[proof boundary](verification.md#what-is-outside-these-claims).

## Build and dependency boundary

For public package syntax and `vastitas check`/`build`, use
[the numerical source guide](numerical-values.md#public-source-and-build).
Checking and kernel source emission need no OpenBLAS. A native build requires
`--openblas-prefix` only when its checked entry emits GEMM; unused numerical
bodies are still checked but do not force a numerical runtime dependency.

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

Transpose and conjugation are independent input operations. Complex inputs use
N (neither), T (transpose), R (conjugation without transpose), or C (both).
The pinned OpenBLAS [CBLAS interface](https://github.com/OpenMathLib/OpenBLAS/blob/v0.3.34/cblas.h)
and [GEMM implementation](https://github.com/OpenMathLib/OpenBLAS/blob/v0.3.34/interface/gemm.c)
provide `CblasConjNoTrans` for R; the adapter passes it directly without adding a
packing buffer or copy. This is a contract with the pinned backend, not a claim
of portability to every BLAS implementation. Real conjugation is the identity,
so its two orientations remain N and T. Transposed output is still rejected.
Conjugation never swaps dimensions, changes physical byte regions, or conjugates
the explicit alpha/beta coefficients.

These raw flags do not confer mathematical dual/adjoint authority: the
[public typed caller](linear-transforms.md) independently checks derived
endpoints/bases or declared orthonormal metric evidence before selecting flags.
Complex scalars and arrays use two adjacent binary64
components; alpha/beta use the CBLAS pointer convention.

An empty output performs no matrix element access and no kernel call; explicit
coefficient views are still checked and read. For nonempty output and zero inner
dimension, the defined operation is beta*C independently of alpha, including
nonfinite alpha. Zero beta fills zero without reading C, one beta preserves C,
and other beta values scale C in place, without a BLAS call. Any preflight failure leaves output
bytes, write counters and the returned operation report unchanged. The native
BLAS routine has no recoverable partial-write result; crashes and violations of
its contract are outside this guarantee.

## Evidence and remaining obligations

Tests cover real and complex 2×3 by 3×2 products for all 16 pairs of independent
transpose/conjugation flags, with compact and padded/shifted views. An independent
small-integer reference loop checks complex results; input values and output
padding guards remain unchanged. Tests also cover T versus C on `[i]`, read
aliases, output reuse, empty shapes,
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
source integration, including explicit typed dual/conjugate operations and
adjoints for declared orthonormal metrics. The remaining public scope is listed
below.
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
post-state. `conjugation_preserves_resource_obligations` proves that changing
either explicit conjugation flag preserves the entire physical resource
predicate. `emitted_operation` connects the actual accepted request, reconstructed
views, flags and coefficients to the exact native instruction. Existing
exact-lowering and closed-exit theorems cover these actions.
It does not prove nominal map typing, ideal matrix multiplication, floating-point
results, native no-read behavior or source/native refinement.

The shared Rust/Lean fixture executes real and complex rectangular products,
overwrite into uninitialized output and accumulate in reused output. Native tests
also cover all 16 complex N/T/R/C pairs on rectangular padded views through the
actual checker, generated Lean FFI and native execution, with non-real alpha/beta
and destination reuse. They cover T versus C on `[i]`, empty output, zero inner
dimension, failure cleanup,
and header dependency rebuilding. Forged native IDs/layouts/flags/modes, unavailable
or suspended loans, wrong shapes, input/output aliases, uninitialized reads and
branch-only initialization are rejected. Numerical CI runs the actual generated
consumer on both supported operating systems; it remains separate from no-BLAS
compiler/storage jobs. Runtime counters exclude backend workspace and Lean overhead.

## Public coverage and remaining work

[PR #298](https://github.com/MGYamada/Vastitas/pull/298) connected public numerical
syntax to this checked native path.
[PR #309](https://github.com/MGYamada/Vastitas/pull/309) strengthened direct-wire
rejection regressions, including unused bodies and the raw resource-GEMM bypass.
The public checker rejects forged IDs/flags/receipts, wrong nominal objects or
bases, and stale or suspended map loans before native generation.

The implemented public scope also includes dependent numerical inputs with static
dimension contracts, initialized `OwnedMap` inputs/results preserving allocation
and layout, and explicit real/complex alpha/beta or coefficients read from
initialized scalar loans. See [the numerical contracts](numerical-values.md).
[Typed transforms](linear-transforms.md) supply explicit dual/conjugate origins,
corresponding bases and declared orthonormal metric evidence for direct adjoints;
raw component flags do not supply that authority.

`tests/numerical_source.rs` covers public source/wire checking and optional
generated execution for real/complex products, coefficients, nested inputs,
owned results and typed transforms. `tests/resource_source.rs` checks that a
raw resource GEMM with otherwise valid statement metadata is rejected by the
public action decoder. Both OS numerical CI jobs explicitly run the
OpenBLAS-dependent tests; normal compiler checks remain BLAS-free.

Generative numerical result packages, general scalar expressions and dynamic
shape interfaces, bilinear dual evaluation, Hermitian pairing execution, general
metric realization/transport, finite networks and broader scratch/dependency
handling remain work. Equivalent-C runtime, allocation/copy and peak-memory
comparisons are still required. Public GEMM execution does not complete
[#91](https://github.com/MGYamada/Vastitas/issues/91),
[#92](https://github.com/MGYamada/Vastitas/issues/92) or the full
[Stage 1 gate](stage1-completion.md), or establish **Fast like C**.
