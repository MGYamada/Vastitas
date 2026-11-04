# Compiler commands and diagnostics

Use `vastitas check INPUT` to validate a source and `vastitas build INPUT -o OUTPUT` to produce a native executable. Work through [Hello, Vastitas](hello-vastitas.md) first, or pass an explicit package manifest as described in the [package guide](stdlib.md).

`check` also accepts a library without `main`. `build` requires a `main` that
returns `Int`: an ordinary `fn main() -> Int`, or in manifest mode a
`resource fn main() -> Int` with no resource inputs or owned outputs. The
generated entrypoint prints the integer and exits successfully. Compilation
never runs the generated program.

Inputs must be regular files, limited to 16 MiB each and 64 MiB / 8,192 loads per
compilation. Package closures admit at most 4,096 logical modules, including
inline modules and repeated file uses. Blocking devices and FIFOs are rejected.
Build refuses nonregular output paths and paths that alias any input source,
including an explicit library, package manifest or module file.
On macOS and Linux, SIGINT/SIGTERM/SIGHUP/SIGQUIT cancel compiler children
and remove the temporary project and staging output. Existing output is kept
until the final atomic replacement. SIGKILL or a host crash cannot run cleanup.
Ctrl-Z suspends the driver only; its separate child process group may continue.

An existing output symlink to a regular file is written through: the binary is
staged beside the link's final target and atomically replaces it, so the link
survives, and input protection compares that target. The output directory must
accept a staging file before the backend runs. The temporary Lake project is
private (mode 0700) whatever the umask. Generated Lake manifests escape paths
for TOML or Lean syntax; non-UTF-8 kernel, runtime or OpenBLAS paths are
rejected by name. Diagnostics keep the last 1 MiB of each child stream, and a
backend response may not exceed 256 MiB. Once the direct child has exited and
its process group is empty, cleanup no longer signals that group ID.
The version banner reports the package version and supported wire protocols 2–9.

Storage and numerical builds coordinate access to their shared optional native
packages, including aliased paths. Waiting is interruptible; builds using only
the prebuilt pure runtime or independent optional packages can proceed concurrently. This
coordination adds no lock to generated programs. Keep direct `lake` builds or
package edits separate from compiler builds that use the same package artifacts.
Lake descendants inherit the package locks, so killing the driver alone does
not unlock artifacts that a surviving build still uses.

`VASTITAS_KERNEL_ROOT` selects the kernel package directory. Without it, the
driver uses the `lean-kernel` directory of the source tree it was compiled
from, which is this repository's `lean-kernel` in a checkout. A driver installed
with `cargo install` has no built kernel of its own: set `VASTITAS_KERNEL_ROOT`
to the absolute path of a built kernel directory, such as the extracted crate's
`lean-kernel` in the [README's install steps](https://github.com/MGYamada/Vastitas/blob/main/README.md#install-the-alpha).
`VASTITAS_KERNEL` additionally selects a trusted backend executable for
development. `check` needs only that executable when it is selected; `build`
also needs the package and uses its pinned `lean-toolchain` for the generated
project.

`lake -d <root> build vastitas-kernel` builds the kernel executable. Generated
programs depend on the kernel package and, when their checked entry needs them,
on the storage runtime (`<root>/native`) and the numerical runtime
(`<root>/numerical`). These are separate Lake packages that the first build
needing them compiles inside the kernel root, so that directory must be
writable. There is no self-contained relocatable installation, and
cross-compilation is not provided: builds target the host.

Every backend response reports the kernel's build identity: a digest of the
kernel sources it was compiled from and its Lean version. The driver rejects a
backend built from other sources or with another Lean (`E_BACKEND: incompatible
kernel`), so rebuild the kernel (`lake -d <root> build vastitas-kernel`) after
updating the compiler or its sources. `build` also requires the package's
`lean-toolchain` to equal the compiler's pin and `lean --version`, resolved as
Lake resolves it, to report that version; otherwise it stops before Lake runs.

### Numerical builds

A program whose checked entry runs GEMM or diagonal Hermitian pairing needs the
numerical runtime and sequential LP64 OpenBLAS 0.3.34. Build OpenBLAS once into
a new, empty prefix with Python 3.12 or later, Make and a host C toolchain:

```sh
python3 scripts/build_openblas.py --prefix "$PWD/target/openblas-0.3.34" --jobs 4
```

The script downloads the OpenBLAS 0.3.34 release and verifies its SHA-256. It
builds a static, sequential, locked LP64 archive. The current script also
checks the installed profile before recording the prefix; the copy at the
`v0.1.0-alpha` tag does not. `--archive PATH` builds from an already
downloaded release archive. Then pass the prefix to `build`:

```sh
vastitas build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix "$PWD/target/openblas-0.3.34" -o target/numerical-example
```

On Linux, add `--native-cc cc` so the numerical program is compiled and linked
with the host C compiler, matching the libc that built OpenBLAS. `check`
rejects both options, and so does a build whose entry needs no numerical
runtime (`E_USAGE` in both cases). A numerical entry built without
`--openblas-prefix` fails with `E_BUILD`. The 0.1.0-alpha crate does not include
`scripts/build_openblas.py`; the README shows how to fetch it. The
[adapter contract](../linalg/maps-and-gemm.md#numerical-adapter) describes the
build profile and its checks in full.

### Internal Lean proof audit (v0.1.0 gate)

The CLI also offers an opt-in, **non-authoritative** cross-check of Lean proof
exports. It runs the external checker `nanoda_bin` that the pinned official
Lean 4.35.0 toolchain ships (nanoda 0.4.19). Vastitas does not build or bundle
a checker of its own. Generate an NDJSON file with `lean4export`, then run:

```sh
cargo run --locked -- audit-lean path/to/lean4export.ndjson
```

The command needs that toolchain installed by elan
(`elan toolchain install leanprover/lean4:v4.35.0`). It locates the toolchain
directory under `ELAN_HOME` (default `~/.elan`), never a `nanoda_bin` on `PATH`.
Before checking, it requires that the toolchain's `lean --version` reports the
official 4.35.0 release (commit `eb6cafb`) for this platform and that the
toolchain's own `nanoda_bin` reports version 0.4.19. A missing or mismatched
toolchain or checker is an `E_LEAN_AUDIT_CHECKER` error. There is no Cargo,
download or alternate-checker fallback.

`audit-lean` passes nanoda an upstream configuration file built from the
checked-in [policy](https://github.com/MGYamada/Vastitas/blob/main/config/nanoda-internal-audit.json).
Only the names `propext`, `Classical.choice`, and `Quot.sound` are allowed,
and every other exported axiom name is a hard error, including `sorryAx` and
`Lean.trustCompiler`. Their statements and dependencies are not authenticated
against the standard Lean environment, so every result is explicitly
conditional on the supplied environment. Renaming an arbitrary assumption does
not validate it as a standard Lean axiom. nanoda runs as a separate supervised
process: a rejection, panic or crash is an `E_LEAN_AUDIT` error that shows its
exit status and a bounded, escaped excerpt of its diagnostics, and an interrupt
stops and reaps it.

This command **rechecks an existing proof term**; it does not elaborate Lean
source, discover proofs, authorize `.vast` source/IR, or discharge any
constitutional theorem. nanoda is not the official Lean kernel. The official
Lean kernel remains the sole authority for CI proofs, kernel compilation, and
CS/MS/CF proof obligations. See
[the exact trust boundary](../verification.md#independent-internal-lean-export-audit-v010-gate)
and [v0.1.0 gate #282](https://github.com/MGYamada/Vastitas/issues/282).
