# Compiler commands and diagnostics

Use `vastitas check INPUT` to validate a source and `vastitas build INPUT -o OUTPUT` to produce a native executable. Run the [quick start](getting-started.md) first or pass an explicit package manifest as described in the [package guide](stdlib.md).

`check` also accepts a library without `main`. `build` requires
`fn main() -> Int`; the generated entrypoint prints the integer and exits
successfully. Compilation never runs the generated program.

Inputs must be regular files, limited to 16 MiB each and 64 MiB / 8,192 loads per
compilation. Package closures admit at most 4,096 logical modules, including
inline modules and repeated file uses. Blocking devices and FIFOs are rejected.
Build refuses nonregular output paths and paths that alias any input source,
including an explicit library, package manifest or module file.
On macOS and Linux, SIGINT/SIGTERM/SIGHUP/SIGQUIT cancel compiler children
and remove the temporary project and staging output. Existing output is kept
until the final atomic replacement. SIGKILL or a host crash cannot run cleanup.
Ctrl-Z suspends the driver only; its separate child process group may continue.

At the pre-book revision, validation of an existing output symlink concerns
its target, while final replacement affects the link itself. The native
manifest path escaping and process-group cleanup limits are tracked
separately. Protocol 9 is supported by the kernel even though the version
banner at that revision lists protocols only through 8.
[Output links, #519](https://github.com/MGYamada/Vastitas/issues/519) · [Process cleanup, #520](https://github.com/MGYamada/Vastitas/issues/520) · [Version banner, #521](https://github.com/MGYamada/Vastitas/issues/521) · [Native manifest paths, #522](https://github.com/MGYamada/Vastitas/issues/522)

Storage and numerical builds coordinate access to their shared optional native
packages, including aliased paths. Waiting is interruptible; builds using only
the prebuilt pure runtime or independent optional packages can proceed concurrently. This
coordination adds no lock to generated programs. Keep direct `lake` builds or
package edits separate from compiler builds that use the same package artifacts.
Lake descendants inherit the package locks, so killing the driver alone does
not unlock artifacts that a surviving build still uses.

The compiler uses this checkout's built backend and runtime. A relocatable
installation and cross-compilation are not provided. The optional
`VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` environment variables select a
trusted backend executable and kernel package directory for development.
The backend build includes the native runtime. `check` needs only the executable
when explicitly selected; `build` also needs the package and uses its pinned
`lean-toolchain` for the generated project.

### Internal Lean proof audit (v0.1.0 gate)

The Rust compiler also offers an opt-in, **non-authoritative** cross-check of
Lean proof exports using the pinned [`nanoda_lib`](https://github.com/ammkrn/nanoda_lib)
crate. Generate an NDJSON file with `lean4export`, then run:

```sh
cargo run --locked -- audit-lean path/to/lean4export.ndjson
```

`audit-lean` uses the checked-in [axiom-name policy](https://github.com/MGYamada/Vastitas/blob/main/config/nanoda-internal-audit.json):
only the names `propext`, `Classical.choice`, and `Quot.sound` are allowed, with hard
rejection of all other exported axiom names. Their statements and dependencies
are not authenticated against the standard Lean environment. Every result is
explicitly conditional on the supplied environment and reports its exported
axiom count; renaming an arbitrary assumption does not validate it as a standard
Lean axiom. In particular, `sorryAx` and
`Lean.trustCompiler` are not permitted. The internal checker runs in an
isolated worker because rejection in upstream nanoda may panic or exit.

This command **rechecks an existing proof term**; it does not elaborate Lean
source, discover proofs, authorize `.vast` source/IR, or discharge any
constitutional theorem. The official Lean kernel remains the sole authority
for CI proofs, kernel compilation, and CS/MS/CF proof obligations. See
[the exact trust boundary](../verification.md#independent-internal-lean-export-audit-v010-gate)
and [v0.1.0 gate #282](https://github.com/MGYamada/Vastitas/issues/282).
