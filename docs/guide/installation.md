# Installation

Vastitas needs three toolchains:

| Tool | Version | Pinned in |
| --- | --- | --- |
| Rust | 1.99.1 | [`rust-toolchain.toml`](https://github.com/MGYamada/Vastitas/blob/main/rust-toolchain.toml) |
| Lean, with Lake | 4.35.0 | [`lean-kernel/lean-toolchain`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/lean-toolchain) |
| A host C toolchain | — | On macOS, install the Xcode Command Line Tools |

Builds of programs that run GEMM or diagonal Hermitian pairing also need
sequential LP64 OpenBLAS 0.3.34. You can skip it until
[Chapter 11](numerical.md). The optional `vastitas audit-lean` diagnostic needs
Lean 4.35.0 installed by elan and runs that toolchain's `nanoda_bin`.

## Build from a checkout

Clone the repository and run these commands from its root. Build the kernel
first: the driver has no fallback without it.

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
```

The storage and numerical runtimes are separate Lake packages under
`lean-kernel/`. The first build that needs one compiles it there, so the kernel
directory must stay writable. The driver is now `target/debug/vastitas`. Check
it:

```sh
target/debug/vastitas --version
```

It prints the package version and the supported wire protocols 2–9. You can also
run the driver through Cargo, as in `cargo run --locked -- check FILE.vast`.

## Install the alpha crate

The alpha release `0.1.0-alpha` is on crates.io. Cargo installs the driver; the
matching kernel comes from the same crate. Build it once in a writable
directory and keep that directory.

```sh
cargo install --locked --version '=0.1.0-alpha' vastitas
curl -fLsS https://static.crates.io/crates/vastitas/vastitas-0.1.0-alpha.crate -o vastitas-0.1.0-alpha.crate
tar -xzf vastitas-0.1.0-alpha.crate
cd vastitas-0.1.0-alpha
export VASTITAS_KERNEL_ROOT="$PWD/lean-kernel"
lake -d lean-kernel build vastitas-kernel
vastitas check examples/pointed.vast
vastitas build examples/pointed.vast -o pointed
./pointed
```

The example prints `42`. Set `VASTITAS_KERNEL_ROOT` to this same absolute path
in each new shell, and keep the directory writable. For programs that import
the combined standard library, run `python3 scripts/build_stdlib_package.py`
once in the extracted crate.

The 0.1.0-alpha crate does not ship `scripts/build_openblas.py`. For numerical
programs, fetch it from the release tag and follow
[Numerical builds](cli.md#numerical-builds):

```sh
curl -fLsS https://raw.githubusercontent.com/MGYamada/Vastitas/v0.1.0-alpha/scripts/build_openblas.py -o build_openblas.py
python3 build_openblas.py --prefix "$PWD/openblas-0.3.34" --jobs 4
```

## Selecting a kernel

Two environment variables select the backend:

- `VASTITAS_KERNEL_ROOT` names the kernel package directory. Without it, the
  driver uses the `lean-kernel` directory of the source tree it was compiled
  from: this repository's in a checkout. A driver installed with
  `cargo install` needs it, as in the alpha steps above. `build` copies the
  root's `lean-toolchain`, which must equal the compiler's pin, into the
  temporary project it generates.
- `VASTITAS_KERNEL` names a trusted backend executable, for development. With
  it, `check` needs no kernel package directory.

Every kernel response carries a build identity: a digest of the kernel sources
and the Lean version. The driver rejects a kernel built from other sources with
`E_BACKEND: incompatible kernel`. After updating the compiler or its sources,
rebuild the kernel with `lake -d lean-kernel build vastitas-kernel`.

There is no self-contained relocatable installation: the driver always uses
the built kernel of one checkout or one extracted crate, named by
`VASTITAS_KERNEL_ROOT` when it is not the default. Cross-compilation is not
provided. The [CLI reference](cli.md) has the details.
