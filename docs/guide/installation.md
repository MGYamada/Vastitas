# Installation

Vastitas needs three toolchains:

| Tool | Version | Pinned in |
| --- | --- | --- |
| Rust | 1.99.1 | [`rust-toolchain.toml`](https://github.com/MGYamada/Vastitas/blob/main/rust-toolchain.toml) |
| Lean, with Lake | 4.35.0 | [`lean-kernel/lean-toolchain`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/lean-toolchain) |
| A host C toolchain | — | On macOS, install the Xcode Command Line Tools |

Programs with numerical operations also need sequential LP64 OpenBLAS 0.3.34.
You can skip it until [Chapter 10](numerical.md).

## Build from a checkout

Clone the repository and run these commands from its root. Build the kernel
first: the driver has no fallback without it.

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
```

The kernel build also builds the native runtime that generated programs link
against. The driver is now `target/debug/vastitas`. Check it:

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
in each new shell. For programs that import the combined standard library, run
`python3 scripts/build_stdlib_package.py` once in the extracted crate.
[Numerical build guide for the alpha](https://github.com/MGYamada/Vastitas/blob/v0.1.0-alpha/docs/guide/cli.md)

## Selecting a kernel

Two environment variables select the backend for development:

- `VASTITAS_KERNEL` names a trusted backend executable. With it, `check` needs
  no kernel package directory.
- `VASTITAS_KERNEL_ROOT` names the kernel package directory. `build` needs it
  (or this checkout's default package) and copies its `lean-toolchain`, which
  must equal the compiler's pin, into the temporary project it generates.

Every kernel response carries a build identity: a digest of the kernel sources
and the Lean version. The driver rejects a kernel built from other sources with
`E_BACKEND: incompatible kernel`. After updating the compiler or its sources,
rebuild the kernel with `lake -d lean-kernel build vastitas-kernel`.

A relocatable installation and cross-compilation are not provided. The
compiler uses the built backend and runtime of one checkout or one extracted
crate. The [CLI reference](cli.md) has the details.
