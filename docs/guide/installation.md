# Installation

The compiler has two parts, and you build both. The
[*frontend*](../appendix/glossary.md#frontend) is the command `vastitas`, a
Rust program that reads your source files. The
[*kernel*](../appendix/glossary.md#kernel) is `vastitas-kernel`, a Lean program
that checks every program and generates its code. `vastitas` starts the
kernel for every check and every build, and it accepts no program without
it.

## What you need

| Tool | Version | Where the version is pinned |
| --- | --- | --- |
| Rust, with Cargo | 1.99.1 | [`rust-toolchain.toml`](https://github.com/MGYamada/Vastitas/blob/main/rust-toolchain.toml) |
| Lean, with Lake | 4.35.0 | [`lean-kernel/lean-toolchain`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/lean-toolchain) |
| A C toolchain for your machine | — | On macOS, the Xcode Command Line Tools |
| Python 3 | — | Runs the script that prepares [the standard library](stdlib.md) |

Vastitas runs on macOS and Linux. Building some numerical programs also
needs the OpenBLAS library. You can leave it until
[Chapter 11](numerical.md).

## Build from a checkout

Clone the [repository](https://github.com/MGYamada/Vastitas) and run these
commands from its root. Build the kernel first:

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
```

The first command builds the kernel inside the directory `lean-kernel`. The
second builds the frontend as `target/debug/vastitas`. Ask it for its
version:

```sh
target/debug/vastitas --version
```

It prints a line that begins with `vastitas` and the version of the
compiler. The commands
of this book call the compiler by this path, from the root of the
repository. You can also run it through Cargo, as in
`cargo run --locked -- check FILE.vast`.

Build both parts again after you update the checkout. Each kernel reports
which sources it was built from, and `vastitas` refuses a kernel that was
built from other sources than its own.

## Install the alpha crate

The alpha release `0.1.0-alpha` is on crates.io. Cargo installs the command
`vastitas`, and the same crate holds the sources of the kernel. Unpack the
crate in a directory that you keep, and build the kernel there:

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

The example prints `42`. An installed `vastitas` has no built kernel of its
own, so `VASTITAS_KERNEL_ROOT` names one. Set the variable to the same
absolute path in each shell that you open.

With this installation, write `vastitas` where the book writes
`target/debug/vastitas`, and run the commands from the unpacked directory.
The book writes its executables to the directory `target`, which the
unpacked crate lacks, so make it first with `mkdir -p target`. The alpha
release is older than this book. Of the programs of this chapter it has only
`examples/pointed.vast`, and it has neither the other programs of the book
nor the libraries of chapters 8 and 9. To follow the book, build from a
checkout.

## Selecting a kernel

Two environment variables say which kernel `vastitas` starts:

- `VASTITAS_KERNEL_ROOT` names the kernel directory. Without it, `vastitas`
  uses the `lean-kernel` directory of the sources that it was built from. In
  a checkout, that is the directory where you built the kernel, so you set
  nothing.
- `VASTITAS_KERNEL` names a kernel executable directly. It is for work on
  the compiler. With it, `check` needs no kernel directory, and `build`
  still needs one.

When `vastitas` finds no built kernel, it reports `E_BACKEND` and prints the
`lake` command that builds one.

Keep the kernel directory as it is, and keep it writable. `build` compares
its files with the files that the compiler was built from, and it rejects a
directory that differs. The first build of a program that uses storage or
numerical operations compiles a runtime library inside that directory.

There is no self-contained installation. `vastitas` always uses the built
kernel of one checkout or of one unpacked crate, which
`VASTITAS_KERNEL_ROOT` names when it is not the default. `build` produces
executables for your machine only.

## See also

- [Appendix A](cli.md): the commands, the two environment variables and the
  checks that `build` makes on the kernel directory.
- [Numerical builds](cli.md#numerical-builds): how to build OpenBLAS and
  pass it to `build`.
- [Run compiler, proof and native checks](../development/validation.md):
  the checks for a change to the compiler.
