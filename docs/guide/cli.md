# Appendix A: CLI reference

This appendix describes the command `vastitas`: its commands and options,
what each command reads and writes, its environment, and the checks that it
makes on the kernel before it builds. [Chapter 12](diagnostics-and-cli.md)
teaches the two commands that a program needs.
[Programs](../language/programs.md) defines flat mode, manifest mode and the
entry point, and [Diagnostics](../language/diagnostics.md) gives the form of a
diagnostic and the exit status. This appendix repeats none of their rules.

## Synopsis

```text
vastitas check INPUT.vast [--lib LIBRARY.vast]...
vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT
vastitas check --manifest-path Vastitas.toml
vastitas build --manifest-path Vastitas.toml -o OUTPUT [--openblas-prefix PREFIX] [--native-cc COMPILER]
vastitas audit-lean LEAN4EXPORT.ndjson
vastitas --help
vastitas --version
```

## Commands

| Command | What it does | What it writes on success |
| --- | --- | --- |
| `check` | Checks a program. The program need not have an entry point | The line `checked INPUT` on standard output |
| `build` | Checks a program in the same way and then builds an executable from its entry point | The file `OUTPUT`, and the line `built OUTPUT` on standard output |
| `audit-lean` | Rechecks an exported Lean proof with a second checker. It checks no program. [`audit-lean`](#audit-lean) describes it | A report of four lines on standard output |
| `--help`, `-h` | Prints the usage. `vastitas` without arguments does the same, and so do `check`, `build` and `audit-lean` with `--help` or `-h` as their only argument | The usage on standard output |
| `--version` | Prints the version of the compiler and the versions of the [wire protocol](../appendix/glossary.md#wire-protocol) that it speaks | One line, such as `vastitas 0.1.0-alpha (wire protocols 2/3/4/5/6/7/8/9)` |

`--help` and `--version` read no file and start no kernel.

Rules:

- No command runs the program that it checks or builds.
- `check` and `build` accept a program only when the kernel accepts it.
  A missing kernel, a kernel that does not match the compiler and a failed
  native build are errors. No command falls back to the checks of the
  frontend alone, as [Check before generating](../language/guarantees.md#check-before-generating)
  says.
- A command that fails writes its diagnostics to standard error and nothing
  to standard output.

## Options

| Option | Commands | Meaning |
| --- | --- | --- |
| `INPUT.vast` | `check`, `build` | The entry file of [flat mode](../language/programs.md#flat-mode) |
| `--lib LIBRARY.vast` | `check`, `build` | A library of flat mode. The option may repeat |
| `--manifest-path Vastitas.toml` | `check`, `build` | The root manifest of [manifest mode](../language/programs.md#manifest-mode) |
| `-o OUTPUT` | `build` | The file of the executable. `build` requires it |
| `--openblas-prefix PREFIX` | `build` | The directory of the OpenBLAS library for a [numerical build](#numerical-builds) |
| `--native-cc COMPILER` | `build` | The C compiler and linker of a numerical build |

Rules:

- The options and the entry file may stand in any order after the command.
- A command names either one entry file or one manifest. Both, neither or a
  second entry file is an error (`E_USAGE`), and so is `--lib` with a
  manifest.
- `--manifest-path`, `-o`, `--openblas-prefix` and `--native-cc` may each
  appear once. A second one is an error (`E_USAGE`).
- The argument of an option must not begin with `-`. Write a path with such a
  name as `./-name`. The arguments of `--openblas-prefix` and `--native-cc`
  must not be empty. Otherwise it is an error (`E_USAGE`).
- `-o`, `--openblas-prefix` and `--native-cc` with `check` are errors
  (`E_USAGE`), and so are `build` without `-o`, an unknown command and an
  unknown option.
- The usage follows the `E_USAGE` of an invalid command line of `check` or
  `build`. No usage follows the `E_USAGE` of `audit-lean`, or that of a
  numerical option for a program that needs none.
- [Building a numerical program](../linalg/maps-and-gemm.md#building-a-numerical-program)
  says which programs need `--openblas-prefix` and which must not have it.

## Inputs

`check` and `build` read the entry file and the libraries of the command, or
the manifests and the source files of the packages.
[Flat mode](../language/programs.md#flat-mode),
[Manifests](../packages.md#manifests) and
[Module declarations](../language/modules.md#module-declarations) give the
rules on these files, and [Source text](../language/lexical-structure.md#source-text)
those on their text.

Rules:

- An input must be a regular file. A directory, a FIFO or a device is an
  error (`E_INPUT`). The compiler rejects such a file without reading it, so
  a FIFO does not block the command.
- The sizes and the number of the inputs have limits, which
  [Appendix D](../appendix/limits.md#inputs) gives (`E_LIMIT`). The compiler
  checks them while it reads, before it parses a file.
- The compiler reads its inputs before it starts the kernel. A file that
  changes later does not change the result of the command.

## The output of `build`

`build` writes one file, the executable `OUTPUT`. An executable prints the
value of its [entry point](../language/programs.md#the-entry-point), as that
section says.

Rules:

- `OUTPUT` must name a file. A path whose last component is empty, `.` or
  `..` is an error (`E_OUTPUT`), as in `dir/` and `dir/..`. A name that ends
  in a dot, such as `prog.`, names a file.
- The directory of `OUTPUT` must exist (`E_OUTPUT`). The compiler creates no
  directory.
- An existing `OUTPUT` must be a regular file or a symbolic link to one.
  A directory, a FIFO or a device is an error (`E_OUTPUT`), and the compiler
  leaves it as it is.
- `OUTPUT` must not be an input of the command: the entry file, a library, a
  manifest or a source file of a package. The rule holds for another name of
  such a file too, such as a symbolic link or a hard link to it. Otherwise it
  is an error (`E_OUTPUT`).
- The compiler checks the first three rules before it reads an input. It
  compares each input with `OUTPUT` when it reads the input, before it
  parses that input, and all inputs once more before it writes `OUTPUT`.
- Before it reads an input, the compiler also tests that the directory of
  `OUTPUT` accepts a file (`E_OUTPUT`). Where `OUTPUT` is a symbolic link,
  the directory is that of the file that the link names.
- A `build` that fails leaves an existing `OUTPUT` as it was. A `build` that
  succeeds replaces it in one step: no reader sees a file that is partly
  written.
- Where `OUTPUT` is a symbolic link to a regular file, `build` replaces that
  file and keeps the link. The rule on inputs then holds for the file that
  the link names.
- The file has the permissions of the executable that the native build
  produces, whatever the permissions of the file that it replaces.

> **Implementation note.** The compiler copies the executable to a
> [staging file](../appendix/glossary.md#staging-file) next to its final
> place and renames that file onto `OUTPUT`. The staging file has the name
> `.vastitas-PID-N.tmp`, where `PID` is the process number of the compiler
> and `N` a number that the compiler counts up. The compiler removes the
> staging file when the command fails. A symbolic link that changes during
> the build is an error (`E_OUTPUT`).

## Exit status

[Exit status](../language/diagnostics.md#exit-status) gives the statuses of
`check` and `build`. `audit-lean` has the same three: 0 when the audit
completes, 1 when it fails, and 128 plus the number of the signal when a
signal interrupts it.

## Environment

| Variable | Commands | Meaning |
| --- | --- | --- |
| `VASTITAS_KERNEL_ROOT` | `check`, `build` | The [kernel root](#the-kernel-and-its-build-identity) |
| `VASTITAS_KERNEL` | `check`, `build` | The kernel executable. The variable serves work on the compiler |
| `PATH` | `build` | Where `build` finds `lean`, `lake` and, for a runtime, `cc` |
| `TMPDIR` | `build`, `audit-lean` | The directory in which the command makes its [temporary directory](#temporary-files) |
| `ELAN_HOME`, `HOME` | `audit-lean` | Where `audit-lean` finds the pinned Lean toolchain |

`build` starts `lean` and `lake` with the environment of the command. A
variable that selects another Lean toolchain, such as `ELAN_TOOLCHAIN`,
therefore changes which `lean` they find, and `build` rejects a `lean` of
another version, as [What `check` and `build` start](#what-check-and-build-start)
says. `--native-cc` sets `LEAN_CC` for `lake`. The compiler reads no
configuration file.

## The kernel and its build identity

The **kernel root** is the directory of the kernel package. It holds the
sources of the [kernel](../appendix/glossary.md#kernel) and its built
executable. It also holds two packages that an executable can need: the
**storage runtime**, in the directory `native`, and the **numerical
runtime**, in the directory `numerical`.
[What `check` and `build` start](#what-check-and-build-start) says which
programs need them, and [Installation](installation.md) shows how to build
the kernel.

Rules:

- `VASTITAS_KERNEL_ROOT` names the kernel root. Without the variable, the
  kernel root is the directory `lean-kernel` of the sources from which the
  compiler was built. In a checkout, that is the `lean-kernel` of the
  checkout.
- The kernel executable is the file `.lake/build/bin/vastitas-kernel` in the
  kernel root, unless `VASTITAS_KERNEL` names another file.
- `check` with `VASTITAS_KERNEL` needs no kernel root. `build` needs one in
  every case.
- A kernel root that does not exist, a kernel executable that is not built
  and a kernel that does not start are errors (`E_BACKEND`). So are an answer
  that neither accepts nor rejects the program, and a kernel that fails after
  it accepts the program. The diagnostic for a kernel that is not built gives
  the `lake` command that builds it.
- A compiler that `cargo install` installed has no built kernel of its own.
  Set `VASTITAS_KERNEL_ROOT` to the kernel root of the unpacked crate, as
  [Install the alpha crate](installation.md#install-the-alpha-crate) shows.

The **build identity** of a kernel executable names what it was built from: a
digest of its Lean sources and of the file of
[limits](../appendix/limits.md#sources-of-the-values), and the version of
Lean.

Rules:

- Every answer of the kernel states its build identity. `check` and `build`
  accept an answer only from a kernel whose build identity is the one that
  the compiler expects. Another kernel is an error (`E_BACKEND`), even when
  it accepts the program. The diagnostic says `incompatible kernel` and gives
  both identities. For a kernel that states no build identity, it says so
  and gives none.
- When a kernel of another build identity rejects a program, the compiler
  shows its diagnostics and adds a note. The note says that they may come
  from a stale or foreign kernel.
- Build the kernel again after a change of the compiler or of its sources:
  `lake -d ROOT build vastitas-kernel`, where `ROOT` is the kernel root.
- An answer that the compiler cannot read is an error (`E_PROTOCOL`). So are
  a kernel that writes no answer, a rejection without a diagnostic, and an
  answer of another version of the wire protocol that does not reject the
  program. When a kernel rejects a program with an answer of another version,
  the compiler shows its diagnostics and adds a note.

> **Implementation note.** The digest is a 64-bit FNV-1a hash of `Main.lean`,
> of the kernel modules that it imports and of `compiler-limits.json`. The
> compiler computes the expected identity from its own copy of these files
> when it is built. The digest detects a stale or mixed tree. It is not a
> cryptographic hash and does not authenticate a kernel.

## What `check` and `build` start

`check` starts one program, the kernel executable. `build` starts the kernel
executable and then the Lean toolchain, which compiles the program that the
kernel generates.

| Command | Programs that it starts | Where it finds them |
| --- | --- | --- |
| `check` | The kernel executable | The kernel root, or `VASTITAS_KERNEL` |
| `build` | The kernel executable, `lean` and `lake` | The kernel root or `VASTITAS_KERNEL`, and `PATH` |
| `build` of a program that needs a runtime, when the runtime is not yet compiled | Also `cc`, the C compiler of the machine | `PATH` |

Rules:

- `check` needs no Lean toolchain and no C compiler. With an empty `PATH`,
  `check` succeeds.
- `build` needs `lean` and `lake` on `PATH`. With an empty `PATH`, `build` is
  an error (`E_BUILD`), even for a program that `check` accepts.
- The Lean toolchain compiles and links the generated program with the C
  compiler that it holds. For a program that needs no runtime, `build`
  starts no other compiler from `PATH`.
- A generated program depends on the kernel package. It needs the storage
  runtime when its entry point is a resource function with an operation on
  an allocation or on
  [runtime extents](../storage/resource-programs.md#runtime-extents). A
  resource entry point that computes scalars alone does not need it.
- A generated program needs the numerical runtime when its entry point
  reaches a [product statement](../appendix/glossary.md#product-statement).
  It then needs the storage runtime too.
- The first `build` that needs a runtime compiles it inside the kernel root,
  so that directory must be writable. This build compiles the C sources of
  the runtime with the command `cc`, apart from the file `ffi.c` of each
  runtime, which the C compiler of the Lean toolchain compiles. Later builds
  use the compiled runtime.
- `build` requires the file `lean-toolchain` of the kernel root to name the
  toolchain that the compiler was built for. It then asks `lean --version`,
  found as `lake` finds it, and requires the version of that toolchain. A
  missing or empty file, another toolchain or another version is an error
  (`E_BUILD`), which `build` reports before `lake` runs.
- A failed native build is an error (`E_BUILD`). The output of `lake` follows
  the diagnostic.
- `build` produces an executable for the machine on which it runs. The
  compiler has no cross-compilation and no installation that is independent
  of a kernel root.

## Checks on the kernel root

The build identity covers the kernel executable. `lake` compiles the
generated program against the files of the kernel root, and these can differ
from the files that the kernel executable was built from. `build` therefore
compares the files that `lake` reads there with the files that the compiler
was built from:

- in the kernel package, the runtime modules that a generated program
  imports and the modules that those import, `lakefile.toml`,
  `lake-manifest.json` and `compiler-limits.json`;
- in the storage runtime and in the numerical runtime, when the program
  needs them, the Lake configuration, `lake-manifest.json`,
  `lean-toolchain`, the Lean modules and the C sources and headers.

Rules:

- A kernel root whose files differ from those of the compiler is an error
  (`E_BUILD`). `build` reports it before `lake` runs and before it writes
  `OUTPUT`. The diagnostic names up to six files that differ, says for each
  whether it is changed, missing or unexpected, and gives a digest of each
  side.
- Each of the three packages has one Lake configuration file. The other name
  of that file must not exist in a package that `build` compares:
  `lakefile.lean` in the kernel package, and `lakefile.toml` in the two
  runtimes. Such a file is an error (`E_BUILD`). In the kernel package,
  `lake` prefers `lakefile.lean`, so such a file would replace the
  configuration that `build` compares. In the two runtimes, the rule keeps
  the configuration of each package in one file.
- `build` compares the kernel package for every program. It compares the
  storage runtime only for a program that needs it, and the numerical
  runtime only for a numerical build. A file of the other name in a runtime
  that the build does not compare is no error of that build.
- A generated program that imports another module than a runtime module of
  the packages that the build compares is an error (`E_PROTOCOL`).
- The path of the kernel root must be valid UTF-8 (`E_BUILD`), and so must
  the paths of the Lean installation and of the OpenBLAS directory.

The comparison rejects a kernel root whose runtime files changed after its
kernel executable was built. It also rejects a `VASTITAS_KERNEL` executable
with the kernel root of another source tree. Both pass the check of the build
identity. The comparison reads source files. It does not cover the build
products under `.lake`, the OpenBLAS directory or a file that changes while
`lake` runs.

> **Implementation note.** Building the compiler fails when its own sources
> lack one of the compared files or hold a file with a forbidden name. The
> compiler compares the name of a forbidden file by rule, not with a recorded
> value, so building the compiler again does not make such a file acceptable.

## Temporary files

`build` writes the generated program and its Lake project to a temporary
directory. `audit-lean` writes the configuration of its checker to one.

Rules:

- The command makes the directory in the temporary directory of the system,
  which `TMPDIR` names, with the name `vastitas-PID-N`. `PID` and `N` are
  the two numbers of the name of the staging file. Only the user of the
  command can enter it, whatever the file mode mask of the process.
- The command removes the directory when it ends, also when it fails or a
  signal interrupts it.

> **Implementation note.** The generated project holds the program that the
> kernel generated, a copy of the file `lean-toolchain` of the kernel root
> and a Lake configuration that names the kernel root. No identifier of the
> source program becomes code in the generated program. The compiler writes
> each path into the configuration as a string of TOML or of Lean and
> escapes the characters that the syntax requires.

## Signals

On macOS and Linux, the signals `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT`
interrupt a command.

Rules:

- A command that fails after a signal arrived exits with status 128 plus
  the number of the signal: 130 for `SIGINT`, 143 for `SIGTERM`, 129 for
  `SIGHUP` and 131 for `SIGQUIT`.
- An interrupted `check` or `build` reports `E_INTERRUPTED`. A command that
  finds another error before it notices the signal reports that error, with
  the exit status of the signal.
- The compiler passes the signal to the programs that it started and waits
  for them to end. It ends a program that does not end within a second.
- The compiler removes its temporary directory and its staging file. An
  existing `OUTPUT` stays as it was.
- `SIGKILL` and a crash of the machine leave no time for this. A temporary
  directory or a staging file can then remain.
- Suspending the command from the terminal, with Ctrl-Z, suspends the
  compiler only. The programs that it started can continue.

> **Implementation note.** Each program that the compiler starts runs in a
> process group of its own, and the compiler signals that group. Once the
> program has ended and its group is empty, the compiler does not signal the
> number of the group again, because another group can have it by then. A
> program that ends while a process that it started still runs in its group,
> with or without the output of the program, is an error of the command: the
> compiler ends that process after a quarter of a second.

## Concurrent builds

Several `build` commands can run at once, also with one kernel root.

Rules:

- Builds of programs that need no runtime run side by side. They read the
  built kernel package and write only their own temporary directories.
- A build that needs the storage runtime takes a lock on that package for the
  time of its native build, and a build that needs the numerical runtime
  takes one on both packages. A second such build waits. A signal interrupts
  the wait (`E_INTERRUPTED`).
- The locks follow the files, not the names: two paths to one package share a
  lock, and two kernel roots have separate locks.
- The lock adds nothing to a generated program.
- Keep a direct `lake` build in the kernel root, and an edit of its packages,
  apart from a `build` that uses the same kernel root. The lock covers the
  commands of the compiler only.

> **Implementation note.** The lock is an advisory lock on the directory of
> the package. On a file system that cannot lock a directory, the compiler
> locks the file `.vastitas-build.lock` in it. `lake` and the processes that
> it starts inherit the lock, so the lock holds as long as one of them runs,
> even after the compiler itself is killed.

## Output of the tools

The compiler bounds what it keeps of the output of the programs that it
starts. A mebibyte, MiB, is 1,048,576 bytes, and a kibibyte, KiB, is 1024
bytes.

| Output | Bound | Beyond it |
| --- | --- | --- |
| The answer of the kernel | 256 MiB | An error (`E_BACKEND`) |
| The answer of `lean --version` and of `lean --print-prefix` | 64 KiB | An error (`E_BUILD`) |
| Standard error of each program, and the output of `lake` | The last 1 MiB | The compiler shows the last 1 MiB after a line that gives the number of bytes that it left out |
| The answers of the toolchain to `audit-lean`: the version of `lean`, the help text of `nanoda_bin` and the report of a success | 64 KiB | An error (`E_LEAN_AUDIT`) |
| The report of the checker of `audit-lean` for a failure | 2000 characters | The compiler shows the first 2000 characters |

The compiler writes the output of `lake` after `E_BUILD` as `lake` gives it.
[Names and text in diagnostics](../language/diagnostics.md#names-and-text-in-diagnostics)
says how the compiler writes paths and names.

## Numerical builds

A **numerical build** is a `build` of a program whose entry point reaches a
[product statement](../appendix/glossary.md#product-statement). Such a
program needs the numerical runtime and the library OpenBLAS.
[Building a numerical program](../linalg/maps-and-gemm.md#building-a-numerical-program)
lists the product statements and gives the rules on `--openblas-prefix` and
`--native-cc`. This section describes the library and the two options.

The library is OpenBLAS 0.3.34, built as a static library without threads,
with locking and with 32-bit integers in its interface: the sequential,
locked LP64 build. Build it
once into an empty directory, the prefix, with Python 3.12 or later, Make and
the C compiler of the machine:

```sh
python3 scripts/build_openblas.py --prefix "$PWD/target/openblas-0.3.34" --jobs 4
```

The script downloads the release of OpenBLAS 0.3.34 and compares its SHA-256
with the pinned value. It builds the library, checks the profile of the
library that it installed and then writes a record of the build into the
prefix. Its options:

| Option | Meaning |
| --- | --- |
| `--prefix PREFIX` | The directory of the installation. The script refuses a directory that is not empty |
| `--jobs N` | The number of parallel jobs of Make. Without the option, 2 |
| `--archive PATH` | A release archive that is already downloaded. The script checks its SHA-256 too |
| `--target HASWELL` or `--target ARMV8` | The processor profile of the library. Without the option, the script takes the profile of the machine |

Pass the prefix to `build`:

```sh
target/debug/vastitas build --manifest-path examples/packages/numerical/Vastitas.toml \
  --openblas-prefix "$PWD/target/openblas-0.3.34" -o target/numerical-example
```

Rules:

- `--openblas-prefix` must name a directory that exists (`E_BUILD`). `build`
  links the file `lib/libopenblas.a` of the prefix and reads the headers in
  its directory `include`.
- `--native-cc COMPILER` makes `lake` compile and link the generated program
  with `COMPILER`. On Linux, pass `--native-cc cc`, so that the program links
  with the C library that built OpenBLAS.
- A numerical executable checks the library when it runs. A library of
  another version, with threads, without locking or with 64-bit integers
  stops the executable
  with a [run-time diagnostic](../language/diagnostics.md#run-time-diagnostics)
  (`E_NATIVE_ABI`).
- `check` needs neither the library nor the numerical runtime.

The script at the tag `v0.1.0-alpha` does not check the installed profile,
and the crate of that release does not hold the script. The
[README](https://github.com/MGYamada/Vastitas/blob/main/README.md#install-the-alpha)
shows how to fetch it.
[Native GEMM adapter](../internals/numerical-backend.md#native-gemm-adapter)
describes the build profile and the checks of the adapter.

## `audit-lean`

`vastitas audit-lean LEAN4EXPORT.ndjson` rechecks the proof terms of a Lean
export with `nanoda_bin`, a checker that is independent of the Lean kernel.
The command serves the review of the proofs of this repository. It checks no
Vastitas program, and its result is no acceptance of one.

```sh
cargo run --locked -- audit-lean path/to/lean4export.ndjson
```

The export is a file in the format of `lean4export`. The checker is the
`nanoda_bin` 0.4.19 that the official Lean 4.35.0 toolchain holds. Install
that toolchain with elan:

```sh
elan toolchain install leanprover/lean4:v4.35.0
```

Rules:

- The command takes one argument, the export. Another number of arguments is
  an error (`E_USAGE`), and so is a path of the export that is not valid
  UTF-8.
- The command finds the toolchain in the directory of elan, which `ELAN_HOME`
  names and which is `.elan` in the home directory without the variable. It
  never uses a `nanoda_bin` or a `lean` from `PATH`.
- Before it checks, the command requires that `lean --version` of the
  toolchain reports the official 4.35.0 release for the platform, with the
  commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. It requires that
  `nanoda_bin` of the toolchain reports version 0.4.19. A missing toolchain,
  a missing checker or another version is an error
  (`E_LEAN_AUDIT_CHECKER`). The command downloads nothing and has no other
  checker.
- The command gives the checker a configuration from the
  [policy file](https://github.com/MGYamada/Vastitas/blob/main/config/nanoda-internal-audit.json)
  of the repository. The policy permits the axiom names `propext`,
  `Classical.choice` and `Quot.sound`. Any other axiom name in the export
  makes the checker fail, including `sorryAx` and `Lean.trustCompiler`. A
  policy that the command cannot use is an error (`E_LEAN_AUDIT_POLICY`).
- An export that the command cannot read, that the checker rejects or that
  holds no declaration is an error (`E_LEAN_AUDIT`). So is a checker that
  crashes or that writes to standard error. The diagnostic shows the exit
  status of the checker and the first 2000 characters of its report, with
  control characters written as escapes.
- The checker runs as a separate program. A signal stops it, and the command
  then reports `E_LEAN_AUDIT` and exits with 128 plus the number of the
  signal.

A completed audit states the limits of its result on standard output. The
result holds for the environment of the export only. The checker admits the
three axioms by their names: it does not compare their statements with the
axioms of Lean, so an assumption with one of these names passes. `nanoda_bin`
is not the Lean kernel. The Lean kernel remains the authority for the proofs
of the repository, for the build of the kernel and for every claim of this
book. The command does not elaborate Lean sources, finds no proof and
authorizes no `.vast` source.
[Verification boundaries](../verification.md#independent-internal-lean-export-audit-v010-gate)
states the boundary of this audit, and
[issue #282](https://github.com/MGYamada/Vastitas/issues/282) records its
purpose.
