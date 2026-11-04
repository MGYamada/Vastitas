# Diagnostics and the CLI

This chapter gathers what you have used so far into a working routine: the
commands, how to read a rejection, and what can still go wrong after a program
has been built.

## The commands

```text
vastitas check INPUT.vast [--lib LIBRARY.vast]...
vastitas build INPUT.vast [--lib LIBRARY.vast]... -o OUTPUT
vastitas check --manifest-path Vastitas.toml
vastitas build --manifest-path Vastitas.toml -o OUTPUT [--openblas-prefix PREFIX] [--native-cc COMPILER]
vastitas audit-lean LEAN4EXPORT.ndjson
```

- **Flat mode** takes one entry file plus repeated `--lib` libraries
  ([Chapter 1](stdlib.md#flat-mode-with---lib)).
- **Manifest mode** takes one `Vastitas.toml` and cannot be mixed with flat mode.
- `--openblas-prefix` and `--native-cc` apply only to builds whose checked entry
  has numerical operations; anywhere else they are rejected. The prefix is
  required only when that entry runs GEMM ([Chapter 10](numerical.md)).
- `audit-lean` is an internal, non-authoritative cross-check of Lean proof
  exports. It does not check `.vast` programs.
- `vastitas --help` prints the usage and `vastitas --version` the version and
  wire protocols.

## Reading a diagnostic

A rejected source produces one line per diagnostic:

```text
FILE:LINE:COLUMN: CODE: message
```

`LINE` and `COLUMN` are one-based, and columns count Unicode scalars. In flat
mode each `--lib` file keeps its own positions, and package diagnostics name the
original module file. For the program from
[Chapter 1](hello-vastitas.md#when-the-checker-says-no), a local build of the
compiler printed the following; message wording can change between revisions:

```text
target/manual-bad.vast:1:20: E_TYPE: expected Int, found Bool
```

The **code** says which rule failed; the message gives the detail. Errors that
have no source position, such as a bad command line or an unbuilt kernel, print
`CODE: message` alone. The process exits with status 1, or with 128 plus the
signal number when it was interrupted.

## Common codes

| Code | What it usually means | Where it is taught |
| --- | --- | --- |
| `E_TYPE` | A value has the wrong type | [Chapter 2](values-and-functions.md) |
| `E_DUPLICATE` | A binding or declaration reuses a name in the same scope | [Chapter 2](values-and-functions.md#bindings-and-blocks) |
| `E_SHADOW` | A binding reuses the name of a function or of an enclosing binding | [Chapter 2](values-and-functions.md#bindings-and-blocks) |
| `E_RECURSION` | A function calls itself, directly or through others | [Chapter 2](values-and-functions.md#functions) |
| `E_DISPATCH_AMBIGUOUS` | Two methods are equally specific for some argument tuple | [Chapter 4](dispatch.md#how-a-method-is-chosen) |
| `E_CAPTURE` | A lambda refers to a value from outside its own scope | [Chapter 5](function-values.md#no-captures) |
| `E_STATIC_CALL` | A function-valued expression has more than one possible target | [Chapter 5](function-values.md#one-static-target-per-call) |
| `E_OWNER` | A declaration edits something its module does not own | [Chapter 6](modules-and-authority.md#edit-authority) |
| `E_LIMIT` | An input exceeded a published compiler limit | [Appendix D](../appendix/limits.md) |

[Appendix B](../appendix/diagnostics.md) lists every code family and the
checker that reports it.

Geometry and resource diagnostics add notes. An identity mismatch names the
source bindings and where each identity was introduced: a construction, a
parameter, a call, an `unpack` or a branch merge. A resource failure points to
the failing statement and names the allocation and any conflicting loan.

## After the build

A program that passed every check can still fail at run time. The common
cases are:

- An `expect` statement finds different bits in a cell and reports
  `E_NATIVE_EXPECT`.
- The native runtime's physical preflight rejects a layout, bound or alias
  before a write, with another `E_NATIVE_*` code.
- An allocation exceeds the live-byte budget (`E_NATIVE_ALLOCATION`), or the
  linked OpenBLAS has the wrong version, ABI or threading (`E_NATIVE_ABI`).
- A runtime extent is negative or too large (`E_RUNTIME_EXTENT`).

[Appendix B](../appendix/diagnostics.md#native-runtime) lists every runtime code.

Function bodies are not transactions: writes made before a native failure are
not rolled back, and no initialized result is published.

## Environment and outputs

`VASTITAS_KERNEL` and `VASTITAS_KERNEL_ROOT` select the backend
([Installation](installation.md#selecting-a-kernel)). Input files are limited
to 16 MiB each and 64 MiB in total per compilation. `build` refuses
nonregular output paths and paths that alias any input, including manifests and
module files. It replaces an existing output only after a successful build.

> **What is checked.** The full command contract, including signal handling,
> concurrent native builds and the proof-export audit, is in the
> [CLI reference](cli.md). Every diagnostic family is listed in the
> [diagnostics reference](../appendix/diagnostics.md) and every numeric bound in
> [Compiler limits](../appendix/limits.md).
