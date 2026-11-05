# Vastitas conformance corpus

`examples/` is the source-level conformance corpus for the public Vastitas
compiler. It is not an unindexed collection of demonstrations. Each entry has
a stable ID and an explicit role in [`corpus.toml`](corpus.toml): an executable
acceptance/rejection contract or a dependency fixture covered by one.

## Layout

| Path | What it tests |
| --- | --- |
| `book/<construct>/*.vast` | Accepted, standalone source programs; also used by the teaching book. |
| `packages/<domain>/<case>/` | Checked path packages and their dependency-only fixtures. Every `Vastitas.toml` is indexed. |
| `reject/<construct>/*.vast` | Rejected standalone sources with a required diagnostic code. |
| `reject/packages/<domain>/<case>/` | Rejected package graphs with an expected diagnostic code (when needed). |
| `corpus.toml` | The machine-readable case registry and expected outcomes. |

The initial domains are `core`, `authority`, `geometry`, `stdlib`, `storage`,
`numerical`, and `tensor`. A package may contain nested package manifests, each
with its own case. No `.vast` source sits directly under `examples/`.

## Case contract

Each `[[case]]` records:

- `id`: a unique, stable dot-separated name, independent of the source path;
- `kind`: `source` or `package`;
- `path`: relative to `examples/`, naming a `.vast` file or `Vastitas.toml`;
- `expect`: `accept` or `reject` for the public `vastitas check` command, or
  `dependency` for a package not valid as a standalone selected closure;
- `diagnostic`: mandatory `E_*` code for a rejected case;
- `covered_by`: mandatory accepted package case ID for a `dependency` fixture;
- `libraries`: optional explicit `--lib` source paths for a standalone case;
- `stdout`: optional exact UTF-8 output (including newlines) of a successful
  native `build` and executable run; absence claims **check acceptance only**.

The corpus must not infer expectations by running the implementation and then
recording its output as an oracle. A changed expectation requires review of the
language contract. Diagnostic checks require both failure status and the named
code as the **first diagnostic**: any other failure is not a conforming rejection.

An authority package may grant editing rights to another package that is not
part of its own standalone dependency closure. Such a package is an indexed
`dependency` fixture, **not** a claim of standalone acceptance. The structural
validator proves its manifest is reachable through path dependencies from its
declared, accepted `covered_by` package. The runner checks that entire package
graph via the public CLI (and deduplicates checks of the same covering root).
Currently the edit-authority `base` and edit-borrow `lib` packages have this
role. No dependency fixture is silently skipped or accepted in isolation.

## Running the corpus

From the repository root:

```sh
python3 scripts/check_conformance_corpus.py
python3 -m unittest discover -s scripts -p test_conformance_corpus.py
```

The first command needs only Python 3.11+ and rejects unindexed sources,
duplicate IDs, missing manifests and broken relative path dependencies.

To exercise the compiler itself, first build the pinned Lean kernel and Rust
driver and generate the standard library package:

```sh
lake -d lean-kernel build vastitas-kernel
cargo build --locked
python3 scripts/build_stdlib_package.py
python3 scripts/check_conformance_corpus.py --run
```

`--case book.geometry` selects matching stable IDs; `--list` displays them.
`--run` performs public `check` on every selected acceptance/rejection contract
or the covering root of a selected dependency fixture; negative cases require
their expected diagnostic, and cases declaring `stdout` are built and run.
Native outputs are compared exactly. The CI compiler job runs this on both
Linux and macOS; structural validation runs without the compiler in the Rust
quality job. BLAS-dependent native execution stays in its dedicated optional
adapter tests, not in this no-BLAS corpus gate.

[`scripts/capture_emit.py`](../scripts/capture_emit.py) enumerates the same
accepted cases when recording frontend wire requests and kernel check/emit
responses. Invalid source may be rejected before wire generation; it is tested
by the corpus runner instead. Corpus checks, runtime witnesses, Lean replay,
mathematical proof, and native refinement remain distinct evidence levels.

## Adding or changing a case

1. Select the narrowest construct or domain directory. Keep related module
   files and path dependencies together.
2. Add one `corpus.toml` entry for each standalone source or package manifest.
   A dependency-only manifest must identify an accepted `covered_by` root whose
   path dependency closure contains it. Do not list individual package modules
   as separate cases.
3. Declare an expected rejection code or an accepted result; declare `stdout`
   only for a deterministic native witness that the no-BLAS CI can run.
4. Update book `{{#include}}` directives, tests and source links if paths move.
   Preserve the stable case ID when reorganizing an existing case.
5. Run structural validation, the public corpus runner, the book checks and
   relevant Rust/kernel tests before merging.

This corpus describes what the implemented compiler accepts, rejects, or
executes. It is **not** evidence that all published mathematical semantics,
CS/MS/CF obligations, or backend refinements are already proved.
