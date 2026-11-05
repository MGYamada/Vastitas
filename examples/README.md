# Vastitas conformance corpus

`examples/` is the source-level conformance corpus for the public Vastitas
compiler. It is not an unindexed collection of demonstrations. Each testable
entry has a stable ID, an input, and an independently declared expected result
in [`corpus.toml`](corpus.toml).

## Layout

| Path | What it tests |
| --- | --- |
| `book/<construct>/*.vast` | Accepted, standalone source programs; also used by the teaching book. |
| `packages/<domain>/<case>/` | Accepted path packages, including dependent and library-only packages. Every `Vastitas.toml` is indexed. |
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
- `expect`: `accept` or `reject` for the public `vastitas check` command;
- `diagnostic`: mandatory `E_*` code for a rejected case;
- `libraries`: optional explicit `--lib` source paths for a standalone case;
- `stdout`: optional exact UTF-8 output (including newlines) of a successful
  native `build` and executable run; absence claims **check acceptance only**.

The corpus must not infer expectations by running the implementation and then
recording its output as an oracle. A changed expectation requires review of the
language contract. Diagnostic checks require both failure status and the named
code as the **first diagnostic**: any other failure is not a conforming rejection.

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
`--run` performs public `check` on every selected case, rejects negative cases
with their expected diagnostic, and builds/runs cases that declare `stdout`.
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
   Do not list individual module files of a package as separate cases.
3. Declare an expected rejection code or an accepted result; declare `stdout`
   only for a deterministic native witness that the no-BLAS CI can run.
4. Update book `{{#include}}` directives, tests and source links if paths move.
   Preserve the stable case ID when reorganizing an existing case.
5. Run structural validation, the public corpus runner, the book checks and
   relevant Rust/kernel tests before merging.

This corpus describes what the implemented compiler accepts, rejects, or
executes. It is **not** evidence that all published mathematical semantics,
CS/MS/CF obligations, or backend refinements are already proved.
