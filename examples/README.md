# Compiler conformance corpus

The index at [corpus.toml](corpus.toml) assigns stable case IDs to the
book's single-file programs, accepted package graphs and rejected examples.
Packages are grouped by subject. Keep each package's relative dependency
graph and module layout together. A dependency that only checks as part of
an application names its covering case in the index.

Run from the repository root.

    python3 scripts/check_conformance_corpus.py
    python3 scripts/check_conformance_corpus.py --list
    python3 scripts/build_stdlib_package.py
    python3 scripts/check_conformance_corpus.py --run

The last command requires the built Rust driver and Lean kernel. It checks
each selected program and requires the first expected diagnostic for a
rejection. A case with a native output witness must also build, exit successfully
and write the declared stdout and stderr bytes. The compiler CI runs these examples on Linux
and macOS. The Rust book tests also pin complete diagnostics and exercise
programs that need the optional OpenBLAS adapter or fail at runtime.

The wire and emission capture consumes this same index. Test results describe
actual compiler runs. Proof claims belong to the verification and
specification chapters. Released source archives retain the paths from
their own tagged revision.
