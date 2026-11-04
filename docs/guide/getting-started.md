# Getting Started

This chapter takes you from an empty machine to a running program:

- [Installation](installation.md) sets up the pinned Rust and Lean toolchains,
  builds the Lean kernel and installs the alpha crate.
- [Hello, Vastitas](hello-vastitas.md) checks, builds and runs a first program,
  then shows what a rejection looks like.
- [Packages and manifests](stdlib.md) moves from a single file to a package with
  a `Vastitas.toml`, and uses the standard library.

Vastitas runs on macOS and Linux. Compilation always has two halves. The Rust
driver `vastitas` parses your source. The Lean kernel `vastitas-kernel` checks
it and, for `build`, generates a native executable. You need both before
anything works.

There is no REPL, user-facing interpreter, language server or package registry. You write
`.vast` files, check them and build native programs.
