# Vastitas contributor guidance

## Scope and sources of truth

- Develop the `.vast` compiler. The current milestone is Stage 0; keep later dispatch, tensor, AD, solver, and physics features separate from implemented functionality. Do not add a REPL, user-facing interpreter, LSP, or package manager unless the user expands the scope.
- Read [docs/design.md](docs/design.md) for the design index and the preserved v0.3 proposal. Its pseudocode and conditional mathematical arguments are not claims of implementation or completed formal verification. Use the README and current tests for implementation status.
- Keep documentation honest about what is implemented, tested, proved, assumed, or deferred. User instructions determine the task scope; ordinary authorized work does not require an additional approval ceremony.

## Architecture and semantic boundaries

- Put the Rust frontend and CLI in `src/`. Send the versioned IR defined in [docs/protocol.md](docs/protocol.md) to Lean; Rust acceptance alone is not semantic acceptance. Update both protocol implementations and relevant tests together.
- Keep `lean-kernel/` independent of mathlib and `lean/`. It owns independent IR validation, checked code generation, and the minimal runtime. Generated programs use the runtime, not the compiler driver or proof oracle.
- Keep `lean/` proof-only. It may depend on mathlib and must import the actual `lean-kernel/` definitions instead of copying a second model of the implementation. Do not use `sorry`, `admit`, or custom unproved axioms to present an obligation as proved. State the scope and assumptions of each theorem; checker proofs do not establish the entire native toolchain's correctness.
- Preserve the distinction between `Scheme` and `CInfScheme`, explicit geometric bases, and nominal object identities. Equal dimensions or equal descriptors do not identify endpoints. A coefficient-ring marker such as `QQ` is not itself the geometric test object in `Point<X, S>`.
- Preserve point/morphism endpoints through dependent arguments and packaging. Unpacking introduces scoped identities; reject escaping points or mismatched objects rather than erasing the failed check. Only checked IR may reach code generation.
- Keep both Lean projects on the same pinned toolchain and keep dependency lockfiles. Ordinary compilation and generated executables must remain usable without mathlib.

## Validation

- Run checks appropriate to the changed subsystem. Rust changes: `cargo fmt --check`, `cargo clippy --all-targets -- -D warnings`, and `cargo test`. Kernel changes: `lake -d lean-kernel build`. Oracle changes: `lake -d lean build`.
- For changes crossing the compiler boundary, build the kernel before integration tests and exercise both `vastitas check` and `vastitas build` on relevant `.vast` examples. Execute generated binaries and test invalid source or tampered IR when affected.
- Preserve the test that the normal compiler path works without mathlib. Add meaningful semantic or regression cases; avoid tests that merely repeat the implementation.
- Report actual commands and results. If a dependency or toolchain prevents a check, describe that specific limitation instead of claiming the check passed.
