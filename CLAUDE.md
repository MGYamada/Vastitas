# Vastitas contributor guidance

## Keep this file small

Keep AGENTS.md and CLAUDE.md identical: **100 lines / 6,000 UTF-8 bytes** each.
`scripts/check_docs.py` checks limits and equality. Keep rules/links here,
specs in docs, decisions in Issues, fixture results and history in Git.
No release/publication histories. Shorten rules; only explicit user instruction
may raise limits.

## Scope and evidence

- Develop `.vast`; status: [README](README.md), tests and
  [acceptance](docs/stage1-acceptance.md)/[completion](docs/stage1-completion.md).
  Stage 1b is not full Stage 1 completion.
- [Design](docs/design.md) is a proposal; distinguish implementation, tests, proofs,
  assumptions and deferred work.
- **Fast like C is the primary goal.** Follow [storage ownership](docs/storage-ownership.md):
  explicit layouts/aliases, destination/scratch reuse, allocation/packing/retention
  costs and equivalent-C measurements. Record gaps; native/BLAS use is insufficient.
- User instructions set scope; authorized work needs no extra approval. No REPL,
  user-facing interpreter, LSP or package manager without scope expansion.
  Keep AD, solver, physics and broader profiles separate.

## Architecture and invariants

- Rust frontend/CLI: `src/`. Lean checks the [protocol](docs/protocol.md)
  independently; update both sides/tests together. Generate only from exact checked IR.
- `lean-kernel/` is independent of `lean/` and mathlib; executables use the runtime.
  `lean/` is proof-only; its sole Lake dependency is the actual local kernel.
  Pin Lean toolchains together; keep lockfiles. Normal compilation needs no mathlib/OpenBLAS.
- No `sorry`, `admit` or custom unproved axioms. Follow [proof boundaries](docs/verification.md)
  and [stdlib admission](docs/adr/0001-mathematics-first-stdlib.md). State assumptions;
  distinguish checker acceptance, mathematical meaning, floats and native refinement.
- Public protocols 2-6 use `Indexed.LegacySource`, 7 uses `Indexed.Wire`, and 8/9
  use `ResourceSource.Wire`. Preserve full authority/Fn/dispatch composition,
  all-body audits and returned-Core equations. Internal/retired checks cannot replace public acceptance.
- Align canonical package namespaces with directories and `mod.vast`.
  Preserve IDs, owners, visibility and provenance. Imports grant no edit authority;
  separate definition ID/edit ownership. Retain `--lib`/`--manifest-path` compatibility;
  protect manifests/module files from output overwrites.
- Audit unused, nonwinning, out-of-domain and unapplied bodies. Keep signature
  probes separate from executable instances. Preserve capture/shadowing bans,
  exact Fn targets, recursion rejection and 4096-key/specialization limits.
  Dispatch remains finite; expected results never choose call keys.
- Preserve nominal objects/bases/endpoints and scoped unpack identities; dimensions
  grant no identity/authority. Distinguish Scheme/CInfScheme and markers/geometric bases.
  Keep unbounded integers, saturating Nat subtraction, explicit Nat-to-Int and Pair restrictions.
- Keep storage separate from pure Core. Preserve provenance, byte initialization,
  aliases/layouts, suspended reborrows, inside-out returns, branch joins and exact
  source/schedule/native audits. No escaping loans/owners.
- Numerical/tensor operations retain nominal bases, dual/conjugate/metric
  authority, exact receipts and physical preflight before writes. Ports do not
  imply disjoint memory. No implicit conjugation/metric/copy/allocation. Preserve
  packing, versions and invalidation. Keep optional runtimes outside the oracle.

- [Mathlib bridge](docs/daleckii-krein.md) stays outside compiler/oracle dependencies.
  For changes run its build, `Audit.lean`, official `leanchecker` and boundary tests.

## Read relevant contracts before editing

- [Dispatch](docs/stage1a.md), [Fn](docs/stage1b.md),
  [abstract contracts](docs/abstract-types.md), [promotion](docs/promotion.md).
- [Packages](docs/packages.md), [edit borrowing](docs/edit-borrowing.md),
  [reborrow/transfer](docs/edit-authority.md), [indexed declarations](docs/indexed-declarations.md),
  [indexed source](docs/indexed-source.md), [geometry](docs/geometry-migration.md).
- [Storage IR/native cleanup](docs/storage-ir.md), [resource calls](docs/storage-functions.md),
  [public resources](docs/resource-source.md), [runtime shapes](docs/runtime-shapes.md).
- [Numerical adapter](docs/numerical-adapter.md), [declarations](docs/numerical-declarations.md),
  [values](docs/numerical-values.md), [transforms](docs/linear-transforms.md),
  [vectors](docs/vector-evaluation.md), [owned packages](docs/owned-map-packages.md).
- [Networks](docs/finite-networks.md), [packing](docs/tensor-packing.md),
  [trees](docs/contraction-trees.md), [cached packing](docs/cached-packing.md),
  [internal graph](docs/graph-crossings.md).

## Validation

- Run `python3 scripts/check_docs.py`; add meaningful behavior regressions.
- Rust: `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`,
  `cargo test --locked --all-targets`. Kernel: `lake -d lean-kernel build`.
  Oracle: `lake -d lean build` and `lake -d lean env lean scripts/audit_axioms.lean`.
- Build the kernel before integration tests. Exercise `check`, `build`, executables
  and invalid source/tampered IR. Preserve no-mathlib tests; distinguish public/retired paths.
- Kernel/checker/dispatch/Fn/authority: `bash scripts/check_kernel_regressions.sh`.
  Indexed Core/codegen: `bash scripts/check_indexed_native.sh`.
  Storage lowering/native: `bash scripts/check_storage_native.sh`.
- GEMM: `python3 scripts/check_gemm_native.py --prefix <prefix>`.
  Checked GEMM/lowering/FFI: `python3 scripts/check_gemm_checked.py --prefix <prefix>`.
  Use pinned sequential LP64 OpenBLAS 0.3.34; Linux also uses `--valgrind`
  with a supported CPU target. Report native tests separately from proofs.
- Report actual commands/results and blockers; do not claim unrun checks passed.
