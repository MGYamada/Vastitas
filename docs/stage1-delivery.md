# Stage 1 stabilization and edit-borrow delivery

This records the earlier protocol-5 delivery. The subsequent historical
Stage 1 completion work and current status are tracked in
[Stage 1 completion](stage1-completion.md) and issue #179; the later-work
snapshot below is retained as the scope of this earlier increment.

Snapshot: 2026-10-28. Every open issue is classified below. Classification is not completion. Issues close only when a merged PR meets their acceptance criteria and records validation. Parent issues #48, #49, #52 and #64 remain open for residual scope.

## Current fixes

Dependency: all of these precede protocol 5 implementation. The existing common-lowering/typed-ID/shared-limit refactor is delivered with #141. Implementation PR: [#167](https://github.com/MGYamada/Vastitas/pull/167), merged after all hosted checks passed.

| Issue | Work |
| --- | --- |
| [#140](https://github.com/MGYamada/Vastitas/issues/140) | A new child abstract type lets any module add scalar memberships to another module's abstract type |
| [#141](https://github.com/MGYamada/Vastitas/issues/141) | Stage 1b lowering is quadratic in program size once any lambda or function value is present |
| [#142](https://github.com/MGYamada/Vastitas/issues/142) | A 64-level Fn parameter type is rejected as "only scalars and Fn types" instead of a nesting limit |
| [#143](https://github.com/MGYamada/Vastitas/issues/143) | The driver waits without bound for descendants that keep the backend or Lake pipes open |
| [#144](https://github.com/MGYamada/Vastitas/issues/144) | Abstract hierarchy errors are reported at the entry file or root manifest 1:1 instead of the offending declaration |
| [#145](https://github.com/MGYamada/Vastitas/issues/145) | Flat-mode qualified method selectors bypass the frontend's "qualified type paths require package input" check |
| [#146](https://github.com/MGYamada/Vastitas/issues/146) | README and verification docs omit the AbstractRegression and ContractRegression validation targets |

## Edit borrowing implementation

Dependency chain: #140–146 → #154 → #155 → #156 → #157 → #158. Implementation PR and hosted acceptance evidence are linked from children #154–158 below. #52 and #64 are umbrella tracking, not automatically closed by this increment.

| Issue | Work |
| --- | --- |
| [#52](https://github.com/MGYamada/Vastitas/issues/52) | Introduce packages and Rust-style modules with namespace-owned functions and borrowed imports |
| [#64](https://github.com/MGYamada/Vastitas/issues/64) | Umbrella: connect whole-function ownership to namespace IR, scoped edit borrowing and validated assemblies |
| [#154](https://github.com/MGYamada/Vastitas/issues/154) | Edit borrowing: protocol 5 declarations, namespace identity and assembly trace |
| [#155](https://github.com/MGYamada/Vastitas/issues/155) | Edit borrowing: independent grants, exclusive loans and contribution provenance |
| [#156](https://github.com/MGYamada/Vastitas/issues/156) | Edit borrowing: final assembly completion, footprint authorization and body checking |
| [#157](https://github.com/MGYamada/Vastitas/issues/157) | Edit borrowing: proofs for actual namespace acceptance, trace and lowering correspondence |
| [#158](https://github.com/MGYamada/Vastitas/issues/158) | Edit borrowing: frontend, examples, adversarial regressions and no-mathlib CI |

Scope: package-only grants, declarative contributions, exclusive borrow/apply/return/seal assembly, final footprint authorization, independent acceptance and lowering correspondence. Preserve protocols 2/3/4 and legacy libraries. Guarantees begin at decoded inputs.

## Later features and design

These issues remain open; no unrelated behavior changes are included. #48's finite abstract selectors and contracts were delivered by PRs #138/#139, but abstract values and broader historical Stage 1 remain future work. #49's geometry depends on #58–63; #61 also needs its abstract/dependent interfaces. #66–71/#91–92 retain storage, geometry and numerical-backend dependencies. Macro work #68/#70/#77–80 retains expansion/hygiene dependencies. #128/#153, #130, #151 and #152 are separate workstreams and do not change this delivery's recursion, geometry or frontend boundary.

| Issue | Remaining work |
| --- | --- |
| [#22](https://github.com/MGYamada/Vastitas/issues/22) | Design: should `let` shadowing be allowed? |
| [#23](https://github.com/MGYamada/Vastitas/issues/23) | Design: function results that keep identity, and packages with several components |
| [#24](https://github.com/MGYamada/Vastitas/issues/24) | Design: generative or applicative identity for canonical constructions? |
| [#25](https://github.com/MGYamada/Vastitas/issues/25) | Design: should `Nat` subtraction silently saturate at zero? |
| [#26](https://github.com/MGYamada/Vastitas/issues/26) | Design: plan for iteration and recursion, and how they interact with nominal identities and ownership |
| [#28](https://github.com/MGYamada/Vastitas/issues/28) | Design: should evidence and provenance tracking live in the language core or in a library and build layer? |
| [#37](https://github.com/MGYamada/Vastitas/issues/37) | Design: abstract-selector fallbacks cannot relate their arguments (`HasOrder` is per argument, and out-of-domain keys are checked) |
| [#48](https://github.com/MGYamada/Vastitas/issues/48) | Separate fn/lambdas from generic dispatch; add abstract types and domain-aware abstract methods |
| [#49](https://github.com/MGYamada/Vastitas/issues/49) | Define Scheme and CInfScheme as abstract types in the .vast standard library |
| [#58](https://github.com/MGYamada/Vastitas/issues/58) | Generalize declaration resolution and indexed-type IR for library-defined geometry |
| [#59](https://github.com/MGYamada/Vastitas/issues/59) | Generalize nominal identity and existential scope checks for geometric type families |
| [#60](https://github.com/MGYamada/Vastitas/issues/60) | Make geometry primitive contracts and mathematical evidence boundaries explicit |
| [#61](https://github.com/MGYamada/Vastitas/issues/61) | Implement geometric interfaces and affine operations in the .vast standard library |
| [#62](https://github.com/MGYamada/Vastitas/issues/62) | Extend independent Lean declaration and acceptance proofs to library-defined geometry |
| [#63](https://github.com/MGYamada/Vastitas/issues/63) | Complete geometry stdlib migration with compatibility regressions and bridge removal |
| [#66](https://github.com/MGYamada/Vastitas/issues/66) | Design std::linalg around geometric tensor values, checked networks, and numerical backends |
| [#67](https://github.com/MGYamada/Vastitas/issues/67) | Specify explicit conjugation, algebraic duality, and Hermitian adjoint in the type system and IR |
| [#68](https://github.com/MGYamada/Vastitas/issues/68) | Introduce hygienic Julia-style prefixed string-literal macros before type checking |
| [#69](https://github.com/MGYamada/Vastitas/issues/69) | Define type-checked tensor-network contraction without implicit conjugation |
| [#70](https://github.com/MGYamada/Vastitas/issues/70) | Add ein"..."(args) as a compile-time parsed, typed einsum macro |
| [#71](https://github.com/MGYamada/Vastitas/issues/71) | Specify complex reverse-mode AD for explicit conjugation, tensor contractions, and metric gradients |
| [#77](https://github.com/MGYamada/Vastitas/issues/77) | Introduce a unified hygienic macro system for syntax-level metaprogramming |
| [#78](https://github.com/MGYamada/Vastitas/issues/78) | Add hygiene-aware syntax objects, macro scopes, and a pre-type-check expansion phase |
| [#79](https://github.com/MGYamada/Vastitas/issues/79) | Introduce declarative hygienic macros with syntax-fragment matching and quote/splice |
| [#80](https://github.com/MGYamada/Vastitas/issues/80) | Define pure, deterministic, resource-bounded compile-time macro evaluation |
| [#87](https://github.com/MGYamada/Vastitas/issues/87) | Add a type ascription expression `(expr : Type)` |
| [#88](https://github.com/MGYamada/Vastitas/issues/88) | Make `_` a discard binder in `let` and `unpack` |
| [#89](https://github.com/MGYamada/Vastitas/issues/89) | Add total integer division/remainder and an explicit Int-to-Nat conversion |
| [#90](https://github.com/MGYamada/Vastitas/issues/90) | Support grouped imports `use path::{a, b as c};` |
| [#91](https://github.com/MGYamada/Vastitas/issues/91) | Specify a minimal typed GEMM API with endpoint, basis, and buffer ownership contracts |
| [#92](https://github.com/MGYamada/Vastitas/issues/92) | Adopt OpenBLAS as the default CPU backend for CInf numerical linear algebra |
| [#96](https://github.com/MGYamada/Vastitas/issues/96) | Define a finite subtype join-semilattice and Union<A, B> types |
| [#97](https://github.com/MGYamada/Vastitas/issues/97) | Introduce indexed SubObject<X> and Open<X> geometric subobjects |
| [#98](https://github.com/MGYamada/Vastitas/issues/98) | Define frame/locale topology, verified covers, and sheaf gluing |
| [#103](https://github.com/MGYamada/Vastitas/issues/103) | Define canonical Affine(n) smooth geometry and checked CInfScheme object gluing |
| [#104](https://github.com/MGYamada/Vastitas/issues/104) | Construct algebraic schemes by gluing Affine(K, 1) Zariski charts |
| [#107](https://github.com/MGYamada/Vastitas/issues/107) | Freeze mathematics-first stdlib: algebra, geometry, analysis, and differential equations |
| [#123](https://github.com/MGYamada/Vastitas/issues/123) | Literal typing of constant subexpressions such as `(1 + 2)` still depends on operand and branch order |
| [#124](https://github.com/MGYamada/Vastitas/issues/124) | An `else if` chain with 63 or more conditions is rejected as excessive expression nesting |
| [#125](https://github.com/MGYamada/Vastitas/issues/125) | Suggest `unpack` when a block statement is written as `value as { scheme: …, point: … }` |
| [#126](https://github.com/MGYamada/Vastitas/issues/126) | Warn about unused `let`/`unpack` bindings and parameters |
| [#128](https://github.com/MGYamada/Vastitas/issues/128) | Allow explicit pure partial application while keeping lambdas capture-free |
| [#130](https://github.com/MGYamada/Vastitas/issues/130) | Separate runtime partiality from mathematical totality and guarantee tail recursion from the outset |
| [#147](https://github.com/MGYamada/Vastitas/issues/147) | Suggest `int(...)` when a Nat is used where an Int is expected |
| [#148](https://github.com/MGYamada/Vastitas/issues/148) | `E_DISPATCH_COVERAGE` should explain why each candidate is inapplicable and where the uncovered key comes from |
| [#149](https://github.com/MGYamada/Vastitas/issues/149) | Explain generative identity when an endpoint mismatch comes from writing the same construction twice |
| [#150](https://github.com/MGYamada/Vastitas/issues/150) | Allow `main` to return Nat, Bool, Unit, Pair<Nat> or Pair<Int> |
| [#151](https://github.com/MGYamada/Vastitas/issues/151) | Implement a finite QQ principal-open descent checker with overlap and cocycle proofs |
| [#152](https://github.com/MGYamada/Vastitas/issues/152) | v0.2.0 release gate: migrate the entire compiler and CLI to Lean 4 |
| [#153](https://github.com/MGYamada/Vastitas/issues/153) | Implement explicit Int partial application with static targets and checked environments |
| [#159](https://github.com/MGYamada/Vastitas/issues/159) | Mathematics checker architecture umbrella |
| [#160](https://github.com/MGYamada/Vastitas/issues/160) | Mathematics standard-library implementation epic |
| [#161](https://github.com/MGYamada/Vastitas/issues/161) | Weil primitives and forward-over-reverse HVP |
| [#162](https://github.com/MGYamada/Vastitas/issues/162) | HomG / SU(2) and linear algebra |
| [#163](https://github.com/MGYamada/Vastitas/issues/163) | Owner-controlled custom pullback registration (depends on #52/#64 plus later AD) |
| [#164](https://github.com/MGYamada/Vastitas/issues/164) | Optimizer primal and pullback design |
| [#165](https://github.com/MGYamada/Vastitas/issues/165) | Exact fields versus Float certified numerics |

## Completion evidence

Record implementation PRs, local commands/results, hosted macOS/Linux no-mathlib CI and oracle axiom audit before requesting merge. Do not infer completion from documentation, a draft PR or partial parent checklists. Reborrowing, ownership transfer, runtime editing, incremental caching, recursion extensions, geometric stdlib migration, storage ownership and linear algebra are excluded.


### Protocol-5 local validation (2026-10-28)

- `cargo fmt --check` and `cargo clippy --locked --all-targets -- -D warnings`: passed.
- `cargo test --locked --all-targets`: 204 passed, including 9 edit-borrowing tests and the 20,000-function watchdogs.
- `lake -d lean-kernel build` and `bash scripts/check_kernel_regressions.sh`: passed, including the imported direct EditRegression checks.
- `lake -d lean build`: passed. `(cd lean && lake env lean ../scripts/audit_axioms.lean)`: 6,351 declarations audited with only the standard allowed axioms.
- Python checker tests: 14 passed; dependency boundaries and generated stdlib consistency passed.
- `vastitas check` / `vastitas build` for `examples/packages/edit-borrow/app/Vastitas.toml`: passed; generated binary printed `42`.

The linked implementation PR records hosted macOS/Linux no-mathlib CI, oracle
axiom audit, review and merge evidence. These local results alone do not close
any child or umbrella issue.
