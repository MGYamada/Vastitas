# Implementation roadmap through Stage 1b and package foundations

The initial four implementation increments below were delivered through
Stage 1a. Independent static functions and the first package/module increment are
implemented, with separate acceptance gates below. This is not completion of historical Stage 1.
The historical v0.3 proposal remains unchanged under `docs/design/`.

| Delivery | Pull request | Acceptance |
| --- | --- | --- |
| Stage 0 reliability | [#30](https://github.com/MGYamada/Vastitas/pull/30) | Regression and hosted CI checks passed |
| Stage 0 usability | [#31](https://github.com/MGYamada/Vastitas/pull/31) | Regression and hosted CI checks passed |
| Stage 0 safety | [#32](https://github.com/MGYamada/Vastitas/pull/32) | Full core soundness/type-safety proof and hosted axiom audit passed before Stage 1a began |
| Stage 1a dispatch | [#33](https://github.com/MGYamada/Vastitas/pull/33) | Finite engine proofs, native regressions, and macOS/Linux no-mathlib CI passed |

The PRs are stacked in that order. Their linked implementation issues close
upon merge; the deferred design issues below remain open. See
[Stage 1a](stage1a.md) and the [proof boundary](verification.md) for the current
contract and exact theorem scope.

The next stack is:

| Change set | Tracking | Delivery |
| --- | --- | --- |
| Input/output, codegen, cancellation hardening | #35, #36, #40, #45, #46 | [PR #51](https://github.com/MGYamada/Vastitas/pull/51) |
| Diagnostics and precise specification/proof scope | #38, #39, #41–44, #47 | [PR #53](https://github.com/MGYamada/Vastitas/pull/53) |
| Independent functions and static higher-order specialization | [#50](https://github.com/MGYamada/Vastitas/issues/50) | [PR #54](https://github.com/MGYamada/Vastitas/pull/54), [contract](stage1b.md) |

Each increment requires local validation, macOS/Linux no-mathlib CI, and the
oracle axiom audit. Fix issues close on PR merge, not merely PR creation.

## Delivery gates

| Change set | Issues | Required result |
| --- | --- | --- |
| Stage 0 reliability | #2–9, #11–17 | Exact rejection diagnostics, bounded native lowering, linear call-graph processing, and reproducible runtime builds |
| Stage 0 usability | #10, #18–21 | Explicit Nat-to-Int conversion, else-if, actionable identity/unsupported-feature diagnostics, accurate proof descriptions |
| Stage 0 safety | #29 | Actual-checker soundness, terminating typed evaluation, and runtime endpoint correspondence |
| Stage 1a dispatch | #27 | Closed-world finite nominal/static-capability checking and statically selected native calls |

The Stage 0 safety gate was proved and passed its proof build and hosted axiom
audit before Stage 1a implementation began. Merely extracting the property of a
certified subtype does not establish checker soundness. The safety gate covers
the actual checked language and its elaboration from decoded raw IR, not the
Rust parser, JSON decoder, Lean/C code generator, linker, or operating system.

## Stage 1a interface

The initial public dispatch universe is `Nat`, `Int`, `Bool`, and `Unit`.
`Any` and `Number` are selector-only abstract types; Nat and Int are siblings.
Generic declarations explicitly list concrete callable-domain tuples; methods
have explicit selectors and scalar result types. Optional `requires (HasOrder)`
uses compiler-established static facts (`HasOrder` implies `HasEq`).

Lean constructs and verifies the finite key environment. Ambiguity is checked
on every admitted key, coverage on the declared domain, and selection follows
the nominal/capability product order. There is no runtime generic-dispatch
fallback or selection using erased geometry identities. The key-space limit
is 4096. Every applicable ground method body is checked before lowering to the
ordinary checked core. The frontend/backend wire protocol is version 2.

## Deferred decisions

Issues #22–26 and #28 remain open design work. For this delivery, keep the
shadowing prohibition, generative object identities, saturating Nat subtraction,
and recursion prohibition. Explicit `int(n)` makes true integer subtraction
available without an implicit conversion. Reverse conversion and changing the
entrypoint result type are deferred.

Stage 1b implements independent lambdas and `Fn<Input, Output>` function values
with statically resolved calls. A generic family is not a function value;
ordinary functions/lambdas provide wrappers. This boundary is recorded in
#48 without claiming abstract types or abstract method contracts are complete.

Issues #37 (same-type argument constraints) and #48 remain open alongside
#22–26 and #28. User-defined value types/capabilities, function edit
ownership, impact regions, borrowing, storage ownership, and linear algebra are
later Stage 1 increments. Stage 1b is not completion of all Stage 1 acceptance
criteria in the original proposal. No deferred issue is closed merely because
it is recorded here.


## Package/module foundation (#56, first increment of #52)

Protocol 3 adds a separately validated namespace IR, preserving protocol 2.
The first PR supplies Lean resolution/visibility/owner checks and proofs; the
second supplies the explicit `Vastitas.toml` loader, modules, CLI, native examples
and documentation. Both require all four kernel regression targets, Rust fmt,
strict Clippy, all tests, oracle build and axiom audit, macOS/Linux no-mathlib
CI, review resolution, merge and local main synchronization.

The implemented boundary is local path dependencies and call-only imports.
Only the exact owning module may add generic methods. #52 remains open for
edit borrowing, authority transfer, impact regions and revalidation semantics.
#48 still needs abstract types and abstract methods; #49 needs those interfaces
and further ownership work to move geometry into the stdlib; #55 needs an
explicit promoted-result representation and static common-type rules in addition
to this ownership foundation. #37 stays an independent next candidate. None of
these design issues closes merely because module ownership is now checked.

See [packages](packages.md) for the current contract. The historical v0.3
proposal remains unchanged.
