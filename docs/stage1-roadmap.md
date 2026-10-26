# Stage 0 hardening and Stage 1a delivery

The four implementation increments below have been implemented and validated
through Stage 1a. This is not completion of the historical Stage 1 roadmap.
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

Independent lambdas, user-defined value types/capabilities, function edit
ownership, impact regions, borrowing, storage ownership, and linear algebra are
later Stage 1 increments. Stage 1a is not completion of all Stage 1 acceptance
criteria in the original proposal. No deferred issue is closed merely because
it is recorded here.
