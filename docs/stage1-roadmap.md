# Stage 0 hardening and Stage 1a delivery

This is an implementation plan, not a completion or verification claim.
The historical v0.3 proposal remains unchanged under `docs/design/`.

## Delivery gates

| Change set | Issues | Required result |
| --- | --- | --- |
| Stage 0 reliability | #2–9, #11–17 | Exact rejection diagnostics, bounded native lowering, linear call-graph processing, and reproducible runtime builds |
| Stage 0 usability | #10, #18–21 | Explicit Nat-to-Int conversion, else-if, actionable identity/unsupported-feature diagnostics, accurate proof descriptions |
| Stage 0 safety | #29 | Actual-checker soundness, terminating typed evaluation, and runtime endpoint correspondence |
| Stage 1a dispatch | #27 | Closed-world finite nominal/static-capability checking and statically selected native calls |

Stage 1a implementation starts only after the Stage 0 safety gate is proved and
passes the proof build and axiom audit. Merely extracting the property of a
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
ordinary checked core. The frontend/backend protocol will move together to
version 2 when this feature is implemented.

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
