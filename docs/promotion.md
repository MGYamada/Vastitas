# Initial Nat/Int promotion

The implemented increment consists of homogeneous numeric Pair data, selected
method result types, four stdlib `promote` methods, and their reuse by `add` and
`maximum`. It completes the initial scope of #55, not the full historical
Stage 1 proposal. Abstract types, relational selectors, edit borrowing, general
conversion search, geometry promotion and variadic promotion remain separate.

## Public contract

| Input key | `promote` result | `add` / `maximum` result |
| --- | --- | --- |
| Nat, Nat | Pair<Nat> | Nat |
| Nat, Int | Pair<Int> | Int |
| Int, Nat | Pair<Int> | Int |
| Int, Int | Pair<Int> | Int |

`pair` requires independently inferred operands of one identical numeric type.
Projections preserve that type and component order. Pair is not a dispatch
key, a Fn contract component, a nested/general tuple or a geometric package.
Generic selection uses scalar argument types and the existing finite
nominal/capability product order. A caller's expected result never chooses a
winner or changes a bare literal from Int to Nat.

The only nonidentity conversion is explicit `int(n)`. Each mixed arithmetic
method binds promotion once and calls the homogeneous Int method using the
Pair's projections. Homogeneous methods still call their scalar kernels.
Primitive operators do not gain mixed-type coercions. All applicable bodies,
including losing/out-of-domain/unused instances, must check; the complete
specialized call graph must be acyclic before pruning.

See [stdlib usage](../stdlib/README.md), [dispatch](stage1a.md),
[Pair and Fn boundaries](stage1b.md#homogeneous-data-pairs) and
[protocol](protocol.md). In package mode, the exact owner is
`arithmetic::generic`; imports and reexports confer call access only. Flat
`--lib` mode preserves its existing whole-assembly semantics.

## Actual-body proofs and fixture agreement

`tests/promotion.rs::stdlib_ir_matches_proof_fixture` runs the real Rust
`parse_sources` frontend on the three canonical stdlib files using stable
virtual diagnostic filenames/offsets. It compares the complete JSON against
`tests/fixtures/promotion.json`; it does not substitute a handwritten AST.
Both no-mathlib CI jobs run this test.

`VastitasPromotion.Fixture` runs the actual JSON decoder and public surface
checker while elaborating the fixture. It reflects their returned raw program
and checked module as ordinary transparent Lean data. Build-time checks compare
both reflected values with the actual decoder/checker outputs. Lake tracks the
JSON as an input dependency of this separate test/proof library; it is not a
dependency of ordinary compiler builds. Concrete fixture acceptance and this
reflection agreement are executable checks, not a new general decoder proof.

`VastitasOracle.Promotion` proves evaluation using the existing `Semantics.Eval`
rules on those exact checked bodies, for arbitrary Nat/Int arguments:

| Theorem | Contract |
| --- | --- |
| `promotion_total` | Each of the four bodies evaluates to the specified Pair and has its exact concrete return type |
| `promotion_preserves_values` | Each evaluated component has its original integer value, interpreting Nat with `Int.ofNat` |
| `same_type_identity_nat`, `same_type_identity_int` | Same-type promotion preserves type, values and component order |
| `reversal` | Swapping inputs preserves common type and swaps components; the reversed actual body evaluates accordingly |
| `idempotence` | Re-promoting the resulting components preserves type and values |
| `embedding_preserves_addition`, `embedding_preserves_order`, `embedding_preserves_maximum` | The Nat-to-Int embedding preserves the required arithmetic/order facts |
| `addition_correct`, `maximum_correct` | The actual mixed bodies evaluate through their shared let, promotion call, projections and homogeneous kernel to the specified numerical result |

The individual `promote_nn/ni/in/ii`, `add_nn/ni/in/ii` and
`maximum_nn/ni/in/ii` lemmas expose the actual evaluation derivations. The
general `checkProgram`, `checkSurfaceProgram` and `checkNamespaceProgram`
typing/order/termination theorems still apply to their exact accepted outputs.
Idempotence does not replace the dependency-order proof.

This does not prove Rust parsing, general JSON decoding, filesystem authenticity,
full surface/namespace rewriting equivalence, or native-toolchain equivalence.
Package source parity, namespace acceptance and flat/package native behavior
are covered by regression checks; the numerical fixture uses flat input.

## Regression and maintenance

`VastitasPromotion.Regression` checks actual acceptance through all three
public paths, the 16 binary keys and selected method identities, numerical
results, and forged checked-call metadata. Its bounded scalar/Pair evaluator
uses the real primitive semantics only as a test harness. The oracle proofs
above establish the arbitrary-input claims.

Two mutations are deliberately accepted by ordinary typing but rejected by the
stdlib contract: a mixed method returning `pair(0, 0)` and a Nat/Nat method
returning Pair<Int>. The compiler has no special policy keyed on `promote`.
The native and raw-IR suites additionally cover large integers, zero, negatives,
invalid Pair forms, expected-type mismatch, ambiguity outside the domain,
coverage, nonwinners, cycles, ownership, aliases and function boundaries.

After an intentional stdlib change, regenerate and review the fixture:

```sh
VASTITAS_UPDATE_PROMOTION_FIXTURE=1 cargo test --locked --test promotion stdlib_ir_matches_proof_fixture
lake -d lean-kernel build VastitasPromotion.Regression
lake -d lean build VastitasOracle
```

A semantic change may require new proofs; regeneration alone is not approval
of a changed numerical policy. Run the full validation documented in
[verification](verification.md), including hosted axiom and no-mathlib checks.
No `sorry`, `admit`, native-decision axiom or custom unproved axiom is used by
these numerical proofs.

The stdlib now has one tracked set of definitions. Run
`python3 scripts/build_stdlib_package.py` to create the ignored manifest-mode
sources under `stdlib/target/package/`; `--check` verifies freshness. The
manifest location and logical module owners are unchanged. This source consolidation
followed #72–#76 and is separate from the
[post-Stage-1 docs cleanup](docs-cleanup-plan.md).
