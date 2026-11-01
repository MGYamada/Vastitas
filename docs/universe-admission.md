# Universe admission: first Lean model

This is partial implementation progress for [#350](https://github.com/MGYamada/Vastitas/issues/350).
The Universe Charter specifies the jurisdiction of constitutional guarantees;
it is independent of the Constitution. This model does **not** complete the
Charter, change CS/MS/CF, or expand the public compiler's certified scope.

## Scope and reuse

`lean-kernel/VastitasKernel/UniverseAdmission.lean` supplies a closed
`RuntimeTy : Type`, `El : RuntimeTy → Type`, a small `CoreHom` family and `denote`.
These are ordinary declarations in the pinned official Lean foundation. There
is no additional foundational axiom, proof verifier or Domain Checker.

| Code | Mathematical interpretation | Representation obligations reused |
| --- | --- | --- |
| `scalar` | Nat, Int, Bool, Unit, homogeneous Nat/Int pairs | Existing `Indexed.Core.PureType`, `Semantics.ValueHasType`, actual Core audit and evaluation |
| `tensorShape` | The exact symbolic layout interpreted over mathematical Nat valuations | `Storage.Shapes.Layout`, live integral slot checks, `Shapes.check`, then `Storage.checkLayout` at a valuation |
| `ownedMap` | Finite coordinate functions returning the existing real/complex UInt64 literal bit patterns, indexed by the selected nominal bases | `Numerical.Valid`, exact basis equality, `auditState`, `OwnedMap.Live` and `OwnedMap.Initialized` |

“Finite scalar profile” means a closed set of implemented scalar types; Nat and
Int remain arbitrary precision. Pair support is existing homogeneous Pair support,
not general records or sums. Bit-pattern coordinates are not identified with
ideal RR/CC values, and no new floating-point arithmetic laws are asserted.

`El` gives mathematical meaning without synthesizing executable values. For
example, a symbolic layout with an invalid leading dimension still has a
mathematical interpretation. An owned-map coordinate function by itself supplies
neither an allocation nor a relationship to native heap contents. The latter
relationship is a future refinement obligation, not part of this structural
admission certificate.

`Representation` is an explicit request, separate from a type's meaning.
`admit` requires it and returns a certificate indexed by the exact target,
context, type and request. Its `Layoutable` field composes existing component
predicates. The only modeled target is the current Lean-runtime/LP64 profile;
adding a target requires its own representation policy.

For shapes, `Layoutable` is **conditional** representation evidence. Static
literals and dynamic integral slots remain distinct. `realizeShape` checks the
actual capacity, leading dimension, LP64 and byte bounds for the supplied
valuation and returns the exact concrete layout. Mathematical valuations are
the same ones used by the existing shape proofs; a certificate does not itself
prove correspondence with runtime scalar slots or UInt64 narrowing. Production
slot availability, narrowing and event ordering remain owned by ResourceSource,
ValueFlow and the shape checker. The tests also retain rejection of negative Int
extents instead of silently saturating them to zero.

Owned moves use the actual `Functions.OwnedMapTransfer` receipts and
`checkAction` transitions. They do not enter the pure function arrow family.
The regression constructs an actual checked resource function call with a
padded owned result, checks its returned receipt, and rejects stale owners,
live-loan moves, missing initialization and equal-dimensional but different bases.

## Computational boundary

`CoreHom` currently contains scalar identity, Nat-to-Int, Boolean negation and
the executable integral nonnegativity decision. Static scalar parameters are
specialized to concrete `Indexed.Core` signatures and submitted to the existing
`Typing.checkModule`. There is no constructor embedding all Lean functions
`El a → El b`, nor an unrestricted identity operation that duplicates owners.

`scalarCode?` and `literalCore?` are deliberately tiny, syntactic meta bridges.
They whitelist supported scalar type constants and literal data. They reject
function spaces, arbitrary Lean types, `Sort` expressions, first-class
`RuntimeTy`, proof terms, noncomputable constants and applications (including
choice hidden below an application). They do not normalize arbitrary Lean
expressions or decide computability of arbitrary definitions. Type aliases and
additional executable expressions need explicit future support.

The regressions additionally ask the official Lean compiler to compile a value
depending on `Classical.choice` and a decision depending on
`Classical.propDecidable`; both must produce the expected noncomputability error.
This is distinct from permitting standard Lean axioms in mathematical proofs.
No `sorry`, custom axiom, `unsafe` definition or `native_decide` is added to the
model or its proofs. The existing transitive axiom audit covers the new oracle
module, and permits only the project's existing standard Lean axioms.

## Established facts and remaining obligations

`lean/VastitasOracle/UniverseAdmission.lean` imports the actual implementation.
The official kernel checks the following local facts:

- Scalar encodings have the existing Core semantic types.
- Successful specialization returns the exact submitted Core module.
- The four scalar arrow forms agree with the existing Core evaluator for every
  input, with an explicit sufficient observation-fuel bound.
- No admission certificate can omit the supplied representation, and its
  representation is fixed by the request.
- Shape admission entails acceptance by the existing symbolic checker. Under
  that checker's guard premises, its actual instantiated schedule is accepted
  by the concrete storage checker with the exact interpreted final state.
- Owned-map admission entails actual nominal, liveness and initialization
  obligations; owned transfer retains the existing exact move/binding receipt.
- The shape realization function is independent of the supplied admission
  proof. This is a local proof-irrelevance fact only.

These facts do **not** establish the source staging theorem, full compiler proof
erasure/noninterference, proof-syntax-independent caches or code generation,
arbitrary dependent runtime types, arbitrary real/complex payload realization,
native heap refinement, numerical correctness, or Charter-amendment replay.
General records/sums, finite categorical/scheme objects and admitted-scope
manifests remain outside this increment.

The public protocol-8 path in `Main.lean` remains unchanged:
`ResourceSource.Wire.check` precedes `ResourceSource.Codegen.generate` on its
actual returned certificate. `Context.ofExecution` can project the actual
execution context, but it does not infer source acceptance from a standalone
model certificate. This module is not imported by `Main`, and these adapters
must never be used as a replacement public acceptance path.

## Verification and #350 acceptance progress

Run from the repository root with the pinned Lean 4.35.0 toolchain:

```sh
lake -d lean-kernel build
bash scripts/check_kernel_regressions.sh
lake -d lean build
(cd lean && lake env lean ../scripts/audit_axioms.lean)
python3 scripts/check_boundaries.py
```

`VastitasStorageTest.UniverseRegression` is included in the existing kernel
regression script and therefore in both Linux and macOS compiler CI. It tests
accepted scalar/shape/owned-map examples, forged Core and metadata, runtime guard
failures, missing representations, unsupported Lean types, choice-dependent
runtime definitions and disallowed universe reflection. Kernel proof checking
and executable regression observations remain distinct forms of evidence.

| #350 initial acceptance item | This increment |
| --- | --- |
| Minimal interface and representations | Partial: scalars/pairs, shape metadata, actual owned-map transfer; general record/sum support remains open |
| Static generics/closure-free staging | Partial: finite scalar specialization and universal denotation facts; full source staging remains open |
| Proof erasure/noninterference | Local realization proof irrelevance only; full compiled-semantics guarantee remains open |
| Executable decisions versus noncomputable choice | Partial: checked integer decision, shape guard failures and actual Lean noncomputability rejection |
| Finite categorical/scheme presentations | Open |
| Unsupported universes and missing layout evidence | Partial: negative tests at the explicit model boundary; public Charter integration remains open |
| Charter amendment and evidence replay | Open |

All broad #350 checkboxes remain open until their entire requirements are met.
