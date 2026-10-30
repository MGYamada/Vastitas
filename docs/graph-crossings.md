# Internal Graph crossing checker

The first executable Graph fragment checks finite, ordered, oriented crossing
words and proposed local rewrites. It implements part of [#201](https://github.com/MGYamada/Vastitas/issues/201)
in `VastitasKernel.Graph`, with regressions in `GraphRegression` and conditional
soundness theorems in `VastitasOracle.Graph`.

This is internal infrastructure. It is not a public `std::monoidal` API, a new
wire protocol, a source tensor lowering path, or an extension of
`Indexed.Core.Term`. `Graph.Core` is the actual structural Core returned by this
checker; connecting it to compiler-returned indexed terms remains pending.
It does not add a release target or a new Stage 1 completion condition.

## Data and authority

- `Strand` retains an occurrence ID, an actual `Indexed.ObjectRef`, and an
  integer degree. Equal degrees or equal objects never merge occurrences.
- `Boundary` retains a presentation brand, a binary bracket shape and the
  ordered source strands. The brand is supplied by the internal caller; this
  module does not establish its generative allocation/freshness.
- Each `Crossing` records the entire selected profile, its current adjacent
  position, its direction and both actual input strands. The auditor replays
  all crossings and compares all stored metadata and the actual target.
- `Profile` retains canonical generic/method IDs using `Namespace.Owner`, the
  implementation revision, profile/category/base/tensor/unit identities,
  associator, both unitors and the chosen braiding. It does not infer category
  or tensor semantics from these names.
- `Context` contains an already checked indexed declaration environment,
  supplied in-scope object references, the selected profile, canonical tensor
  ID and an `Authority Lawful`. Source strands must refer to valid, in-scope
  objects with the profile's coefficient marker.

`Authority` carries a proof of the caller-supplied predicate
`Lawful profile capability`. A request only carries an `EvidenceRef` and must
match that exact authority, including its certificate identity and full
profile. Supplying a different capability label, stale implementation revision
or another profile's certificate does not upgrade it.

**Trust boundary:** this increment does not implement the production provider
of `Lawful`, canonical tensor resolution, actual method selection, or the
derivation of `inScope` from source/Core bindings. The integration layer must
obtain these from the actual checked program and verified mathematical laws;
they are not frontend-authored serialized flags. The regression fixture uses
`FixtureLaws := True` explicitly and only to test the checker. That fixture is
not a certified monoidal category and must not become a production authority.
Integer degrees are preserved metadata here, not an implementation of the
independent Grading Checker.

## Supported checks and rewrites

Words execute left to right. At the current pair `A,B`, a positive crossing
denotes `β_(A,B)`, while a negative crossing denotes `β_(B,A)^(-1)`; both have
source `A⊗B` and target `B⊗A`. Their equal endpoint permutation does not erase
their distinct direction.

| Rule | Required capability | Local pattern |
| --- | --- | --- |
| Inverse cancellation | Braided or Symmetric | `i⁺;i⁻` or `i⁻;i⁺` to empty |
| Adjacent braid | Braided or Symmetric | Same-sign `i;(i+1);i ↔ (i+1);i;(i+1)` |
| Distant commutation | Braided or Symmetric | Exchange crossings at positions separated by at least two, retaining both signs |
| Symmetric cancellation | Symmetric | Same-sign `i;i` to empty |

The rules check bounds against the actual source arity. Monoidal rejects every
crossing. Inverse and symmetric cancellation only reduce words; there is no
search for a normal form. Mixed-sign braid rules and arbitrary user-morphism
nodes are not included.

`checkCore` independently audits the selected binding, source shape, unique
occurrences, nominal scope/base, allowed capability, actual crossing sequence
and exact target. `checkRewrite` checks both full cores, exact evidence, the
rule instance, unchanged source/profile/target, and the exact prefix, local
pattern and suffix. A result with the same permutation or coordinates cannot
replace the requested output. `CheckedRewrite` is indexed by the actual input
and request and retains an equation tying its returned `core` to that request.

`checkTrace` rechecks every intermediate proposal and binds the final result to
the actual `returned` graph. It rejects skipped/reordered steps and returning
an intermediate or unrelated graph. Neither checker computes scalar values.

Bracket shape and presentation brand are unchanged by every supported rewrite.
No reassociation/unitor rule exists. Valid nominal leaf references are retained;
equal dimensions, coordinates or flattened factor lists cannot identify them.
The aggregate tensor object and its explicit associator lifts still need a
categorical/source representation. This fragment does not silently identify
an associator with equality of nominal tensor objects.

## Proved scope

The proof oracle imports the actual kernel implementation. There are no new
unproved axioms, `sorry` declarations or copied checker implementations.

| Theorem | Scope |
| --- | --- |
| `monoidal_no_crossings` | A well-formed graph under Monoidal authority has no crossings |
| `checked_rewrite_boundaries` | Actual input/output are audited and preserve exact profile, source and target |
| `checked_rewrite_binding` | Actual returned graph uses the selected/canonical identity and the same authority's law predicate |
| `rule_sound`, `context_sound` | Each allowed rule and its fixed surrounding context preserve an independently supplied interpretation |
| `checked_rewrite_sound` | Conditional semantic equality for the actual returned Core |
| `trace_boundaries`, `checked_trace_sound` | Finite trace preserves audited boundaries and conditional semantics through its actual final return |

Semantic equality is conditional on
`Interpretation profile capability arity M`. This supplies composition and the
four explicit generating laws, with valid-position hypotheses at that arity.
Its laws are about fixed word patterns, not about checker acceptance. Context
preservation follows from composition; trace preservation follows by induction.
The type `M` can represent an action on a family of ordered boundaries, but
constructing the intended categorical interpretation is not proved here.

In particular, `Authority.verified` and the oracle's `Interpretation` have not
yet been joined by a production law provider. The conditional theorem does not
derive braid relations from hexagons, prove that an arbitrary implementation
realizes a tensor, or identify this word denotation with compiler/native
execution. See [remaining proof obligations](graph-proof-obligations.md).

## Exact Python reference and regressions

`scripts/graph_reference.py` is the independent standard-library-only reference
using `Fraction` and `χ_q(a,b)=q^(ab)` for graded rational lines. Negative
crossings explicitly use `1/χ_q(b,a)`. The closed fixture registry models
authority binding; it does not verify Lean certificates.

The 45 reference tests in `scripts/test_graph_reference.py` include:

- Degrees `[-2,2]`: 25 inverse/symmetric pairs, 125 braid triples in both signs,
  both bicharacter multiplicativities and 625 distant-commutation quadruples.
- `q=2`, degrees `(1,1)`: positive double crossing has coefficient 4,
  negative double crossing 1/4, and opposite signs cancel to 1.
- Degrees `(1,2,3)`: both braid paths have coefficient 2048.
- `q=-1`: symmetric double crossings cancel, but the same representation with
  only Braided authority cannot acquire a symmetric rewrite from observation.
- Profile/certificate/capability/revision substitution, stale equal-degree
  ports, orientation erasure, changed brackets/brand, changed return values,
  and equal-scalar/permutation shortcuts are rejected.

The pure braid `σ₁²σ₂²σ₁⁻²σ₂⁻²` evaluates to scalar 1 and the identity
permutation in this one-dimensional representation for every degree triple.
The tests check 125 triples. Independently, the integral matrices
`A=((1,1),(0,1))`, `B=((1,0),(-1,1))` satisfy `ABA=BAB` but send this word to
`((13,8),(8,5))`, not the identity. This demonstrates why equal observations
cannot decide arbitrary braid equality. Neither representation is exposed as
a general braid or user-morphism equality solver.

The Lean kernel regressions run 500 signed/directional braid cases on those
125 degree triples, inverse/symmetric cases, all sign pairs for far
commutation, and explicit malformed metadata/authority/return negative cases.
These runtime checks are distinct from the conditional general theorems.

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/demo_graph_reference.py
lake -d lean-kernel build
bash scripts/check_kernel_regressions.sh
lake -d lean build
cd lean && lake env lean ../scripts/audit_axioms.lean
```

Existing CI discovers the Python tests, runs `GraphRegression` through the
kernel regression script, and builds/audits `VastitasOracle.Graph` through the
oracle root. Python is a development reference, not a compiler/runtime
dependency. The existing 8 Domain Checkers plus independent Ownership/Borrow
architecture and historical Stage 1 completion criteria are unchanged.

The [finite CAR/spin reference](car-spin-reference.md) reuses this exact
evaluator and fixture authority for #246's one/two-mode examples. It retains
the QQ scalar-line profiles, explicitly embeds their coefficients into Q(i),
and distinguishes ordinary spin tensor from Koszul exchange. Its matrix
equalities and Pauli rank witnesses grant no additional Graph rewrite rules.
