# Pure evaluation and graph proofs

<a id="pure-evaluation-and-graph-checker-proofs"></a>

The pure evaluator and the finite crossing-word checker have separate inputs and theorems. Each section identifies the definitions used by its proofs and the remaining correspondence obligations. Neither checker is a [public checker route](../appendix/glossary.md#public-checker-route): no command reaches it, as [Verification boundaries](../verification.md#how-to-read-this-chapter) explains. The theorems of both sections are Proved (oracle).

<a id="universe-totality"></a>

## Least-fuel meaning for accepted scalar Core

**Internal observer.** The theorems of this section are about
`ScalarFuel`, an observer that no command reaches. It reads the Core audit
`Typing.checkModule`, a component of the current routes, and the kernel's
Core evaluator `Semantics.eval`.

This is the first finite implementation of the totality obligations that
[History](#history) names. It is independent of the
unmerged universe admission model. It does not complete the
Universe Charter, general stateful semantics, or CF.

### Profile and connection to the implementation

`lean-kernel/VastitasKernel/ScalarFuel.lean` operates on the existing
`Indexed.Core.Term`, `Module`, `Function` and `Semantics.Value`. It reuses the
existing scalar operations; it does not define a parallel expression language.
The supported syntax consists of literals, variables, unary/binary operations,
homogeneous pairs and projections, Nat-to-Int conversion, ascriptions, scopes,
branches and `letE`. Values are arbitrary-precision Nat/Int, Bool, Unit and the
existing homogeneous pairs. “Finite profile” limits constructors, not integer
values or input cardinality.

`supported` inspects both branches and every nested term. Calls, primitives,
packages and unpacking are outside the profile, even in an unselected branch.
The existing public evaluator, checker and native generator are unchanged.
This observer is internal proof/test infrastructure, not a public interpreter.

`AcceptedHom a b` retains the actual module input, the exact successful
`Typing.checkModule input false` equation and returned `CheckedModule`, the
selected function ID and lookup equation, its input/output signature, and the
profile evidence. `stage` runs that existing independent audit before applying
the profile restriction. The initial interface admits one parameter at Core
symbol zero; pairs allow the existing two-component scalar input. An accepted
certificate cannot be obtained from `supported` or a mathematical function
alone. `accepted_actual_core` proves the returned module is the input module.
These are Core-level facts; this adapter does not claim source elaboration,
target representation, or code-generation refinement.

### Outcomes and fuel

`EvalOutcome A` distinguishes `outOfFuel`, `success A`, and `failure Failure`.
Failures record a missing variable, an invalid operand, or an unsupported
observer form. They are operational failures of this observer. They do not
implement `monad::safediv`, and a pure error returned as a language value would
instead be a success. Unsupported-form rejection is not a claimed semantics
for calls, packages or other excluded operations.

`evalFuel` keeps the existing evaluator's depth-fuel convention and evaluation
order. Children receive the remaining depth independently. Consequently fuel
is neither elapsed time nor an instruction count, and sequential bounds use
`max`, not addition. `evalAccepted` decodes into the actual codomain `El b`.

The following are Lean theorems, not sampled test observations:

| Theorem | Established statement |
| --- | --- |
| `evalFuel_terminal` | For fixed term and environment, any terminal result at `n` is exactly preserved at **every** `n' ≥ n`, including failures. |
| `evalFuel_erases` | For every fuel and supported term, erasing the refined outcome to `Option` equals the existing `Semantics.eval` on that exact term. |
| `evalAccepted_success_iff` | At each fuel, typed success is equivalent to the existing checked-body evaluation returning the encoded value. |
| `accepted_total` | Every accepted arrow in this profile has a successful fuel for every typed input, derived from `IndexedProgramSafety.checked_functions_total_and_typed`. |
| `letE_budget` | A successful first computation at `n` followed by a terminal body at `m` gives that body outcome at every fuel at least `max n m + 1`. The second bound may depend on the intermediate value. |

The raw terminal theorem needs no typing assumption, so it covers failures of
malformed scalar terms as well. Accepted typed arrows have no operational
failure: totality and terminal stability exclude it. There is no mutable heap,
resource state or effect trace in this profile; `Values` is a fixed immutable
environment, extended locally by `letE`.

### Least fuel and derived meaning

`VastitasOracle.LeastFuel` implements a Nat.find-style search using only Lean
core accessibility recursion and an executable `DecidablePred`. An existential
success witness proves accessibility starting at zero; the search advances by
one while the predicate is false. `least_spec` proves success and
`least_minimal` proves minimality. No custom axiom, `sorry`, `native_decide`,
Mathlib import or choice-based witness extraction is used.

The search is a **specification-level `noncomputable def`** using `Acc.rec`;
it is not advertised as a compiled runtime implementation or a promise of
kernel normalization on arbitrary proof terms. Each fuel observation and its
`IsSuccess` predicate are executable independently of that definition.

`TotalHom a b` is the subtype of `AcceptedHom a b` carrying
`∀ x, ∃ n, IsSuccess (evalAccepted f n x)` in `Prop`. `certify` supplies the
proved certificate for this profile. `denoteTotal f x` extracts the value at
the **least successful fuel**; no independent function is stored or assumed.

`leastFuel_success`, `leastFuel_minimal`, `denoteTotal_agrees` and
`denoteTotal_actual_core` establish existence, minimality, universal
sufficient-fuel agreement, and agreement with the actual checked Core.
`successful_value_unique` covers any observed success, while
`before_least_outOfFuel` shows every smaller observation is exhausted.
Changing only the totality certificate gives definitionally identical meaning;
the required proof-irrelevance regression is literally `rfl`.

### Validation

`VastitasOracle.ScalarFuelRegression` is imported by the normal oracle root,
so the existing oracle build and transitive axiom CI audit cover these
definitions and proofs. The search and its two specifications depend only on
the permitted `propext` and `Quot.sound`; the axiom audit additionally rejects
`Classical.choice` in those three declarations. The connected Core evaluator
and totality bridge retain the existing transitive `propext`, `Classical.choice`,
`Quot.sound` assumptions, as does the original `Semantics.eval`. There are no
further logical axioms. Kernel-checked examples include a selected branch with
least fuel 2 for `true` and 3 for `false`, its derived mathematical value,
terminal failures, exhaustion, `letE`/pair evaluation, saturating subtraction,
mixed-type rejection and certificate proof irrelevance. A concrete admission
equation uses logical typing/order evidence checked by Lean; it does not rely
on native evaluation of the checker's internal hashing. Separate executable
regressions exercise stage acceptance, wrong signatures, an absent function
and an invalid unused branch; these tests do not provide proof authority.

Relevant checks: the kernel, oracle and audit sequence in
[Validate the compiler and proofs](../development/validation.md), and
`python3 scripts/check_boundaries.py`.

### Remaining obligations

- Extend outcome refinement and exact evaluator correspondence to calls,
  general recursion/divergence, primitives and packages. This work does not
  replace the general evaluator's `Option Value` result.
- Give stateful/ownership-sensitive evaluation separate initial/final heap,
  resource and trace indices; prove preservation of every terminal failure
  **including its state and observable trace**, at all larger fuel.
- Prove accepted composition construction/closure, identity and associativity,
  representation/ownership compatibility and the denotation composition law.
  `letE_budget` is an operational sequencing lemma, not those category laws.
- Extend the pure `TotalHom` bridge to the Charter's target/context/representation
  boundary and additional runtime codes. This local `PureType`/`El` instance
  does not supersede the universe admission model that
  [History](#history) names.
- Connect the exact source/selected-method/environment/revision identities,
  staging and proof erasure through the compiler and cache, then establish
  native refinement under explicit backend assumptions.
- Connect admitted mathematical constructions to CF and any future partial or
  operational CF formulation. Total evaluation and least-fuel meaning alone
  establish no algebraic law, mathematical algorithm specification, or CF claim.

<a id="graph-crossings"></a>

## Internal Graph crossing checker

**Internal checker.** The theorems of this section are about
`VastitasKernel.Graph`, a checker that no command reaches: only
`GraphRegression` and the oracle read it.

The first executable Graph fragment checks finite, ordered, oriented crossing
words and proposed local rewrites. It is implemented
in `VastitasKernel.Graph`, with regressions in `GraphRegression` and conditional
soundness theorems in `VastitasOracle.Graph`.

This is internal infrastructure. It is not a public `std::monoidal` API, a
wire protocol, a source tensor lowering path, or an extension of
`Indexed.Core.Term`. `Graph.Core` is the actual structural Core returned by this
checker; connecting it to compiler-returned indexed terms remains pending.
It does not add a release target or a Stage 1 completion condition.

### Data and authority

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

### Supported checks and rewrites

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

### Proved scope

The proof oracle imports the actual kernel implementation. No axiom beyond
the three that the audit admits is used, and there are no `sorry`
declarations or copied checker implementations.

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
No field mentions `profile`; it is a nominal tag, so the theorems do not show
that a model realizes the declarations of that profile.
Its laws are about fixed word patterns, not about checker acceptance. Context
preservation follows from composition; trace preservation follows by induction.
The type `M` can represent an action on a family of ordered boundaries, but
constructing the intended categorical interpretation is not proved here.

In particular, `Authority.verified` and the oracle's `Interpretation` have not
yet been joined by a production law provider. The conditional theorem does not
derive braid relations from hexagons, prove that an arbitrary implementation
realizes a tensor, or identify this word denotation with compiler/native
execution. The intended-model coherence and source correspondence remain open, and model-owned tensor binding is separate work. [History](#history) names both issues.

### Exact Python reference and regressions

`scripts/graph_reference.py` is the independent standard-library-only reference
using `Fraction` and `χ_q(a,b)=q^(ab)` for graded rational lines. Negative
crossings explicitly use `1/χ_q(b,a)`. The closed fixture registry models
authority binding; it does not verify Lean certificates.

The reference tests in `scripts/test_graph_reference.py` include:

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
```

Then run the kernel, oracle and audit sequence in
[Validate the compiler and proofs](../development/validation.md).

Existing CI discovers the Python tests, runs `GraphRegression` through the
kernel regression script, and builds/audits `VastitasOracle.Graph` through the
oracle root. Python is a development reference, not a compiler/runtime
dependency. The existing 8 Domain Checkers plus independent Ownership/Borrow
architecture and historical Stage 1 completion criteria are unchanged.

## History

- **Least-fuel meaning for accepted scalar Core.** The section is the first
  finite implementation of the totality obligations in
  [#350](https://github.com/MGYamada/Vastitas/issues/350). It is independent of the unmerged universe admission
  model in [#368](https://github.com/MGYamada/Vastitas/pull/368), and its local `PureType`/`El` instance does
  not supersede that model.
- **Internal Graph crossing checker.** The fragment implements part of
  [#201](https://github.com/MGYamada/Vastitas/issues/201). The intended-model coherence and source correspondence
  remain open in that issue. Model-owned tensor binding follows
  [#387](https://github.com/MGYamada/Vastitas/issues/387).
