# Derivative-rule coherence reference (#163 / #164 / #192)

This executable **Python reference and specification** distinguishes true
ambient derivatives, derivatives within a set, and explicitly selected
backwards. It refines the design obligations in [#163](https://github.com/MGYamada/Vastitas/issues/163),
[#164](https://github.com/MGYamada/Vastitas/issues/164), and
[#192](https://github.com/MGYamada/Vastitas/issues/192).
It is not production AD, a Lean theorem, an authenticated rule registry,
actual-Core derivative acceptance, or a general differentiability decision
procedure. No new checker, release target or CF completion is claimed.

The reviewed implementation baseline is
`e026b89cbdbe6ea2f766cde7d18bdd959f48a007`. The examples follow #278's pinned
mathlib semantics, #279's independent proof-route principle, and #285's intended
independent mathematical semantics / Bridge architecture. The latter is not a
claim that the proposed packages or migration already exist.

PR #270 already supplies the [metric reference](metric-reference.md). This
reference has no metric, musical-map or coordinate-conversion implementation.

The mathematical API review uses mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned by the baseline lockfile:

- [FDeriv/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Basic.lean)
- [FDeriv/Congr.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Congr.lean)
- [FDeriv/Comp.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Comp.lean)
- [FDeriv/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/FDeriv/Defs.lean)
- [TangentCone/Real.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/TangentCone/Real.lean)

## 1. Three contracts, with explicit scope

Use distinct semantic propositions. The names below are proposed vocabulary,
not implemented public syntax.

| Contract | Mathematical meaning | What does not follow |
| --- | --- | --- |
| `AmbientDerivative(f,x,L)` | `HasFDerivAt f L x` for the declared scalar field, normed spaces and map interpretation | No derivative at another point, no derivative field on an entire region, no native correctness |
| `WithinDerivative(f,S,x,L)` | `HasFDerivWithinAt f L S x`, retaining the actual set/filter | No ambient differentiability and no unrestricted uniqueness without further hypotheses |
| `SelectedBackward(f,x,policy,B)` | The explicit backward program realizes the declared policy/action at its indexed cotangent endpoints | No assertion that `B` is the dual of a true derivative |

`L` is a continuous linear map. In the finite real examples its matrix is `J`;
the backward is the canonical dual `L*(eta) = eta o L`, represented by `J^T eta`.
No metric, gradient, Hermitian identification or implicit conjugation is involved.
Real and complex derivative contracts are not interchangeable.

Keep **the map's domain**, **the set S used for within differentiation**, and
**the set U on which a registered rule is promised to work** as distinct data.
A point theorem is not a `forall x in U` theorem. If the primal is a partial map,
an ambient statement requires a specified interpretation on a neighborhood of x;
an arbitrary extension outside its domain cannot redefine the original map.

Record function/method identity and revision, defining/attaching authority,
environment and mathematical model, scalar field, source/target identities,
domain hypotheses, basepoint x and output f(x), exact linear/backward code,
proof kind, quantifier scope and dependencies. A name, shape, successful sample,
priority, `fderiv` value or producer-supplied checked flag is not this evidence.
Mathlib's total `fderiv`/`fderivWithin` functions include default choices; use
`HasFDerivAt`/`HasFDerivWithinAt` evidence, not the mere availability of a value.

## 2. Direct-versus-composite coherence for true derivatives

Work first over real normed spaces E, F, G. Analogous scalar profiles require
their own correctly typed hypotheses. Let g:E->F, h:F->G, f:E->G and x:E.

### Ambient rule

Require independently checked witnesses for

```text
HasFDerivAt f L x
HasFDerivAt g A x
HasFDerivAt h B (g x)
f =ᶠ[𝓝 x] h o g
```

The last premise is equality on a neighborhood of x (equality of germs), not
just `f(x) = h(g(x))`. Global equality is sufficient but unnecessary. The chain
rule supplies `HasFDerivAt (h o g) (B.comp A) x`; neighborhood congruence
transports it to f, and uniqueness proves

```text
L = B.comp A
L* = A* o B*.
```

The germ equality also gives `f(x)=h(g(x))`. Retain the corresponding output
fiber transport so both backwards consume a cotangent at the same actual point.
Equality means equality as linear maps, hence for every valid cotangent seed,
not agreement for one seed. The proof does not require global smoothness of f,
g or h; differentiability at the stated points and the local equality suffice.

For two unrelated direct implementations f1 and f2, the same argument uses
`HasFDerivAt f1 L1 x`, `HasFDerivAt f2 L2 x` and their germ equality. Different
nominal objects, scalar structures or charts need explicit valid transports;
equal dimensions do not discharge these premises.

For a reusable derivative field on U, establish these conditions for every
point in the claimed U. Equality of the two derivatives at one x proves only
the pointwise claim. In particular, `2x` and `4x` agree at zero; this cannot
certify the former as the derivative field of `2x²`. Conversely, the scalar
zero *is* the true derivative at zero if proved using a valid point theorem.

### Within-set rule and uniqueness

The corresponding sufficient premises are

```text
HasFDerivWithinAt f L S x
HasFDerivWithinAt g A S x
HasFDerivWithinAt h B T (g x)
MapsTo g S T                         -- or the appropriate local Tendsto proof
f =ᶠ[𝓝[S] x] h o g
f(x) = h(g(x))
UniqueDiffWithinAt k S x.
```

Public applications also retain required membership witnesses, including x in
S and g(x) in T. The separate basepoint equation is needed by within-congruence;
it is not inferred from an arbitrary punctured or within filter. When x in S
and an adequate relative neighborhood equality imply it, record that derivation.

Chain-rule and congruence give two within derivatives of the same map on S;
`UniqueDiffWithinAt.eq` gives equality of their full continuous linear maps.
Uniqueness on T is not necessary merely to compose given witnesses. If two
rules have different within sets, first justify a common restriction or equality
of their local filters, and then prove uniqueness on that actual comparison
set. Intersecting two domains can destroy uniqueness.

Without `UniqueDiffWithinAt`, the individual within witnesses may still be
valid. Equality on the tangent cone (`HasFDerivWithinAt.unique_on`) is weaker
than equality of the ambient linear maps. Reject an unsupported full-map
coherence claim; do not relabel valid within evidence as false.

### Promotion to the ambient derivative is a separate rule

The standard sufficient promotion is

```text
HasFDerivWithinAt f L S x + S in 𝓝 x  =>  HasFDerivAt f L x.
```

`IsOpen S` together with `x in S` suffices. `UniqueDiffWithinAt k S x` alone
does not. For `f(x)=|x|`, `S=[0,infinity)`, x=0, the within derivative is uniquely
the slope 1, but there is no ambient derivative at zero. At x=1 this same S is
a neighborhood and the promotion is legitimate. For `S={0}`, arbitrary slopes
are valid within derivatives at zero; neither uniqueness nor promotion holds.

The neighborhood premise is sufficient, not necessary for every possible proof
of ambient differentiability. An independent ambient proof may already exist;
restriction plus within uniqueness can then identify its derivative with L.
A separately proved gluing theorem can also be used with all its premises.
Neither route follows from within uniqueness alone, and an extension theorem
must still establish the required neighborhood agreement with the original map.

## 3. Acceptance, rejected candidates and available proof routes

Distinguish proposing a rule, admitting a registration, resolving an occurrence,
and proving an optimizer rewrite. Preserve diagnostics and proof dependencies.

| Situation | Required outcome |
| --- | --- |
| Two true-derivative routes with the coherence premises above | Establish equality, then either proved implementation may be chosen; retain its provenance. |
| A candidate has only tests, an unsupported hypothesis or an invalid proof | Refuse that candidate's requested certificate. Report missing/failed obligations, not a theorem of non-differentiability. |
| One optional candidate is refused and an independent route proves the exact requested derivative | The occurrence may use the proved route. The refused candidate is not installed or silently upgraded. |
| An explicit required rule/selected policy fails, or an active registry is inconsistent | Fail that request/registration; no silent substitution by a different policy or dropping of a required invalid attachment. |
| Two purported true rules disagree under identical checked premises | Treat as an evidence, binding or implementation inconsistency; no priority/import-order override. |
| A within proof lacks uniqueness | Keep its within status; reject the unproved full-map equality claim. |
| A within proof lacks ambient promotion evidence | Reject ambient promotion; still permit an independent ambient proof if available. |
| A selected backward equals a true derivative numerically | Retain selected status until a separate derivative/correspondence proof is checked. |

The simplest independent-route witness is `g(x)=|x|`, `h(u)=u²` at zero.
The usual ambient chain rule through g is unavailable, while the whole
composite equals x² and has a valid derivative. This follows #279. A true-rule
request can use the whole-function proof; it need not discover a differentiable
factorization or claim that the failed factorization is valid.

## 4. Optimizer consequence (#164)

For a true-derivative context, a certified primal germ equality and valid
ambient derivative evidence on both sides justify equality of pullbacks by
uniqueness. No independently guessed priority between the two rules is needed.
Retain the applicability domain, scalar profile, basepoint/output transports,
and any separate realization/ownership obligations.

For a selected-backward context, primal germ equality does not prove equality
of the selected action. Require policy-aware equality for every admitted
cotangent seed on the claimed domain, including residual dependence; otherwise
reject the rewrite or preserve a barrier. Existing ReLU examples in #164 remain
valid. A true derivative proof for the same primal does not erase an observable
selected policy. Equally, a selected policy never supplies the premises of
`HasFDerivAt.unique`.

The branch `if x == 0 then 0 else x` denotes the identity over R. Its zero
branch is constant only on `{0}`. That branch's within derivative is not a
certificate for the whole function. An exact whole-function equality proof
permits the ambient derivative 1. A separately declared zero-backward policy
remains selected and cannot silently replace this true derivative.

## 5. Executable reference and its limits

Run with Python 3.10+ and no third-party packages:

```sh
python3 -m unittest discover -s scripts -p 'test_derivative_coherence_reference.py' -v
```

The [reference](../scripts/derivative_coherence_reference.py) and
[regressions](../scripts/test_derivative_coherence_reference.py) use
`Fraction`, exact polynomial coefficients, a closed domain catalogue and
explicit evidence constructors. No floating tolerances, finite differences,
ForwardDiff invocation or production Vastitas execution are involved.

For `g(x)=(x,x²)`, `h(u,v)=u²+v`, `f(x)=2x²`, the reference independently
checks the direct polynomial Jacobian and composition of checked factor
Jacobians, with exact intermediate basepoint `g(x)` and nominal endpoints.
The shared result is 4x; the dual action is multiplication by 4x. Polynomial
coefficient identities certify the reference's supported symbolic formulas;
the displayed finite basepoint/seed checks are regression observations only.

The branch normalizer has two deliberately small rules: for `if x==0`, compare
the exceptional values exactly and then use the other polynomial everywhere;
for `if x>=0`, either both branch polynomials agree identically or an explicit
nonnegative domain chooses that branch. This is not a general branch AD engine.
`square(abs(x))` is constructed branch by branch and normalized to x².

Each admitted `Rule` is bound to one `Context` and basepoint. The polynomial
constructor uses a stronger whole-domain formula check as sufficient evidence;
`point_from` uses an already verified derivative at the same point plus exact
linear-map equality *at that point*. It does not turn its formula into a
derivative field. The promotion constructor is likewise point-scoped.

The domain catalogue records known mathematical facts about R, `{0}`,
`[0,infinity)` and `(-1,1)`; their Lean justification remains pending. This Python
API is an in-process reference, not an authenticated ownership/evidence store
or hostile decoder. Caller-supplied expected identity/policy data must come from
the actual checked environment in production. It exposes no accepted-Core token.

The 22 regression tests cover the required examples plus domain, basepoint,
revision, environment, nominal endpoint and shape mutations. Existing CI's
`python3 -m unittest discover -s scripts -p 'test_*.py'` includes these tests.
Reference test success does not establish Lean proofs or production compiler
acceptance; neither is implemented by these files.

## 6. Required Lean results (separate from reference test success)

These are proof obligations and reviewed API dependencies, not newly completed
theorems. At the pinned mathlib revision the following building blocks exist:

| Dependency | Location | Role |
| --- | --- | --- |
| `HasFDerivAt.comp` | FDeriv/Comp.lean, line 105 | Ambient chain rule at g(x) |
| `HasFDerivWithinAt.comp`, `.comp_of_tendsto` | FDeriv/Comp.lean, lines 75, 86 | Relative chain rule with MapsTo/local filter premises |
| `HasFDerivAt.congr_of_eventuallyEq` | FDeriv/Congr.lean, line 174 | Transport over an ambient germ equality |
| `HasFDerivWithinAt.congr_of_eventuallyEq` | FDeriv/Congr.lean, line 158 | Relative germ transport with an explicit basepoint equation |
| `HasFDerivAt.unique` | FDeriv/Basic.lean, line 173 | Ambient uniqueness |
| `UniqueDiffWithinAt.eq` | FDeriv/Basic.lean, line 165 | Within uniqueness under its extra premise |
| `HasFDerivWithinAt.singleton` | FDeriv/Basic.lean, line 305 | Any continuous linear candidate on a singleton |
| `HasFDerivWithinAt.hasFDerivAt` | FDeriv/Basic.lean, line 357 | Promotion with S in the ambient neighborhood filter |
| `uniqueDiffWithinAt_Ici` | TangentCone/Real.lean, line 133 | Within uniqueness at the endpoint of a real closed half-line |

Minimal statement/proof sketches, to be elaborated and checked in the pinned
Bridge environment, are:

```lean
-- In real normed spaces E, F, G, with continuous linear maps L, A, B:
-- hf : HasFDerivAt f L x
-- hg : HasFDerivAt g A x
-- hh : HasFDerivAt h B (g x)
-- heq : f =ᶠ[𝓝 x] (h ∘ g)
-- Goal: L = B.comp A
exact hf.unique ((hh.comp x hg).congr_of_eventuallyEq heq)

-- hf : HasFDerivWithinAt f L S x
-- hg : HasFDerivWithinAt g A S x
-- hh : HasFDerivWithinAt h B T (g x)
-- hm : Set.MapsTo g S T
-- heq : f =ᶠ[𝓝[S] x] (h ∘ g)
-- hx : f x = h (g x)
-- hu : UniqueDiffWithinAt ℝ S x
-- Goal: L = B.comp A
exact hu.eq hf ((hh.comp x hg hm).congr_of_eventuallyEq heq hx)

-- hf : HasFDerivWithinAt f L S x; hs : S ∈ 𝓝 x
-- Goal: HasFDerivAt f L x
exact hf.hasFDerivAt hs
```

Required additional proofs are:

1. Real denotation of rational polynomials, exact coefficient normalization,
   differentiation/substitution and the reference's two branch-equality rules.
2. The two concrete derivative routes, the whole-branch identity derivative,
   the point-versus-field distinction for 2x, and the independent derivative of
   `square(abs(x))` despite the unavailable ambient factor rule at zero.
3. The domain facts used by the finite catalogue, including within uniqueness
   on the closed half-line at zero, its failure to be a neighborhood there,
   and singleton nonuniqueness. Keep these as separate propositions.
4. Dualization of linear-map equality and reversed composition, with explicit
   cotangent basepoint transports, for all seeds in the declared finite profile.
5. Independent semantics of selected policies and preservation under a checked
   rewrite. No theorem stating that an arbitrary selected policy is a derivative.
6. Soundness of the **actual** evidence validator and its decoder/registration/
   occurrence binding, using implementation definitions, not this Python model.

Under #285's intended split, reusable propositions belong in `VastitasMath`,
pinned-mathlib models and congruence/uniqueness correspondence in `VastitasBridge`,
and actual-checker soundness in `VastitasOracle`. Ordinary `lean-kernel/` remains
mathlib-free. This does not claim those packages or migrations already exist.

## 7. Actual accepted-Core obligations (#163 / #192)

The current [IndexedAcceptance.lean](https://github.com/MGYamada/Vastitas/blob/e026b89cbdbe6ea2f766cde7d18bdd959f48a007/lean-kernel/VastitasKernel/IndexedAcceptance.lean)
defines `Wire.CheckedInput`, retaining exact decoder and combined-checker
equations. The [IndexedWire oracle](https://github.com/MGYamada/Vastitas/blob/e026b89cbdbe6ea2f766cde7d18bdd959f48a007/lean/VastitasOracle/IndexedWire.lean)
connects actual checked audit/executable Core to typing and finite evaluation;
it explicitly does not prove numerical semantics or native refinement. These
existing guarantees are not derivative-rule acceptance.

A future implementation must establish, for each actual derivative occurrence:

```text
actual acceptance(input, pinned environment, evidence) = returned artifact
  => the occurrence, selected method, primal, domain and evidence are the requested ones
  => the exact returned executable/audit Core satisfies its declared contract
  => every certified pass preserves that contract and its dependencies.
```

For the ambient case, the independent semantic conclusion includes
`HasFDerivAt (denote primalCore) L x` and
`denote backwardCore (eta) = eta o L` at the actual output basepoint, for every
valid eta. For the within case retain S and its distinct property; for selected
backward conclude only the declared policy semantics unless separate derivative
evidence exists. Conditional assumptions remain visible, not silently discharged.

Concrete integration obligations:

- Decode untrusted candidates without deserializing trusted evidence status;
  verify authority and exact subject, model, domain, scalar, point, code and
  theorem identity independently of the producer.
- Connect the mathematical evidence to the actual returned Core and selected
  implementation, including original source mapping, both audit/executable paths,
  inactive or nonwinning registrations where the existing all-body policy applies,
  and any admitted direct Core entry points. Type-correct linear IR alone is insufficient.
- Preserve rejected optional candidates versus required registrations in the
  resolution trace. Do not fabricate successful evidence after falling back.
- Carry primal/germ, factor, basepoint and dual-action proofs through AD and
  rewrites, and invalidate them after relevant function/model/domain/owner/version
  changes. A digest is a binding mechanism, not itself a correctness proof.
- Test tampered Core, swapped proof subjects, stale identities, wrong factor
  basepoints, dropped domain obligations and selected-to-true retagging through
  the actual public check/build path once the feature exists.
- Keep native realization, floating error contracts and ownership/resource
  safety separately established. Exact reference equality is not native refinement.

This adds a narrowly scoped instance of CS-established derivative premises and
CF correspondence. It does not discharge the general CF theorem, identify
analytic Fréchet derivatives with the existing algebraic/Kähler family without
its own bridge, or expand into general differentiability inference or metric work.
