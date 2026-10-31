# Exact polynomial first-variation reference

This is an **external Python reference** for the first boundary-term examples in
[#305](https://github.com/MGYamada/Vastitas/issues/305). It compares two finite
exact calculations and rejects malformed or mismatched evidence. It does not
implement `std::analysis::variational`, general function-space differentiation,
Lean soundness, or acceptance by Vastitas's actual source/checked-Core path.
The broader issue remains open.

## Supported mathematical profile

One real scalar path `q(t)` and one variation `eta(t)` on the positively oriented
interval `[0,1]`, both represented by `Q[t]`. A first-order Lagrangian is an
arbitrary finite rational polynomial `L(t,q,v)` with `v=q'`. The roles `t,q,v`
have an explicit ordered permutation in every Lagrangian; arity alone does not
establish variable identity. There are no rational-function denominators or
nonpolynomial operations. Rational coefficients have their usual real
interpretation; floats and bools cannot stand in for exact evidence scalars.

The action and its first variation for the supplied pair are

```text
S(q)             = integral_0^1 L(t, q(t), q'(t)) dt
delta S_q(eta)   = [epsilon^1] S(q + epsilon*eta).
```

For this finite polynomial perturbation, the action is a polynomial in epsilon.
Extracting its linear coefficient is an exact calculation, not a finite
difference or a sampled derivative. The result is the **scalar evaluation of a
linear functional at eta**, not a tangent vector or gradient. No metric, Riesz
identification, inner product or conjugation is selected.

The two supported variation spaces are unrestricted polynomial variations and
polynomial variations with `eta(0)=eta(1)=0`. A fixed-endpoint request checks
both values, with exact arithmetic, before either computation. The endpoints
of `q` need not be zero. Other constraints, support conditions and variation
spaces are not inferred. In particular, zero boundary contribution does not
prove fixed-endpoint admissibility: the two nonzero boundary values could
cancel, or the momentum could vanish.

## Arithmetic reuse and dependency status

[#281](https://github.com/MGYamada/Vastitas/pull/281) owns the introduction of the
[arity-aware shared Poly](../scripts/rational_polynomial_reference.py), the
symplectic extraction and the four-variable compatibility checks for both
symplectic and metric consumers, including zero polynomials. This increment
depends on that change and contains no second extraction or polynomial type.
It does not import the SOS producer/verifier. The shared compatibility tests
live in `test_rational_polynomial_reference.py` alongside the common arithmetic.

The integral-enclosure reference in
[#315](https://github.com/MGYamada/Vastitas/pull/315) also reuses #281. Its
univariate coefficient antiderivative, partition and local-error checks remain
independent of the variation and boundary-term checks here. The small shared
[polynomial calculus module](../scripts/rational_polynomial_calculus.py) adds
simultaneous substitution, exact evaluation and coefficientwise integration
using the same Poly. Integration removes the selected variable and preserves
the order of the remaining parameters. It uses the monomial rule
`c*(b^(n+1)-a^(n+1))/(n+1)`. Its arithmetic primitive supports rational endpoints;
the variational consumer deliberately accepts **only `[0,1]`**.

This is no integral-enclosure verifier, approximation/error-bound framework,
adaptive quadrature or additional AD engine. Differentiation uses the existing
`Poly.derivative` operation. Both computation routes share this arithmetic, so
their agreement is not independent verification of Python or the common
polynomial implementation. Primitive regressions separately test the
fundamental theorem on a finite polynomial family, parameter ordering, exact
small fractions and a polynomial with zero endpoint samples but nonzero integral.

## Two calculation routes

1. `direct_first_variation` substitutes `q+epsilon*eta` and
   `q'+epsilon*eta'` into the **whole** Lagrangian in `Q[t,epsilon]`, integrates
   out `t`, retains the full `Q[epsilon]` action, and extracts its linear
   coefficient. It never differentiates L or calls the bulk/boundary route.
2. `bulk_boundary_first_variation` independently computes the partials `L_q`
   and `L_v`, substitutes the actual path, and differentiates the substituted
   `L_v` in `t`. This retains explicit time dependence and acceleration terms.
   It returns the full polynomial coefficient and the separate contributions:

```text
p(t)       = L_v(t, q(t), q'(t))
EL(t)      = L_q(t, q(t), q'(t)) - d_t p(t)
bulk       = integral_0^1 EL(t) * eta(t) dt
boundary_0 = p(0) * eta(0)
boundary_1 = p(1) * eta(1)
boundary   = boundary_1 - boundary_0
delta      = bulk + boundary.
```

The boundary is **always computed**, even for fixed endpoints. Its value is
never replaced with zero on the strength of a tag. `EL` follows the stated
minus sign convention; for `L=(v^2-q^2)/2` it is `-q''-q`. The local equation
`EL=0`, the scalar first variation on a selected eta, and stationarity over
an entire admissible space are different statements. The API does not infer
stationarity from a zero coefficient or one zero first variation.

## Evidence and independent request binding

`propose` supplies the bulk/boundary decomposition and the variation endpoint
values. `verify(expected_subject, evidence)` first requires equality with an
**independently supplied** Subject, then recomputes admissibility, both routes,
and every supplied component. It compares the entire EL polynomial, bulk,
both oriented endpoint contributions, boundary difference and final total
separately. A compensating wrong bulk and boundary cannot pass by preserving
the sum. A mocked incorrect decomposition is also caught by the direct route.

The subject binds the named Lagrangian and defining revision, actual
coefficients, variable order, path and variation coefficients, exact interval,
admissible variation space, environment, configuration identity, scalar profile
and reference ruleset. Equal numerical answers do not erase these distinctions.
Changing the Lagrangian by a constant or swapping symmetric variable roles
still invalidates old evidence. Different intervals are rejected both as stale
subjects and, after relabelling, as unsupported profiles.

Changing both the expected subject and the evidence label is not a shortcut:
all content is recomputed. Correct freshly recomputed evidence for another
supported subject can of course pass. IDs/revisions here are **fixture data**,
not authenticated proof declarations. Frozen Python dataclasses do not confer
authority; consumers must call `verify` again rather than trust a constructed
`Evidence` or `ReferenceCheck`. The returned result retains the exact expected
subject and freshly computed values.

## Reproduction and regressions

Only Python's standard library is needed. From the repository root:

```sh
python3 -S scripts/demo_variational_reference.py
python3 -m unittest discover -s scripts -p 'test_variational_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_rational_polynomial_calculus.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
git diff --check
```

The demo emits exact rational strings in JSON. Existing CI discovers the new
tests through its current `test_*.py` pattern.

| L; q; eta | EL along q | Direct first variation | Bulk | Boundary |
| --- | --- | --- | --- | --- |
| `q*v`; `t`; `t` | `0` | `1` | `0` | `1` |
| `q*v`; `t`; `t*(1-t)` | `0` | `0` | `0` | `0` |
| `(v^2-q^2)/2`; `t`; `t*(1-t)` | `-t` | `-1/12` | `-1/12` | `0` |
| `q*v`; `t+2`; `1` | `0` | `1` | `0` | `3-2` |
| `t*v`; `t`; `t*(1-t)` | `-1` | `-1/6` | `-1/6` | `0` |
| `v^2/2`; `t^2`; `t*(1-t)` | `-2` | `-1/3` | `-1/3` | `0` |

The tests also include 80 nonlinear Lagrangian/path/variation combinations,
all six correctly reindexed variable orders, a finite family of total
derivatives, rational linearity in eta, constant/linear Lagrangians, the full
epsilon action, and a nonzero boundary as small as `10^-30`.

Negative cases cover omitted/reversed boundaries, wrong lower-endpoint signs,
swapped endpoint values, wrong EL signs, forged totals and compensating errors,
forged fixed-endpoint tags/traces, inadmissible variations with zero boundary,
and stale Lagrangian identity/revision/body, interval, variable order, variation
space, path, eta, environment or configuration. A relabelled variation with the
same endpoint traces still has its interior contribution recomputed.

## Remaining obligations

| Layer | Status and obligation |
| --- | --- |
| Finite Python reference | Exact coefficient/endpoint calculations and instance equality for tested inputs, plus mutation rejections. This is executable evidence, not a universal formal proof. |
| Polynomial mathematical semantics | Prove soundness of substitution, partial/total differentiation and integration over the real interpretation; prove coefficient extraction gives the derivative of the finite polynomial action and the bulk-plus-boundary identity with its sign. |
| General function spaces | Separately select configuration/test-function spaces, topology, regularity, integrability, continuity/linearity of the derivative, boundary traces and justified differentiation under the integral/integration by parts. No extension from finite tests is automatic. |
| Lean soundness | Formalize the actual supported implementation and prove acceptance implies the independently defined first-variation statement and the actual endpoint premises. Under #285, separate mathematical definitions, implementation soundness and pinned-mathlib correspondence. No new axioms or proof completion are supplied here. |
| Actual accepted Core | Resolve/authenticate definitions, revisions, ordered roles, domain and admissible spaces from the real environment; bind the verified result to the exact returned Core; reject forged, stale and swapped evidence through real source/IR acceptance. No source or Core variational feature currently follows from this reference. |
| Native realization | Any later backend needs a separate refinement/rounding contract. Exact Python arithmetic says nothing about native numerical error or performance. |

No ODE/PDE solving, general jet-bundle construction, Noether theorem, constrained
stationarity solver, higher-order/vector/multidimensional action, infinite
domain, integral enclosure or alternative differentiation engine is added. The
existing 8 Domain Checkers plus Ownership/Borrow Checker and CS/MS/CF remain the
architectural framework; this reference creates no additional checker or
constitutional theorem.
