# Exact elliptic addition reference (#253)

This is an executable **Python reference and regression suite**, scoped to
`E: y^2 = x^3 - x` over **F5**, and the explicitly listed rational boundary points
`O, (-1,0), (0,0), (1,0)` over **QQ**. It does not enumerate or classify all of
`E(QQ)`. It supplies no public `.vast` API, accepted Core, named `Group` instance,
Lean theorem, or group-scheme implementation.

The reference follows [#253](https://github.com/MGYamada/Vastitas/issues/253)'s
separation between point membership and correct group operations. The issue
also lists a different F5 curve, `y^2=x^3+x+1`, and broader acceptance cases;
those are not implemented here and the issue remains open.

## Run and reproduce

Python's standard library is sufficient; no CAS, float arithmetic or third-party
dependencies are used.

```sh
python3 scripts/demo_elliptic_reference.py
python3 scripts/demo_elliptic_reference.py --json
python3 -m unittest discover -s scripts -p 'test_elliptic_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

| File | Responsibility |
| --- | --- |
| [elliptic_reference.py](../scripts/elliptic_reference.py) | Fixed fields and curve, nominal handles, exact points, guarded addition, evidence replay, exhaustive finite group audit |
| [demo_elliptic_reference.py](../scripts/demo_elliptic_reference.py) | Human-readable table/JSON report and two deliberately invalid slope mutations |
| [test_elliptic_reference.py](../scripts/test_elliptic_reference.py) | Independent group-table oracle, projective enumeration, exception/identity/evidence regressions |
| [f5-y2-x3-minus-x.json](../tests/fixtures/elliptic/f5-y2-x3-minus-x.json) | Complete ordered 8-by-8 addition table, law counts, mutation witnesses, rational boundary results |

The regression compares the generated JSON with that committed record. Existing
CI already discovers `scripts/test_*.py`; no compiler dependency is introduced.

## Total inversion and formula applicability

The project's [mathlib lock](../lean/lake-manifest.json) pins revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Its
[field definitions](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Field/Defs.lean)
include `DivisionRing.inv_zero`. The reference preserves `inv0(0)=0` in both
fields. F5 uses canonical integers in `0..4`; QQ uses `fractions.Fraction`.
Point construction accepts exact integers (and fractions for QQ), then stores
canonical values. Float and Boolean coordinates, and noncanonical raw claims,
are rejected.

`slope_inverse` checks that the denominator is nonzero **before** invoking total
inversion. This is a precondition on using the affine slope formulas, not a
partial definition of field inversion. Addition records the following branches:

| Branch | Condition | Result / applicability |
| --- | --- | --- |
| `left_identity` | Left point is O | Return right point, after validating both subjects |
| `right_identity` | Right point is O | Return left point, after validating both subjects |
| `double_y_zero` | Same affine point and y=0 | O; no inversion evaluated |
| `inverse_pair` | Same x and opposite y, after the previous case | O; no inversion evaluated |
| `tangent` | Same affine point and y nonzero | Slope `(3*x^2-1)/(2*y)`, with checked `2*y != 0` |
| `chord` | Remaining pair | Slope `(y2-y1)/(x2-x1)`, with checked `x2-x1 != 0` |

For the last two branches, `x3=lambda^2-x1-x2` and
`y3=lambda*(x1-x3)-y1`; the result is checked for exact membership again.
Distinct on-curve points with equal x in these two fields are inverse pairs,
so all admitted pairs reach a valid branch. The exceptional branches explicitly
precede any affine division.

O is represented by a tagged `None` coordinate, denoting `[0:1:0]` on
`Y^2 Z = X^3 - X Z^2`. It is not an unindexed global point and is never confused
with the affine point `(0,0)`. The tests independently enumerate homogeneous
triples over F5: 32 nonzero representatives modulo the four nonzero scalars
give precisely the eight points, with exactly one point at infinity.

The fixed discriminant is `-16*(4*(-1)^3)=64`, hence 4 over F5. It is attached
to the selected short presentation and exact field. The reference supports no
coefficient parameter, general Weierstrass model, or coordinate change.

## Full F5 table and independent expected values

| + | O | (0,0) | (1,0) | (2,1) | (2,4) | (3,2) | (3,3) | (4,0) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| O | O | (0,0) | (1,0) | (2,1) | (2,4) | (3,2) | (3,3) | (4,0) |
| (0,0) | (0,0) | O | (4,0) | (2,4) | (2,1) | (3,3) | (3,2) | (1,0) |
| (1,0) | (1,0) | (4,0) | O | (3,3) | (3,2) | (2,4) | (2,1) | (0,0) |
| (2,1) | (2,1) | (2,4) | (3,3) | (0,0) | O | (1,0) | (4,0) | (3,2) |
| (2,4) | (2,4) | (2,1) | (3,2) | O | (0,0) | (4,0) | (1,0) | (3,3) |
| (3,2) | (3,2) | (3,3) | (2,4) | (1,0) | (4,0) | (0,0) | O | (2,1) |
| (3,3) | (3,3) | (3,2) | (2,1) | (4,0) | (1,0) | O | (0,0) | (2,4) |
| (4,0) | (4,0) | (1,0) | (0,0) | (3,2) | (3,3) | (2,1) | (2,4) | O |

The tests compare all 64 entries with a separate `C4 x C2` table oracle. Its
coordinate dictionary is fixed by `G=(2,1)` and `H=(1,0)`: the tangent at G has
slope 3 and gives `2G=(0,0)`; the chord through G,H has slope 1 and gives
`G+H=(3,3)`; the horizontal chord through `(0,0),H` gives `(4,0)`; inversion
negates y. The resulting dictionary maps `(i,j)` to `iG+jH` and builds expected
entries by integer addition modulo 4 and 2. It does not call the implementation's
addition, inverse, enumeration or auditor to compute expected entries. This
oracle is regression data with an explicit mathematical interpretation, not
a Lean proof of that interpretation.

The exhaustive audit uses every point in the independently enumerable F5
carrier. It does not accept a caller-selected sample or subset. It checks 64
ordered closure cases, 512 associativity triples, 64 commutativity pairs, and
8 cases each for left/right identity and left/right inverse. All pass for the
reference operation. `check_f5_group` reconstructs the table and all checks;
it never accepts a caller-supplied success report as evidence.

## Why membership is insufficient

The demo includes an intentionally incorrect `slope_only_mutant`: it preserves
identity handling but replaces all affine exceptional branches with slope
formulas evaluated using total inversion. For `P=(0,0)` it computes
`lambda=(-1)*inv0(0)=0` and returns **P instead of O**, over both F5 and QQ.
P still satisfies the curve equation, but `P+(-P)=O` fails. Replaying an addition
claim with that on-curve result is rejected as `ADDITION_MISMATCH`.

The unrestricted mutation does **not** preserve membership everywhere: doubling
`(1,0)` over F5 gives the off-curve `(3,0)`. The regression records that fact
rather than claiming all 64 naive outputs pass membership.

For the stronger negative control, `isolated_zero_torsion_mutant` substitutes
that same slope-only formula **only for P+P**, leaving all other entries correct:

| Property | Correct addition | Isolated slope mutation |
| --- | --- | --- |
| Closure / membership | 64/64 pass | 64/64 pass |
| Left/right identity | 8/8 each pass | 8/8 each pass |
| Left/right inverse | 8/8 each pass | 1 failure each, at P |
| Commutativity | 64/64 pass | 64/64 pass |
| Associativity | 512/512 pass | 24 failures among 512 triples |

For `H=(1,0)`, writing the mutated operation as `*`, a concrete witness is
`(P*P)*H=(4,0)` but `P*(P*H)=H`. Every intermediate point is on the curve.
The group check rejects this operation with `GROUP_LAW_FAILURE`.

## Nominal subjects and evidence replay

`Field`, `Curve`, and `Model` are separate immutable in-process handles with
object identity, not structural equality. Their names are display labels only.
Constructing another handle with exactly the same label and equation still
creates a distinct subject. A point retains its model, which retains its curve
and coefficient field. Even O retains these indices. Neither coefficient
equality, equal coordinates, nor an isomorphic presentation authorizes mixing.

Model evidence binds the discriminant to that presentation. Membership evidence
binds its point and exact residual. Addition evidence binds the exact model,
ordered input points, result, branch, denominator and slope. Every evidence check
recomputes the requested arithmetic and compares its subject and payload;
points and evidence from another field, curve, presentation or input pair are
rejected. Both input points are checked before identity shortcuts. Tests also
reject substituted on-curve results, forged denominators, altered branch names,
bad residuals, foreign result points and Boolean scalar claims.

This is an in-process reference API, not serialization of declaration authority
or a hostile-Python security boundary. Bypassing frozen dataclasses or changing
the Python implementation is outside its trust model. Rebuilding a claim for
a new subject and recomputing every obligation is a fresh reference check, not
transport of the old evidence. The JSON report is an observation with display
labels; it cannot be imported as nominal authority. `Model` denotes a coordinate
presentation here; it is **not** the future named `Group` model.

## Verification and integration obligations

| Layer | Established here | Remaining obligation |
| --- | --- | --- |
| Exact reference arithmetic | Canonical F5 / Fraction computations; explicit exception branches; QQ boundary `2(0,0)=O`; discriminants 4 and 64 | No general field, general curve or general rational-point API |
| Finite group laws | The complete F5 table, all listed laws, independent expected table and mutation witnesses | No uniform theorem over bases, families or arbitrary points |
| Lean mathematical semantics | `inv0(0)=0` follows the pinned definition's convention | Formalize this exact carrier/operation and prove branch completeness, nonzero-denominator applicability, membership preservation and group laws; connect the reference to those definitions |
| Named `Group` model | Nominal subject checks are exercised in Python | Bind the actual carrier, chosen operation, owner/declaration identity and Lean evidence to one named structure (#204); no coordinate-based model conflation or reuse of stale evidence |
| Accepted Vastitas Core | No source, IR, checker or code-generation changes | Resolve actual declarations and endpoints through the existing checkers; independently validate source/typed-IR/direct forged-Core cases; prove the relation for the **exact returned Core** and executable operations |
| Scheme and base change | A fixed short-model point representation and explicit infinity | Relate points to `Point<E,T>` with the geometric test object and base map; prove the relevant structural maps and any transport instead of treating a field marker as T |
| Native execution | Python regressions only | Runtime/native refinement and performance measurements remain separate from reference checks and kernel proofs |

Future Lean work must use the actual implementation definitions and preserve
the existing kernel/oracle boundary; a separately copied mathematical model
does not establish acceptance of the compiled operation. This work adds neither
a ninth Domain Checker nor an elliptic compiler opcode. The finite reports do
not discharge #253's full acceptance checklist.

General rings, arbitrary bases, general Weierstrass equations in characteristics
2 or 3, reduction/base-change machinery, model isomorphisms, scalar-multiplication
APIs, cryptographic subgroup approval and constant-time guarantees are outside
this reference. The Python branches and arithmetic make no constant-time claim.
