# Exact finite time-reversal reference (#301)

This implements **two selected two-dimensional models over Q(i)** for
[#301](https://github.com/MGYamada/Vastitas/issues/301): a spin-1/2 doublet
and a separately selected spinless two-orbital model. It is Python reference
calculation and regression coverage. It adds no Lean theorem, public `.vast`
feature, accepted-Core connection, empirical verification or classification.
#301's wider design checklist remains open.

## Dependency and reproduction

At preparation, [PR #275](https://github.com/MGYamada/Vastitas/pull/275) was
still an open draft at `6b9a6dd92c2f302b6dccabfc15080c516b2142a7` with no
follow-up discussion. This change is stacked on that exact head. It imports
`Qi`, `Matrix`, matrix validation/construction, multiplication, scaling and
conjugate transpose directly from `car_reference.py`. It does not copy those
operations or rebuild the CAR, Clifford, crossing or Koszul regressions.
The two models here select time reversal independently of tensor statistics.

```sh
python3 scripts/demo_time_reversal_reference.py
python3 -m unittest discover -s scripts -p 'test_time_reversal_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Reference](../scripts/time_reversal_reference.py): explicit semilinear
  actions, independent target selection, phase and basis transport, and
  subject-bound invariance observations.
- [Tests](../scripts/test_time_reversal_reference.py): independent numerical
  witnesses and negative examples, discovered by the existing Python CI.
- [Demo](../scripts/demo_time_reversal_reference.py): full exact operands,
  selected metadata, observed squares, phase/basis transport, Hamiltonian
  and state results, and expected rejection messages as JSON. Rational
  coefficients are numerator/denominator records, never decimal estimates.

Only the Python standard library is needed. No existing CAR/Graph code,
test, compiler, kernel, oracle or CI workflow is changed.

## Selected coefficients, actions and physical interpretation

The coefficient field is Q(i), with the explicit embedding into C sending
its generator to the positive imaginary unit. The rational inclusion and
generator conjugation are recorded separately. Float, Python complex and
Boolean coefficients do not enter the arithmetic. Only this embedding is
supported; a changed embedding payload must not reuse its identity string.
This is exact calculation in a subfield, not a new implementation of C.

Coordinates are column vectors. The Hermitian form is conjugate-linear in
its first argument. Each basis has an ordered pair of labels, a nominal
identity, its actual columns in the model's reference basis, and Gram I.
Only exact orthonormal basis changes are admitted in this reference.

| Selection | Reference basis | Matrix part U | Scalar action | T squared |
| --- | --- | --- | --- | --- |
| Spin-1/2 doublet | up, down | `[[0,1],[-1,0]]` | componentwise conjugation K | -I |
| Spinless two-orbital model | orbital-0, orbital-1 | I | componentwise conjugation K | +I |

These labels describe **assumed physical interpretations** of the selected
mathematical actions. The calculation does not determine which model a
real material has, infer statistics, or assert that every system labeled
spinless uses this particular orbital representation.

For a semilinear pair `(A, sigma)`, application is `A sigma(v)`. Composition
is left after right:

```text
(A, sigma) compose (B, tau) = (A sigma(B), sigma compose tau).
```

The explicit `ScalarAction` enum is identity or conjugation. The matrix of
the inner action is conjugated exactly when the outer action conjugates
coefficients. Tests cover all four scalar-action combinations, including
complex matrices, noncommuting products, associativity and vector execution.
For time reversal, the checks separately inspect matrix unitarity,
`T(i e_j) = -i T(e_j)`, the square's matrix **and** scalar action, and the
selected representative. Complex vector and inner-product tests provide
additional witnesses independent of the original square.

## Phase and basis transport

An overall phase q is an explicitly selected Q(i) element with
`q conjugate(q) = 1`. It changes the representative to `q U K` but leaves
the square unchanged. Tests use `1, -1, i, -i, (3+4i)/5` for both models.
This finite reference does not silently identify representatives or transport
evidence simply because their squares agree.

For `v_reference = B v_new`, the transported action is

```text
U_new = B† U conjugate(B),       T_new = U_new K.
```

More generally, for source and target bases with columns `B_s, B_t`, let
`S = B_s† B_t`; transport `(A, sigma)` to `(S† A sigma(S), sigma)`.
The tests check the commuting application equation, round trips, preservation
of all four composition profiles, phase transport and operator/state transport.

The complex basis `B=diag(1,i)` gives `U_new=-i U` for spin-1/2 and
`U_new=diag(1,-1)` for spinless. The usual linear similarity `B† U B` is
wrong in both cases. A second basis with columns
`[[3/5,4/5],[-4i/5,3i/5]]` also tests mixing; its spinless action matrix is
`[[-7/25,24/25],[24/25,7/25]]`. These expected matrices are independently
fixed in tests rather than obtained by calling the transport implementation.
Nonorthonormal changes are rejected, not treated as unitary by using a dagger
in place of an inverse. General Gram transport is outside this finite profile.

## Independent selection and replay rejection

`check_time_reversal(expected, candidate, observation=None)` requires an
independently supplied `Selection`: full model/carrier/owner/revision and
physical-interpretation record, full basis columns and ordering, coefficient
embedding, full antiunitary profile, and chosen phase. There is no default
that obtains the expected target from the candidate or its report.

The model registry is closed to the two fixtures, and compares the complete
record. The caller can select an explicit orthonormal basis. A candidate
must have exactly the selected coordinate record and the correct transported
matrix and scalar action. The diagnostic name `T` is neither necessary nor
sufficient for acceptance. The profile's square and inner-product payload
cannot be changed while retaining its name.

Observations contain the actual candidate, expected selection and equality
operands. Any supplied report is compared with a freshly recomputed report;
`all_hold`, a profile name or an action name is not accepted as evidence.
The independent selection is trusted *input to this reference API*, not a
newly authenticated source resolver. Python fixture identities and exact
record comparison are not production proof capabilities or cryptographic
tokens. The API does not defend against arbitrary code modifying its own
trusted registry or passing a different target deliberately.

| Negative case | Why it fails despite superficially plausible data |
| --- | --- |
| Drop K from the original real U | U squared is still -I and unitarity passes, but `T(i v)=-i T(v)` and the scalar-action profile fail. |
| Compute ordinary `(i U)^2` after phase change | It gives +I; the actual semilinear square remains -I. The false square report is rejected on recomputation. |
| Reuse spinless evidence for spin-1/2 | Both can be named T and have dimension 2, but model/carrier/basis/profile and square differ. Relabeling the matrix cannot repair the failure. |
| Infer invariant state from symmetric H | For H=I, `T H T^-1=H`; the ground-state projector `P_up=diag(1,0)` goes to `diag(0,1)`. A report for H cannot certify P. |
| Use ordinary linear basis similarity | Complex basis transport requires conjugating the right basis matrix. Correct original-basis tests cannot certify the wrong transported action. |

A further negative matrix `[[0,2],[-1/2,0]]` has semilinear square -I but
fails unitarity: a square is not an antiunitarity test.

## Hamiltonian and state are different subjects

Operator transport under `(A,sigma)` is `A sigma(O) A†`, with unitarity
checked before treating the dagger as the inverse. Hamiltonian subjects
must be Hermitian. Pure-state subjects are Hermitian idempotents of trace 1;
using projectors distinguishes ray invariance from literal vector equality.
For example, spinless K sends `i e0` to `-i e0` while preserving its projector.
A different complex spinless state projector need not be invariant.

`check_invariance` independently receives the actual subject's full matrix,
kind, identity and coordinates. It recomputes the transformation, including
when a prior report is supplied. Changing a Hamiltonian report's subject to
a projector, retaining an object name, or forging a true `holds` value does
not establish the requested invariance. The H=I example is degenerate: it
shows that an individual ground state need not be invariant. It makes no
claim of thermodynamic spontaneous symmetry breaking.

## Status and remaining obligations

| Layer | Status of this change |
| --- | --- |
| Reference computation | Exact Q(i) matrix/vector equations, positive and rejection regressions, and executable JSON demo. |
| Lean proof | None added. Exact arithmetic/embedding correspondence, semilinear composition, antiunitarity and transport soundness still require proofs against the actual definitions. |
| Production Core | No source resolver, Core certificate, checker authority, lowering or native-refinement connection. A future bridge must bind independently resolved identities and methods to the exact accepted Core and preserve all coefficient/basis/profile/subject data. |
| Physical assumptions | Explicitly chosen interpretations of the two finite actions; mathematical acceptance verifies no experimental identification. |

These obligations retain #301's boundary with #204/#223, #278/#279 and
#285 and the existing checker architecture. They do not add a Domain Checker,
constitutional theorem or release gate. Space-group databases, general
projective classifications, magnetic groups and arbitrary physical symmetry
discovery are outside this change.
