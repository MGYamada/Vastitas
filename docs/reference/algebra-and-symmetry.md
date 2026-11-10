# Algebra, order and symmetry reference models

These independent exact models exercise finite algebraic structures: canonical anticommutation relations and spin, antiunitary time reversal, spectral pairs of small Hamiltonians, and finite orders and lattices. Each has its own hypotheses, verifier and regression examples.

<a id="car-spin-reference"></a>

## Exact finite CAR and ordinary-spin reference (#246)

This is the first executable physics example for
[#246](https://github.com/MGYamada/Vastitas/issues/246), using the crossing
reference associated with [#201](https://github.com/MGYamada/Vastitas/issues/201)
and the super/Koszul obligations in
[#245](https://github.com/MGYamada/Vastitas/issues/245).
It covers **one/two modes only**, independent spin sites, and the two/three
Pauli generator images. It is a Python matrix observation, not `.vast`
execution, a Lean proof, an implemented stdlib algebra, or production Graph
authority. #246 remains open; its wider acceptance checklist is not completed.

### Run and inspect

```sh
python3 scripts/demo_car_reference.py
python3 -m unittest discover -s scripts -p 'test_car_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_graph_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

- [Reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/car_reference.py): exact scalars, matrices, closed
  named models, explicit adjoints, finite observations and rank witnesses.
- [Demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_car_reference.py): JSON containing the full model,
  ordered basis, grading, operator matrices and relation operands, plus all
  four requested negative examples. Fractions are numerator/denominator
  records; complex coefficients are pairs of exact fractions.
- [Regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_car_reference.py): CAR, ordinary spins,
  Pauli images, metadata mutations and the separation from Graph authority.

Only the Python standard library is needed. The existing CI discovers
`scripts/test_*.py`, including these tests and the unchanged
[`test_graph_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_graph_reference.py) suite.
No compiler, kernel, proof-oracle or workflow change is required.

### Coefficients, ordered bases, adjoint and models

The executable coefficient field is **Q(i)**, not an inexact implementation
of C. A scalar is `(a,b)` with `a,b : Fraction` and `i^2=-1`. The model records
the embedding `Q(i) -> C` sending `i` to the positive imaginary unit.
Float, Python `complex`, and Boolean coefficients are rejected.

Matrices act on column vectors; row is output and column is input.
The first site is the most significant bit. Kronecker coordinates have the
right index varying fastest.

| Item | CAR model | Physical spin model |
| --- | --- | --- |
| One-site ordered basis | `(0),(1)` | `(0),(1)` |
| Two-site ordered basis | `(00),(01),(10),(11)` | `(00),(01),(10),(11)` |
| Local basis parity | `(0,1)` | `(0,0)` (trivial grading) |
| Two-site basis parity | `(0,1,1,0)` | `(0,0,0,0)` |
| Generator exchange degree | `c`, `c†` odd | site `X,Y,Z` even |
| Named tensor interpretation | `SuperVec_QQ(i):Koszul` | `Vec_QQ(i):ordinary` |
| Existing scalar-line profile | `symmetric_sign`, `q=-1` | `symmetric_one`, `q=1` |

Each immutable `Model` retains model/owner/carrier/interpretation/revision,
the coefficient field and embeddings, full `graph_reference.ProfileKey`,
ordered basis, grading and adjoint profile. A closed fixture registry rejects
changed fields, basis reorderings, erased parity, stale revisions and
cross-profile substitution. These are fixture identities, not authenticated
resolver identities or Lean evidence.

The graph profiles **keep their original QQ coefficient and graded-line
category IDs**. They supply scalar exchange observations, not a claim that
the existing checker already implements SuperVec over Q(i). The explicit
`QQ -> QQ(i)` embedding transports those rational coefficients for the
matrix computation. It transports no law evidence or rewrite permission.
The full categorical/model bridge remains an obligation below.

Adjoint requires an explicit `AdjointProfile` argument tied to the same
model, the involution `a+bi -> a-bi`, and the specified orthonormal ordered
basis with Gram matrix I. It is conjugate transpose in this realization.
No quadratic form or Symmetric capability supplies a dagger or positivity.
The standard positive Hermitian realization under the stated embedding is
chosen here; the Python profile is not a proof of positivity. Missing,
transpose-only, other-model and unsupported inner-product profiles fail.

### Finite observations and negative examples

Let `R=[[0,1],[0,0]]` and `Z=diag(1,-1)`. The one-mode annihilator is `R`.
For two modes, `embed_local` moves the local homogeneous action past the
occupied first factor using **`graph_reference.make_word` and `evaluate`**.
There is no second Koszul/Jordan-Wigner sign formula. The resulting matrices
are checked independently against

```text
c1 = R tensor I      c2 = Z tensor R
c2 |01> = |00>      c2 |11> = -|10>
```

Explicit adjoints give the creators. `observe_car` checks every ordered
pair `(i,j)` in each of the three CAR families: 3 equalities for one mode
and 12 for two modes. Its report includes the actual candidate operators,
their adjoints, and both sides of every equality. It does not recognize
arbitrary candidate matrices as the canonical Fock generators simply
because they satisfy CAR.

| Negative example | Exact failure |
| --- | --- |
| Drop `Z`, set `c2=I tensor R` | The six diagonal single-mode relations still hold; all six cross-mode relations fail. In particular `{c1,c2}=2 R tensor R != 0`. |
| Insert a fermionic prefix on spin site 2, `X2=Z tensor X` | Both site squares remain I, but `[X tensor I, Z tensor X] != 0`. The correct `I tensor X` commutes; falsely imposing an odd exchange on the correct pair gives `{X1,X2}=2 X tensor X != 0`. |
| Reuse the other tensor profile's evidence | The existing `graph_reference` rewrite checker rejects it, in both directions, even though both selected profiles are Symmetric and both double-crossing scalars equal 1. |
| Identify `Cl3(C)` with `Mat2(C)` through Pauli images | The 8 ordered standard-word images have rank 4, with kernel witness `e1e2e3-i*1`; their images satisfy `XYZ=iI`. |

The Pauli check fixes `q=sum(x_j^2)` and verifies square-one generators and
pairwise anticommutation. The four images `1,X,Y,XY` for `Cl2` are independent;
the eight images `1,X,Y,Z,XY,XZ,YZ,XYZ` for `Cl3` are not. Gaussian elimination
uses Q(i) throughout. Under the recorded field embedding, the matrix ranks
are unchanged by extension to C: the same minors vanish or remain nonzero.
The universal Clifford construction and PBW basis theorem are mathematical
inputs to that interpretation, not newly proved by listing these words.
`require_independent_images` is only a necessary rank check, not an
isomorphism verifier.

In particular, the abstract Clifford generators are odd, but the Pauli
operators in the **physical spin** realization have trivial exchange
grading. The three-generator Pauli map is an ungraded representation;
its kernel witness relates abstract odd and even parts. Abstract Clifford
parity and a matrix-algebra identification never select fermionic statistics
for separate spin sites.

### Observation is not rewrite authority

`MatrixObservation.all_hold` means exactly that these finite matrices satisfy
the listed equations. Nothing in `car_reference` issues Graph evidence,
defines a new rewrite, or consumes/produces `Indexed.Core`.

The existing structural whitelist and fixture evidence checker remain in
[`graph_reference.py`](https://github.com/MGYamada/Vastitas/blob/main/scripts/graph_reference.py). The new tests use
them directly for same-profile double cancellation, rejection of single
crossing deletion, and cross-profile evidence rejection. A matrix report
cannot substitute for `FixtureEvidence`. Tests disable both matrix and
scalar evaluation while structural replay succeeds, and mutate the shared
sign evaluator so that the independent CAR matrix equalities fail.

Even successful structural replay in Python is **reference replay**, not
production authority. Odd creation/annihilation operations are matrix
observations with explicit degree metadata; they are not silently inserted
as ordinary even morphisms into the Graph crossing fragment. There is no
general homogeneous-map interchange rule here.

### Remaining connections and proof obligations

These extend [the existing Graph obligations](../verification/core-models.md),
not the completed theorem set:

1. **Named models (#204):** resolve the actual algebra/carrier, exact base,
   chosen tensor, selected method/revision, owner and interpretation from
   source. Bind basis/gradation and dagger evidence to that model; do not
   identify ordinary and super tensors from equal dimensions or coordinates.
2. **Algebra and representation (#246):** establish the finite Fock/CAR
   realization, universal Clifford lift and the required PBW facts. Prove
   the Q(i) embedding, exact matrix arithmetic and explicit involution/inner
   product correspondence; distinguish the faithful Cl2 representation
   from the Cl3 quotient. Finite tests alone do not establish these theorems.
3. **Super semantics (#245):** derive the parity-sector exchange and the
   scalar-line observation bridge from a certified super symmetric model.
   Connect odd operators through parity-shifted endpoints, or separately
   verified homogeneous-map superinterchange. Preserve scalar signs and
   grading through all selected tensor/method operations.
4. **Actual acceptance (#184/#192):** connect source selection to the exact
   returned `Indexed.Core`, retaining the same model, coefficient, parity,
   adjoint, operands and selected profile across lowering/optimization.
   Evidence must bind that accepted input and returned Core, not a parallel
   synthetic program or a report of equal matrices.
5. **Lean soundness:** implement the supported checks in the mathlib-free
   kernel and prove soundness against the actual definitions from the
   proof-only oracle. Derive real `Graph.Authority` law evidence and method
   realization; never promote these fixture tokens or `all_hold` to proofs.
   Existing conditional Graph theorems, source correspondence, native
   refinement and Ownership/Borrow obligations retain their separate scope.

General Clifford normal forms, arbitrary rank, exterior/PBW implementations,
infinite-mode CAR and C*-completions are outside this change. There is no
new top-level Domain Checker, public wire protocol, or release condition.

<a id="order-reference"></a>

## Finite order, lattice and Galois connection reference

This is the executable **finite reference** for [#294](https://github.com/MGYamada/Vastitas/issues/294).
It does not implement `std::order`, add a checker, certify accepted Vastitas Core,
or complete any Lean theorem. It introduces no set library or sort algorithm.

The baseline inspected was main `cd09ad9be313b9068ec38065356d954dfed8d4d7`.
The issue had no comments, and searches for its number, `std::order`, and
Galois implementations found no corresponding follow-up PR. The existing
`HasOrder` capability in `lean-kernel/VastitasKernel/Dispatch.lean` concerns
finite scalar dispatch; it is not a public named order/lattice/adjunction API.
This reference follows the existing independent Python probes in `scripts/`.

```sh
python3 -S scripts/demo_order_reference.py
python3 -m unittest discover -s scripts -p 'test_order_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

The demo emits JSON and exits zero only when all positive and negative
expectations match. The existing Python CI discovery includes the tests.
Only the Python standard library is required. The three files are
[the verifier](https://github.com/MGYamada/Vastitas/blob/main/scripts/order_reference.py),
[literal fixtures and demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_order_reference.py), and
[regressions](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_order_reference.py).

### Finite representation and acceptance

An `Order` contains an immutable, square **Boolean relation table** on at most
eight distinct string-labelled elements. The labels identify enumerated atoms;
the verifier does not parse `"{0}"`, `"-1"`, or `"NaN"` as mathematics. The table's
entry `le[i][j]` means **element i <= element j**. Its transpose defines a
different relation. Carrier equality is equality of atom indices; induced
preorder equivalence `le[i][j] and le[j][i]` never changes that equality.

The caller independently supplies the required law and the complete expected
subject. `verify(expected, Claim(candidate_subject, claimed_law), law=required)`
first compares both, then enumerates the mathematical conditions again.

| Profile | Conditions checked from the supplied data |
| --- | --- |
| `preorder` | Reflexivity and transitivity |
| `partial_order` | Preorder conditions and antisymmetry using carrier equality |
| `linear_order` | Partial-order conditions and comparability of every pair |
| `bounded_lattice` | Partial order, both binary universal properties, bottom and top |
| `monotone` / `antitone` | Preorders at both endpoints and the indicated implication for every pair |
| `galois` | Preorders, both monotonicity laws, adjunction, unit and counit, each independently evaluated |
| `order_iso` | Preorders, both monotonicity laws, both literal inverse equations, and order preservation/reflection |
| `binary_joins` / `binary_meets` | Partial orders, monotonicity, existence and preservation of every requested binary bound |
| `all_joins` / `all_meets` | The same checks for **every subset of the finite source**, including the empty subset |

The empty carrier is permitted for order profiles: the four laws hold
vacuously. It cannot supply bottom or top, and fails `all_joins`/`all_meets`
at the empty family. A zero count on the binary profile is only a vacuous
binary statement, never a completeness claim. No profile is inferred from
a comparator name or a successful comparison.

The supplied lattice operations must satisfy, for every a,b,z,

```text
join(a,b) <= z  iff  a <= z and b <= z
z <= meet(a,b)  iff  z <= a and z <= b.
```

These universal properties are checked against the actual relation. The
verifier does not assume that a commutative operation, or an arbitrary upper
or lower bound, is a join or meet. Nonunique bounds in a preorder are not
silently resolved by carrier equality: the lattice and preservation profiles
explicitly require partial orders. Galois connections themselves accept
preorders. Preservation up to preorder equivalence is outside the current
preservation profile.

For preservation, the verifier searches the relation table independently for
each least upper/greatest lower bound. It does **not** trust the fixture's
join/meet tables or infer preservation from an adjunction flag. Every requested
source bound and corresponding target image bound must exist; a missing bound
is an error, not a skipped successful check. `all_joins` alone does not certify
all meets or all target joins unrelated to image families. These bounded
enumerations are not an API for infinite or arbitrary indexed families.

### Binding and trust boundary

The following data participate in exact subject comparison:

| Subject | Bound fields |
| --- | --- |
| Order | Context snapshot, nominal carrier, order name, revision, ordered atom labels, entire oriented relation table |
| Map | Name and revision, full source and target orders, every image index |
| Adjoint or inverse pair | Both complete maps in their declared lower/upper roles, with exactly matching opposite endpoints |
| Lattice | Complete order, every proposed join/meet table entry, bottom and top |
| Request | The law independently required by the consumer |

This permits multiple named orders on one carrier. Even two identical tables
with different order names cannot replay the same candidate. Reusing a name
with an altered table, reversing its orientation, changing the revision,
reordering atoms, changing a map, or downgrading the requested law also fails.
For example, the valid usual order relabelled `absolute-value` cannot provide
antisymmetry evidence for the independently selected absolute-value relation.
Rebinding the candidate to the latter still causes its antisymmetry check to fail.

There are no accepted flags, model-name registry lookups or cached proofs.
`Claim` is an untrusted payload. Successful verification returns enumeration
counts; failure raises `Invalid` with a code and first counterexample in
deterministic index order. The raw `inspect_order` / `inspect_connection`
functions report independent law checks and confer no bound acceptance.
For preservation failures the witness is `(family, image_of_bound, bound_of_images)`.

This is an in-process reference, not a hostile-Python or authenticated namespace
boundary. The caller must obtain the expected subject independently of the
candidate. Passing the candidate as its own expected target cannot establish
provenance. Strings do not establish ownership or actual Core identity.
Rebinding a lawful candidate and recomputing all laws for a new expected target
is a fresh finite check, not transfer of an existing proof. Python mutation
bypasses, production decoding, cryptographic receipts and namespace resolution
remain outside the reference.

### Reproduced examples and independent regressions

For the constant function `f:{0,1}->{x}`, the literal fixtures encode the
powerset orders, direct image `l=f_!` and inverse image `u=f*`.

| Checked statement | Enumeration / result |
| --- | --- |
| `l(S) <= T iff S <= u(T)` | All 4 x 2 = **8** pairs |
| Unit `S <= u(l(S))` | All **4** source elements |
| Counit `l(u(T)) <= T` | All **2** target elements |
| Left-adjoint binary join preservation | All 4 x 4 = **16** pairs |
| Right-adjoint binary meet preservation | All 2 x 2 = **4** pairs |
| Left-adjoint joins of all finite subsets | **16** families, including empty |
| Right-adjoint meets of all finite subsets | **4** families, including empty |
| False left-adjoint meet preservation | `l({0} intersect {1})={}` but `l({0}) intersect l({1})={x}` |
| False inverse law | `u(l({0}))={0,1}`, not `{0}` |

The binary and all-subset counts happen to agree in this example but represent
different quantifications. A constant-top map of the two-element chain
preserves binary joins and fails empty-join/bottom preservation; constant-bottom
similarly fails empty-meet/top preservation.

Further regressions cover:

- The absolute-value relation on `{-1,0,1}`: a preorder, with `-1` and `1`
  mutually related but distinct. Antisymmetry and linear-order claims fail.
- Divisibility on `{1,2,3,6}`: a partial order with incomparable 2 and 3;
  a cyclic comparator; strict comparison misused as reflexive comparison;
  and an ordinary floating comparison table containing a NaN diagonal.
- **All 512 Boolean relations on three labelled atoms**, compared with an
  independent set-composition oracle: 29 preorders, 19 partial orders,
  6 linear orders.
- **All 256 pairs of total maps** between the two fixed powersets, compared
  with actual Python set inclusions independently of the relation tables:
  exactly four are adjoint pairs. Each accepted pair also passes the separate
  all-subset left-join and right-meet tests.
- A pair of monotone constant maps with false adjunction, unit and counit;
  and a pair satisfying unit/counit without monotonicity that fails adjunction.
- The diagonal/meet adjunction between a two-element chain and its square:
  the right adjoint preserves meets but fails binary join preservation. This
  detects a direction error that inverse image alone would miss, since that
  particular right adjoint also preserves joins.
- A connection on the indiscrete two-element preorder whose composites are
  equivalent to the identity but are not equal to it; literal isomorphism
  acceptance fails.
- Swapped adjoints, a reversed endpoint relation, and positive **correct
  duality**, which reverses both orders and exchanges lower and upper maps.
- A genuine order isomorphism between distinct usual/reversed named orders,
  without identifying their nominal model records.
- Forged bound operations, missing joins/meets, all subject-binding mutations,
  and malformed tables/maps, including integer truth values and Boolean indices.

These are complete enumerations of the indicated finite domains, not random
sampling, general decision procedures or proofs of the Python implementation.

### Remaining obligations

1. **Finite checker soundness in Lean.** Formalize table denotation, atom equality,
   exact subject/law binding and complete enumeration. Prove that the *actual*
   checker acceptance establishes each advertised law for its full finite
   domain, including the empty-family cases and counterexample meanings.
   No Lean file or new axiom is introduced here.
2. **General order theory.** Establish the selected Lean/mathlib counterparts
   (`Preorder`, `PartialOrder`, `LinearOrder`, `Lattice`, `CompleteLattice`,
   `Monotone`, `Antitone`, `OrderHom`, `OrderIso`, `GaloisConnection`) under
   #278/#285. Prove the general adjunction consequences, preservation of existing
   suprema/infima with the necessary hypotheses, equivalence-versus-equality
   distinctions for preorders, and duality. Infinite structures, arbitrary
   indexed joins/meets, quotient constructions, Galois insertions/coinsertions,
   frames/locales and ordered algebra are not implemented by this probe.
3. **Actual accepted Core and evidence provenance.** Independently resolve the
   caller-selected named model, carrier/equality, oriented relation and maps
   from the actual source occurrence and environment. Link them to the exact
   returned Core and audit trace; prove denotation correspondence and prevent
   replay across models, contexts, revisions, endpoints and law profiles.
   A separately checked Python record or lookalike Core is insufficient.
4. **Existing jurisdictions and realization.** Reuse the established eight
   Domain Checkers and independent Ownership/Borrow checker. Connect #256,
   #263 and #257 through declared lawful models without duplicating sets,
   sorting or topology. A lawful finite table does not establish native
   comparator correctness, IEEE field/order laws, compiler soundness, or a
   new constitutional theorem. These obligations remain open with #294.

<a id="time-reversal-reference"></a>

## Exact finite time-reversal reference (#301)

This implements **two selected two-dimensional models over Q(i)** for
[#301](https://github.com/MGYamada/Vastitas/issues/301): a spin-1/2 doublet
and a separately selected spinless two-orbital model. It is Python reference
calculation and regression coverage. It adds no Lean theorem, public `.vast`
feature, accepted-Core connection, empirical verification or classification.
##301's wider design checklist remains open.

### Dependency and reproduction

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

- [Reference](https://github.com/MGYamada/Vastitas/blob/main/scripts/time_reversal_reference.py): explicit semilinear
  actions, independent target selection, phase and basis transport, and
  subject-bound invariance observations.
- [Tests](https://github.com/MGYamada/Vastitas/blob/main/scripts/test_time_reversal_reference.py): independent numerical
  witnesses and negative examples, discovered by the existing Python CI.
- [Demo](https://github.com/MGYamada/Vastitas/blob/main/scripts/demo_time_reversal_reference.py): full exact operands,
  selected metadata, observed squares, phase/basis transport, Hamiltonian
  and state results, and expected rejection messages as JSON. Rational
  coefficients are numerator/denominator records, never decimal estimates.

Only the Python standard library is needed. No existing CAR/Graph code,
test, compiler, kernel, oracle or CI workflow is changed.

### Selected coefficients, actions and physical interpretation

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

### Phase and basis transport

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

### Independent selection and replay rejection

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

### Hamiltonian and state are different subjects

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

### Status and remaining obligations

| Layer | Status of this change |
| --- | --- |
| Reference computation | Exact Q(i) matrix/vector equations, positive and rejection regressions, and executable JSON demo. |
| Lean proof | None added. Exact arithmetic/embedding correspondence, semilinear composition, antiunitarity and transport soundness still require proofs against the actual definitions. |
| Production Core | No source resolver, Core certificate, checker authority, lowering or native-refinement connection. A future bridge must bind independently resolved identities and methods to the exact accepted Core and preserve all coefficient/basis/profile/subject data. |
| Physical assumptions | Explicitly chosen interpretations of the two finite actions; mathematical acceptance verifies no experimental identification. |

These obligations retain #301's boundary with #204/#223, #278/#279 and
##285 and the existing checker architecture. They do not add a Domain Checker,
constitutional theorem or release gate. Space-group databases, general
projective classifications, magnetic groups and arbitrary physical symmetry
discovery are outside this change.
