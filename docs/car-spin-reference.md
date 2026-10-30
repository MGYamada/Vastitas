# Exact finite CAR and ordinary-spin reference (#246)

This is the first executable physics example for
[#246](https://github.com/MGYamada/Vastitas/issues/246), using the crossing
reference associated with [#201](https://github.com/MGYamada/Vastitas/issues/201)
and the super/Koszul obligations in
[#245](https://github.com/MGYamada/Vastitas/issues/245).
It covers **one/two modes only**, independent spin sites, and the two/three
Pauli generator images. It is a Python matrix observation, not `.vast`
execution, a Lean proof, an implemented stdlib algebra, or production Graph
authority. #246 remains open; its wider acceptance checklist is not completed.

## Run and inspect

```sh
python3 scripts/demo_car_reference.py
python3 -m unittest discover -s scripts -p 'test_car_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_graph_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

- [Reference](../scripts/car_reference.py): exact scalars, matrices, closed
  named models, explicit adjoints, finite observations and rank witnesses.
- [Demo](../scripts/demo_car_reference.py): JSON containing the full model,
  ordered basis, grading, operator matrices and relation operands, plus all
  four requested negative examples. Fractions are numerator/denominator
  records; complex coefficients are pairs of exact fractions.
- [Regressions](../scripts/test_car_reference.py): CAR, ordinary spins,
  Pauli images, metadata mutations and the separation from Graph authority.

Only the Python standard library is needed. The existing CI discovers
`scripts/test_*.py`, including these tests and the unchanged
[`test_graph_reference.py`](../scripts/test_graph_reference.py) suite.
No compiler, kernel, proof-oracle or workflow change is required.

## Coefficients, ordered bases, adjoint and models

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

## Finite observations and negative examples

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

## Observation is not rewrite authority

`MatrixObservation.all_hold` means exactly that these finite matrices satisfy
the listed equations. Nothing in `car_reference` issues Graph evidence,
defines a new rewrite, or consumes/produces `Indexed.Core`.

The existing structural whitelist and fixture evidence checker remain in
[`graph_reference.py`](../scripts/graph_reference.py). The new tests use
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

## Remaining connections and proof obligations

These extend [the existing Graph obligations](graph-proof-obligations.md),
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
