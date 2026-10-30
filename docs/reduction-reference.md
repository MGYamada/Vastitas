# Finite reduction-plan reference

This independent Python reference for [#303](https://github.com/MGYamada/Vastitas/issues/303)
checks a candidate reduction against a **separately supplied target**. It does not
implement a Vastitas acceptance route, a production law provider, Lean proof
checking, native SIMD, real threads, a scheduler or a profiler.

`scripts/reduction_reference.py` owns the checker and arithmetic models;
`reduction_fixtures.py` constructs examples, `test_reduction_reference.py` supplies
regressions, and `demo_reduction_reference.py` prints the finite result ledger.
These scripts use only the Python standard library and are development tools,
not compiler/runtime dependencies. Existing CI discovers the tests.

## Independent target and candidate

The caller supplies a target with ordered input occurrence IDs, each input's
revision and exact value, a selected operation/revision, carrier, coefficient
model, numerical profile and contract. The candidate contains only its target
ID, selected binding, a binary tree and references to the closed law fixtures.
The checker never infers the requested target from the candidate. The caller must
actually control the target input; two filenames alone do not establish authority.

The checker separately compares:

1. Leaf identity and revision against the actual target occurrences.
2. Multiplicity: each target occurrence appears exactly once.
3. Ordered leaf sequence, independently of bracket shape.
4. Binary bracketing and, when pinned, the complete exact tree.
5. Operation, implementation revision, carrier and coefficient identity.
6. Each numerical-profile field and every submitted evidence reference.
7. Recomputed values against the independently selected reference computation.

Each binary node repeats and must match the selected binding. Leaves cannot
supply payloads. Equal values do not merge occurrences; equal matrix dimensions
do not identify a different carrier or coefficient model. Candidate-owned
contracts, result claims, callables, law tags, checked fields and proof payloads
are not admitted. Evaluation uses the same immutable parsed tree that was audited.
SHA-256 report identifiers record the target/candidate data, not proof authority;
reports cannot be fed back as certificates, and every call recomputes results.

## Law authority and transformation policy

The closed `_LAWS` table is an **explicit reference assumption**, not a Lean
certificate verifier. It contains scoped associativity fixtures for exact
rational 2x2 matrix multiplication and associativity/commutativity fixtures for
rational addition and multiplication. No binary64 associativity fixture exists.
The table cannot be extended by candidate JSON. Every submitted reference,
including unused evidence, must match both its independent catalog record and
the full selected binding. Candidate tags cannot upgrade a law. The matrix v2
fixture deliberately has v1's arithmetic but a different revision identity.

For an exact reduction, reassociation preserves the leaf order unless the
independent target explicitly permits permutation and matching commutativity
evidence is present. Associativity alone never authorizes permutation. This
conservative reference requires associativity for every non-identical tree,
including permutations; it does not implement every possible local commutation
rule. Matching finite results alone cannot grant transformation permission.

## Contracts and arithmetic profiles

| Contract | Reference and admission | Meaning of success |
| --- | --- | --- |
| `exact` | Ordered seedless left fold; scoped exact laws for changed trees, plus explicit permission and commutativity for permutation | Exact equality for these inputs, under the closed reference law assumptions |
| `fixed_tree` | Target independently pins the full tree and profile; candidate must match both | Repeatable evaluation in this software model; left-fold equality is a separate observation |
| `left_fold_equivalent` | Retain leaf order and compare against the left fold | Equality for this finite input snapshot only; no law or permission for other inputs |
| `relaxed` | Retain explicit policy/error-contract IDs; validate structural fields | Always `unsupported` for a structurally valid candidate, because error/enclosure checking is unimplemented |

`left_fold_equivalent` is an additional finite diagnostic mode, not a fourth
general parallel contract. A fixed tree may succeed even when its left-fold
comparison overflows; that observation is `outside_profile` with no equality
claim. An unsupported relaxed contract never succeeds merely because sample
results happen to agree, and there is no implicit epsilon.

Exact values use `Fraction`; exact matrices are 2x2 over QQ. Scalar QQ addition,
multiplication and subtraction are also available, but subtraction has no law
fixture. Approximate coefficient coercion and machine integer overflow are absent.

The binary64 model accepts finite input bit patterns, computes the exact rational
sum, then rounds using integer arithmetic to nearest, ties to even. It retains
gradual subnormals and signed zero; NaN/infinity inputs and overflowing results
are rejected. FMA is forbidden. Profiles retain representation, precision,
rounding, FMA, subnormal, exceptional-value and signed-zero policies plus backend
identity. The backend here is the software reference, not OpenBLAS or hardware.
All 64 result bits are compared, including signed zero.

This is a **value-only finite numerical profile**, not the full observable-flags
or failure semantics proposed by [#318](https://github.com/MGYamada/Vastitas/issues/318).
It does not implement `monad::float` or claim its monad laws. Observable flags,
traps, NaN policies, branch effects and first-failure traces need their own
admitted semantics. Bind associativity never authorizes arithmetic reassociation.

Reference limits: 1–128 input occurrences, 255 tree nodes, depth 128, rational
input strings of at most 256 characters, and intermediate numerators/denominators
of at most 8192 bits. Exact arithmetic budget exhaustion is `unsupported`.
Empty reductions, seeds, unit laws, DAGs and user-defined operators need separate
contracts. The model never inserts an identity for empty inputs or partial chunks.

## Finite results and regressions

For `A=[[1,1],[0,1]]`, `B=[[1,0],[1,1]]`, `C=[[1,2],[0,1]]`:

- `(AB)C = A(BC) = [[2,5],[1,3]]`: ordered reassociation is admitted.
- `(BA)C = [[1,3],[1,4]]`: associativity-only permutation is rejected.
- Equal-valued identity-matrix samples still cannot supply commutativity evidence.

For binary64 `x=2^54`, `y=-2^54`, `z=1`, the left fold yields
`3ff0000000000000` (1), while the right tree yields `0000000000000000` (0).
The independently pinned right tree succeeds with a false left-fold-equivalence
observation; asking it to satisfy `left_fold_equivalent` yields `VALUE_MISMATCH`.

The 62 regression tests include:

- All 5 binary shapes and 24 permutations of four occurrences: only the five
  ordered matrix plans pass, while all 120 QQ-add plans pass with both laws and
  explicit permission.
- 4096 triples of 2x2 matrices with binary entries, and 5000 seeded binary64
  additions compared with the host Python result.
- Rounding ties, subnormal boundaries, cancellation, signed zero, overflow and
  strict JSON/CLI rejection and exit status handling.
- Missing/duplicate/stale/unknown leaves, equal-valued occurrence substitution,
  self-issued laws, operation/revision/carrier/coefficient/profile substitutions,
  invalid unused evidence, unsupported relaxed claims and resource limits.

These enumerations are finite observations, not general algebraic proofs or
soundness proofs of the Python checker. The host comparison is an additional
finite check; plan evaluation itself does not depend on host Float rounding.

```sh
python3 -m unittest discover -s scripts -p 'test_reduction_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/demo_reduction_reference.py
python3 scripts/demo_reduction_reference.py --write-fixtures /tmp/reduction-fixtures
python3 scripts/reduction_reference.py \
  /tmp/reduction-fixtures/matrix_ordered_reassociation.target.json \
  /tmp/reduction-fixtures/matrix_ordered_reassociation.candidate.json
```

The checker CLI exits with 0 for accepted, 1 for rejected, 2 for unsupported and
3 for malformed CLI input. It rejects duplicate JSON keys and NaN/Infinity.

## Actual implementation and remaining proof obligations

Reviewed main `46580b6bb217af421dc2bd5a82c0b89ace340a6f` includes public numerical
GEMM and [#309](https://github.com/MGYamada/Vastitas/pull/309)'s independent wire
mutation tests. Those tests retain valid surrounding metadata so rejection
reaches the intended semantic boundary. They do not implement reductions.

The [Graph checker](graph-crossings.md) audits finite crossing words, scoped law
authority and exact returned graphs; it has no reduction reassociation rule and
its production law provider/Indexed.Core bridge remain pending.
[StorageNumerical](numerical-values.md) connects nominal products and live loans
to the actual emitted resource GEMM. Its structural certificates do not prove
Float laws or accuracy. The [native adapter](numerical-adapter.md)'s `NativeFast`
policy permits backend FMA/blocking/reduction order and cannot supply this
reference's pinned-tree guarantee.

Before admitting a production reduction transformation:

1. Prove the actual selected operation's algebraic laws, domain/closure and exact
   realization. Prove ordered reassociation from associativity and permutation
   from the required commutativity. Empty/seeded folds need explicit extra laws.
2. Reconstruct the target from the actual accepted source/environment/Core,
   independently of the proposal. Connect every input occurrence, selected
   method and revision-bound evidence to that same returned Core. Pure,
   pre-evaluated reference values do not justify reordering effectful expressions.
3. Prove soundness of the actual checker using its implementation definitions;
   the closed Python law table, candidate tags and report hashes are not authority.
4. Preserve exact tree/occurrences/operations/profiles through lowering and
   native execution. Keep source-to-Core and Core-to-native refinement distinct.
   Add source and forged/direct-IR regressions through that real entry point.
5. Prove the selected numerical implementation/refinement, including rounding,
   FMA, subnormals, signed zero and observable exceptional/effect behavior.
   General left-fold equivalence and validated relaxed error bounds require
   separate proofs; a single matching sample is insufficient.
6. Establish the remaining #303 access, ownership, noninterference, completion
   and scheduling obligations when actual parallel execution is introduced.

This reference completes none of those general Lean/Core/native obligations,
adds no Domain Checker or constitutional theorem, and does not close #303.
