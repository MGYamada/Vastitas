# Finite order, lattice and Galois connection reference

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
[the verifier](../scripts/order_reference.py),
[literal fixtures and demo](../scripts/demo_order_reference.py), and
[regressions](../scripts/test_order_reference.py).

## Finite representation and acceptance

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

## Binding and trust boundary

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

## Reproduced examples and independent regressions

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

## Remaining obligations

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
