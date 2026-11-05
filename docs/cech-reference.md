# Finite open-cover Čech reference (#265)

This is a **Python reference calculation and regression suite**, not a Vastitas
language feature, a Lean proof, or production acceptance. It implements only a
small finite-open fragment of [#265](https://github.com/MGYamada/Vastitas/issues/265).
The general complex/homology contract remains with
[#258](https://github.com/MGYamada/Vastitas/issues/258). No general sites,
characteristic classes, spectral sequences, resolutions, or second homological
algebra library are implemented.

Baseline: main `d783b5a6e393214a54cb408501963b1e42a7be94`.
Python 3.10+, standard library only, with arbitrary-precision integers:

```sh
python3 -m unittest discover -s scripts -p 'test_cech_reference.py' -v
python3 scripts/demo_cech_reference.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

- [Reference](../scripts/cech_reference.py): finite topology, intersections,
  componentwise sections, restrictions, alternating differential and binding checks.
- [Demo](../scripts/demo_cech_reference.py): JSON containing separate check
  outcomes, proposed complex input, cover provenance and exact integer witnesses.
- [Tests](../scripts/test_cech_reference.py): 28 regression cases, automatically
  discovered by the existing Python CI step. No workflow change is needed.

Validation: all 28 focused tests passed; full Python discovery ran 237 tests
with 236 passes and one existing live compiler integration skip (the Rust CLI
and Lean kernel binaries are not built in this environment). The dependency
boundary checker passed. No Rust or Lean source changed; no new compiler or
Lean build result is claimed.

## Fixed semantic profile and independent checks

The input is a nonempty space of at most eight explicitly named points, its
complete finite topology, and one to four **ordered, labelled** cover members.
The checker verifies that the topology contains the empty set and whole space,
contains only point subsets, and is closed under pairwise unions/intersections.
Since the family is finite, these conditions give finite intersections and
arbitrary unions. It separately verifies that every cover member is open and
their union is the whole space. Duplicate cover *opens* are allowed under
distinct labels; empty members are allowed. These are reference size limits,
not mathematical restrictions on #265.

For each nonempty increasing index tuple, the checker recomputes the actual
intersection from the cover sets. It retains **empty intersections explicitly**.
It never uses the submitted intersection table to compute the expected complex.
The current convention is the increasing-index alternating Čech complex;
changing ordering/bases requires reconstruction or future proved transport.

The coefficient object is the **locally constant integer sheaf**: sections on
an open U are integer-valued locally constant functions, represented by one Z
per connected component. This is not the constant presheaf assigning one Z to
every nonempty open. In a finite space, components are obtained from the
undirected specialization graph, using minimal open neighbourhoods computed
from the topology. In particular F(empty)=0, while a disconnected open can
have multiple generators. The future equivalence with the sheaf interpretation
is an explicit proof obligation below.

For V contained in U, every component of V lies in one component of U. The
restriction matrix has one row per V-component and one column per U-component,
with entry 1 precisely for that containment. We retain all inclusions among
the actual intersection opens, including identities and maps to the empty set.
Thus both the **actual restriction functions** and their **identity/composition
laws** can be checked separately. A different functor with zero maps on proper
inclusions can satisfy the laws while failing to represent the chosen sheaf.

For an increasing tuple J=(j_0,...,j_(p+1)), the component of the differential is

```math
(dc)_J=\sum_{k=0}^{p+1}(-1)^k
 \operatorname{res}_{U_{J\setminus j_k},U_J}(c_{J\setminus j_k}).
```

All matrices act on column vectors. The checker compares the submitted maps
with this alternating construction and separately multiplies adjacent submitted
differentials over Z. Matrix dimensions remain explicit even for zero rows or
columns. There is no floating-point tolerance or rational-rank acceptance.

| Check | What is checked independently |
| --- | --- |
| Binding/profile | Exact expected subject and supported finite-open / locally constant Z profile |
| Topology / cover | Actual topology axioms / actual open-cover condition |
| Overlaps | Complete increasing tuple table equals recomputed intersections |
| Sections | Ordered section bases equal components of those actual intersections |
| Restrictions | Complete typed restriction diagram equals restriction of locally constant functions |
| Restriction laws | Identities and every composable inclusion triangle |
| Orientation | Returned complex equals the fixed alternating construction, including coefficient identity and ranks |
| Endpoints | Internal ranks, differential count and source/target matrix dimensions |
| d squared | Each adjacent matrix product is exactly zero |

Malformed immutable records are rejected with `Invalid`. A changed subject
blocks subsequent checks; unsupported site/coefficient profiles are reported
as `unsupported`. Missing or ill-typed maps produce `not_checked` for the
dependent laws/product. Neither status counts as success. Well-typed candidate
matrices can still have their d squared checked when their geometric checks
fail; that result is algebraic only. All checks must pass before `returned`
contains a candidate. `propose` is a convenience producer, not an authority.

## Six-point model and the adversarial complex

The points are v0,v1,v2,e01,e02,e12, ordered by face inclusion. Opens are upper
sets. Exhaustive enumeration gives 18 opens, with the cover

```text
U0 = {v0,e01,e02}
U1 = {v1,e01,e12}
U2 = {v2,e02,e12}
```

The pair intersections in order 01,02,12 are {e01},{e02},{e12}; the triple
intersection is empty. Each nonempty intersection is connected. Hence

```math
C^0=\mathbb Z^3,\quad C^1=\mathbb Z^3,\quad C^2=0,\qquad
D=d^0=\begin{pmatrix}-1&1&0\\-1&0&1\\0&-1&1\end{pmatrix}.
```

All degrees beyond the finite presentation are zero. This statement concerns
**this Čech complex only**, not derived-functor sheaf cohomology.

| Candidate | Geometric / orientation result | d squared | H1 of candidate complex |
| --- | --- | --- | --- |
| Actual cover | All checks pass | Zero | Z |
| Invented triple intersection, C2=Z, d1=(1,-1,1) | Overlap, section basis and orientation fail | Zero | 0 |
| One incorrect sign in original d0 | Orientation fails | Zero because C2=0 | Not used for acceptance |
| Three genuine identical opens of a point, then wrong d1=(1,1,1) | Overlaps pass; orientation fails | Nonzero | Not computed |
| Reuse on another cover, coefficient or site | Binding fails | Not checked | Not borrowed |

For the fake complex, the added point {e01} is not even contained in the other
two pair intersections. Matrix algebra cannot repair that missing geometric
origin. Conversely, on the one-point space a genuine three-member repeated
cover has exactly the matrices D and (1,-1,1) and is accepted. Identical matrices
do not determine which space/site/cover they represent.

## Integral kernel, image and quotient witnesses

The executable witness routine is deliberately restricted to the two displayed
triangle presentations. It is not a general Smith normal form or homology
implementation. It verifies the following **integer** matrices and their
explicit integer inverses:

```math
U=\begin{pmatrix}1&0&0\\0&1&0\\1&-1&1\end{pmatrix},\quad
V=\begin{pmatrix}0&0&1\\1&0&1\\0&1&1\end{pmatrix},\quad
UDV=\operatorname{diag}(1,1,0).
```

Both products U U_inverse and U_inverse U, and likewise for V, are checked
against the identity. Thus this is a unimodular change of integral bases.
The kernel of D is Z(1,1,1), and its image has basis
b1=(1,0,-1), b2=(0,1,1).

Let q(a,b,c)=a-b+c, g(n)=(0,0,n), and S(a,b,c)=(0,a,b). The program checks
the full matrix identities

```math
qD=0,\qquad qg=1,\qquad DS+gq=I_3.
```

In particular, every integral y=(a,b,c) decomposes as

```math
y=D(0,a,b)+(a-b+c)(0,0,1).
```

Consequently im(D)=ker(q), q is onto Z with integral section g, and
Z^3/im(D) is Z, with no torsion. For the actual complex ker(d1)=Z^3, so
H0=Z and H1=Z. For the fake complex d1=q, hence ker(d1)=im(D) and H1=0.
In the JSON, `cokernel_d0_map` and its section describe the ambient cokernel
C1/im(D) in both cases; they are not a section of the fake complex's H1.
This gives kernel, image and quotient arguments without inferring an integral
answer from dimensions over Q. The tests also double D: the same U,V yield
diag(2,2,0), and b1 cannot lie in im(2D) because its first coordinate is odd.
The original integral witness is rejected despite unchanged rational rank.

These are executable exact identities plus the stated elementary argument;
they are not yet Lean-checked proofs.

## #258 handoff versus #265 provenance

`ComplexData` is a **proposed data boundary**, not an existing std::category::abel
API: it contains the selected integral coefficient identity, finite graded
ranks and exact differential matrices. It uses local integer basis slots and
implicitly zero terms outside the finite range. General kernels, images,
quotients, homology functoriality and derived-functor machinery belong to #258;
this reference implements none of those generically.

`CoverData` is the #265 sidecar: actual intersections indexed by the ordered
cover, bases labelled by intersection/component, and actual restriction maps.
`Candidate.subject` binds both to the complete topology and cover plus the
environment, space, site, coefficient, sheaf, cover and model-revision identities.
Consumers must carry the sidecar/subject when claiming that a #258 complex is
cover-derived. Passing only matrices loses that claim.

`verify(expected, candidate)` takes the expected subject independently and
compares complete immutable values, not hashes, matrix equality alone or
caller-supplied success flags. Changed identities require fresh checking even
when the mathematics looks identical. Retagging the entire candidate still
causes reconstruction; changing both inputs cannot import external authority.
Python records and these synthetic identifiers do not authenticate ownership,
dependencies or a real compiler environment. A consumer must replay verification
against its current expected subject, not treat a constructed `Report` as proof.

## Additional evidence and future proof obligations

No result here certifies overlap acyclicity, higher **sheaf** cohomology
vanishing, an acyclic/good cover, or comparison with a circle, singular
cohomology or derived global sections. Even the one-member cover {X} of this
six-point space passes finite-cover checking and has zero positive-degree
Čech terms. The checker does not infer a sheaf-cohomology vanishing theorem
from that truncated complex.

For a Čech-to-sheaf comparison, first supply the abelian sheaf/category and
derived-global-sections framework with its admissible resolution hypotheses,
then an actual comparison map and theorem with applicable hypotheses. One
possible route requires acyclicity of the chosen sheaf on every relevant
nonempty finite overlap: all positive-degree derived groups there vanish.
Finiteness, connectedness, d squared zero and computed matrix ranks do not
provide those premises. Any circle/singular comparison would separately need
an interpreted finite model and an appropriate proved comparison. Neither is
implemented here, and there is no comparison-evidence acceptance API.

The future Lean work must establish, against independent mathematical semantics:

1. Finite topology/cover acceptance implies the actual open-cover predicate;
   every returned intersection is its set-theoretic intersection.
2. The component representation denotes locally constant Z-valued sections
   (including empty and disconnected opens), with a lawful abelian sheaf
   interpretation. Returned matrices denote the actual restrictions and satisfy
   their identities/composition, not merely an arbitrary lawful presheaf.
3. The chosen ordered bases and alternating signs denote the Čech differential;
   face cancellation proves d squared zero. Executable integer matrix operations
   agree with the abelian-group maps supplied to #258.
4. Acceptance returns exactly those complex/provenance data for the same subject.
   Prove the fixed integer splitting identities and their kernel/image/quotient
   interpretation using #258, rather than introducing another homology library.

Implement executable checks in the **mathlib-free `lean-kernel/`**, with proofs
in `lean/` importing that actual implementation. No `sorry`, custom axiom,
second Boolean checker, or Python success flag can discharge these obligations.
Failure of this bounded reference is not a universal nonexistence theorem.

For the accepted-Core bridge, resolve the actual space/topology, cover, sheaf,
coefficients, selected operations and dependencies from the validated environment
and the exact protocol-7 executable Core. Bind the resulting subject to
`accepted.checked.executable.core.module`, prove the denotation of each extracted
section/restriction/differential agrees with that Core, and retain the exact
returned module in the evidence attachment consumed by codegen. The existing
[`IndexedWire.codegen_input`](../lean/VastitasOracle/IndexedWire.lean) equates
that module with the lowered module; it supplies no Čech theorem. Changes to
source, environment, coefficients, site, cover, ordering or selected method
must invalidate evidence or use proved transport for the actual transformed
Core. Compose these obligations through #184/#192 and existing checker
jurisdictions with independent Ownership/Borrow; do not add another top-level
Domain Checker. Storage/native refinement remains a separate obligation.

| Layer | Status of this increment |
| --- | --- |
| Finite topology/cover, sections/restrictions and integer matrices | Implemented and regression-tested Python reference |
| Kernel/image/quotient for the two fixed complexes | Explicit integral identities checked; argument above |
| General homological algebra | Remains #258's responsibility; not implemented here |
| Lean soundness and actual accepted-Core connection | Obligations only; no new Lean build/proof claimed |
| Acyclicity, sheaf/singular/circle comparisons | Require additional evidence/theorems; not certified |
| General sites, characteristic classes, spectral sequences | Outside this increment |

Ordinary compilation and generated programs do not import Python or this
reference. Rust, Lean kernel/oracle, public protocols and stdlib are unchanged.
