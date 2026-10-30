# Exact SSH Bloch/Fermi reference

This is the first finite physics reference for
[#247](https://github.com/MGYamada/Vastitas/issues/247). It implements exact
external Python calculations and regression tests. It does **not** implement
`std::geometry::toric`, accept `.vast` programs, or establish a Lean theorem.
The general toric design and its acceptance checklist remain open.

## Run

From the repository root, with Python 3.10 or later and only its standard library:

```sh
python3 scripts/demo_ssh_toric_reference.py
python3 -m unittest discover -s scripts -p 'test_ssh_toric_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The demo emits JSON containing exact equations, quotient multiplication matrices,
the three counterexamples, and named checks; it exits nonzero if a check fails.
Its status is explicitly `external_exact_reference_only`. The existing Python
CI discovery includes the new tests without adding SymPy or a compiler dependency.

Files: [arithmetic and presentations](../scripts/ssh_toric_reference.py),
[demo](../scripts/demo_ssh_toric_reference.py), and
[regressions](../scripts/test_ssh_toric_reference.py).

## Supported fragment and stored data

The arithmetic is finite sparse `QQ[v,w,E,z,z^-1]`, using `Fraction` coefficients
and exponent tuples in that fixed order. Only the exponent of `z` may be
negative. Normalization merges equal monomials and removes zero coefficients;
it never takes a radical or extracts a root set. Floats, Boolean coefficients,
negative parameter/energy powers and arbitrary rational-function inverses are
rejected. There is no expression parser or untrusted JSON input interface.

`TorusPresentation(coordinates, equation)` retains the affine presentation
`Spec(QQ[coordinates,z^-1]/(equation))`. The coefficient field is always `QQ`,
the inverted coordinate is always `z`, and remaining `v,w` are base parameters;
remaining `E` is the energy coordinate. `Specialization` retains its source,
target and exact assignments, and reconstructs the target equation to reject
inconsistent maps. Its scheme morphism is contravariant to this ring map.
Equal presentations are compared structurally; this is not a test of nominal
scheme identity or a decision procedure for isomorphism of presentations.

| Scheme data to preserve | This reference | Production obligation |
| --- | --- | --- |
| Base and ambient | `QQ`, remaining coordinates, and localization at `z` | Checked base/model identities and coordinate/group-ring interpretation |
| Defining ideal | One complete Laurent generator, including repeated factors | Quotient algebra and certified ideal comparisons, never automatic reduction |
| Family and fiber maps | Source, target, exact rational assignments; `E=0` is explicit | Base-change/fiber construction and endpoint correspondence |
| Multiplicity | The full double-point algebra with basis `1,epsilon` | Prove the quotient equivalence and module length over the stated residue field |
| Localized units | Signed `z` exponents and explicit inverse in the double point | Unit witnesses and localization universal property |
| Polynomial representatives | Clearing power, original generator, saturation witness | Extension/contraction certificate for the chosen affine/toric ambient |
| Spectral module/action | The actual SSH matrix remains separate from its determinant | Retain matrix/module data when kernel or Jordan information is required |
| Provenance | Fixed example and explicit presentation maps | Actual source/Core occurrence, nominal objects, owners, model laws, revisions and evidence binding |

All Python objects and operations are external reference representations, not
authenticated compiler evidence. The code does not implement general schemes,
quotients with arbitrary ideals, multivariate Laurent lattices, general matrices,
fan gluing, compactification, numerical bands or the physical unitary slice.
The algebraic torus is not restricted by `|z|=1`.

## Parameter family, fiber and specialization order

Over `R=QQ[v,w]`, the code constructs

```math
H=\begin{pmatrix}0&v+wz^{-1}\\v+wz&0\end{pmatrix},\qquad
P=\det(EI-H)=E^2-v^2-w^2-vw(z+z^{-1}).
```

The Bloch presentation is `Spec(R[z,z^-1,E]/(P))`, with its projection to the
parameter base and to the energy line over that base. The zero-energy Fermi
presentation is its fiber along `R[E] -> R`, `E -> 0`. Parameter specialization
uses `R -> QQ`, leaving `z` invertible. Tests compare these operations in both
orders and together, and compare specialization before/after the matrix
determinant. Exact independent scalar evaluations cover rational and negative
parameters as well as zero hoppings. No operation divides by `v` or `w`.

The symbolic coefficient test records that `P` is monic of degree two in `E`.
The corresponding future theorem is that the Bloch projection to the torus is
finite locally free of rank two, with basis `1,E`, including degenerate bands.
This is a different projection from the Fermi fiber over a fixed energy: that
fiber need not always have length two. At `v=w=0,E=0` its equation is zero
(the whole torus); at `(v,w)=(0,1)` or `(1,0),E=0` its equation is `-1`
(the empty scheme). The double-point adapter rejects these cases.

Polynomial representatives require care. Clearing the parameter-family
denominator first and then setting `v=w=0` gives `z*E^2`; specializing in the
Laurent ring first and then clearing minimally gives `E^2`. They differ as
polynomials but generate the same Laurent ideal. The code checks the equality
after restoring the recorded powers of `z`. Scheme-theoretic closure/saturation
must not be assumed to commute with arbitrary base change.

## The nonreduced zero-energy fiber

At `v=w=1,E=0`,

```math
P_0=-(z+1)^2/z,\qquad
A=\mathbb Q[z,z^{-1}]/((z+1)^2)
  \simeq\mathbb Q[\epsilon]/(\epsilon^2).
```

The exact adapter first checks the full specialized presentation, not its roots.
The factor `-z^-1` is a unit. The maps are `z -> -1+epsilon`,
`z^-1 -> -1-epsilon`, and conversely `epsilon -> z+1`. The relations show the
maps are mutually inverse; `1,epsilon` is a basis over `QQ`. Hence this is a
length-two point supported at the rational point `z=-1`.

`Dual(a,b)` retains both coefficients. Multiplication and inversion are

```math
(a+b\epsilon)(c+d\epsilon)=ac+(ad+bc)\epsilon,\qquad
(a+b\epsilon)^{-1}=a^{-1}-ba^{-2}\epsilon\quad(a\ne0).
```

Columns of the regular multiplication matrix are images of the ordered basis
`(1,epsilon)`:

```math
M_\epsilon=\begin{pmatrix}0&0\\1&0\end{pmatrix},\quad
M_z=\begin{pmatrix}-1&0\\1&-1\end{pmatrix},\quad
M_{z^{-1}}=\begin{pmatrix}-1&0\\-1&-1\end{pmatrix}.
```

Tests explicitly check `epsilon != 0`, `epsilon^2=0`, both inverse products,
and that the fiber equation vanishes in this algebra. Negative powers are also
compared with the independent first-order remainder
`z^n = (-1)^n + n*(-1)^(n-1)*epsilon` for integers `-9 <= n <= 9`.
The first column of multiplication by `a+b*epsilon` recovers `(a,b)`, so these
matrices retain the element, not just its eigenvalues.

The reduction map `a+b*epsilon -> a` kills a nonzero element and reduces the
vector-space dimension from two to one. Equations `z+1` and `(z+1)^2` have
the same point support, but `z+1` is nonzero in `A`. Replacing the SSH equation
by the reduced equation or a triple power fails the exact presentation check.
The SSH matrix itself has off-diagonal entries `-epsilon,epsilon` over `A`,
while its value at the reduced point is the zero matrix.

## Boundary component and restricted saturation

After `v=w=1`, minimal clearing gives

```math
F=zE^2-(z+1)^2=zP.
```

An extra clearing gives `zF`. In affine `Spec(QQ[E,z])`, `zF` vanishes on
the entire line `z=0`, while `F|_{z=0}=-1`. On the torus they differ by a unit;
their affine zero schemes differ. `polynomial_boundary_at_z_zero` is explicitly
evaluation in the polynomial ambient. Laurent specialization at `z=0` is
rejected even for a constant expression, because it is not a ring map from
the declared Laurent ring.

`saturate_principal_z` supports **one nonzero polynomial `f` in `QQ[E,z]`**.
It finds the smallest `z` exponent `k` in the support and returns `g=z^-k f`.
The independent witness checks require the exact original input, `k>=0`,
`f=z^k g`, and `g|_{z=0} != 0` as a polynomial. Here the last condition means
`z` does not divide `g`; it does not assert pointwise nonvanishing for all `E`.
In this UFD, with prime `z`, these facts give

```math
(f):z^\infty=(g).
```

For `f=zF`, the returned generator is `F`. Equivalently, the contraction after
adjoining `t` and `1-tz` recovers `(F)`; one inclusion has the elementary witness
`F=t(zF)+(1-tz)F`. The implementation does not run a general elimination engine.
It removes only the `z` factor: saturation of `z^k(z+1)^2` still returns
`(z+1)^2`. Wrong powers, altered generators, replayed original inputs and
radicalized answers fail the witness check.

This is not general ideal membership, ideal equality or saturation over arbitrary
rings. Lists of generators, remaining parameters `v,w`, Laurent input and the
zero polynomial are explicitly unsupported by this helper. The last restriction
is an API limit, not a claim that saturation of the zero ideal is undefined.
Arbitrary toric closures and general boundary certificates remain future work.

## Characteristic multiplicity is not Jordan structure

At the reduced point `v=w=1,z=-1`, the SSH matrix is zero. Compare it to
`J=[[0,1],[0,0]]`. Both characteristic polynomials are `E^2`, but exact scalar
kernel dimensions are respectively two and one. `J` is nonzero and `J^2=0`.
The zero matrix has minimal polynomial `E`; `J` has minimal polynomial `E^2`.
Thus no similarity or exceptional-point claim follows from equal characteristic
polynomials or their repeated factors. `kernel_dimension2` only handles exact
scalar 2-by-2 matrices and rejects unresolved parameters; it is not a Jordan
classification algorithm over a nonreduced algebra.

## Future stdlib and Lean obligations

These are specifications, not completed Lean declarations or `.vast` fixtures.

1. Define the admitted exact coefficient and group-ring models; prove sparse
   normalization and operations denote finite Laurent polynomials. Establish
   localization, units and the supported ring maps, preserving declared bases.
2. Prove the determinant interpretation and its naturality under coefficient
   base change. Construct the actual quotient/fiber and comparison isomorphisms;
   prove monicity gives a finite locally free Bloch projection of rank two.
3. Prove the specific double-point quotient equivalence, basis independence,
   nonzero nilpotent and unit formulas. Preserve the nonreduced structure through
   serialization and lowering; a point set or square-free equation is insufficient.
4. Prove the actual restricted saturation verifier implies the stated
   extension/contraction result under its `QQ[E,z]`/principal hypotheses.
   New coefficient rings or ideals need separately justified algorithms and
   certificates. Prove polynomial-boundary evaluation is distinct from the
   Laurent ring map; do not infer closure/base-change commutation.
5. Keep spectral action/module data when claiming kernel/Jordan properties.
   Equal characteristic polynomials alone cannot supply that evidence.
6. Bind all evidence to the same checked environment, source occurrence,
   coefficient/model identities, ambient, ideal, specialization maps and actual
   returned Core. Independently reconstruct/recheck these in the kernel and
   import those actual definitions into the proof-only oracle; tests of this
   Python model are not a proof about a separately implemented compiler.

Use the existing checker responsibilities and independent Ownership/Borrow
boundary; this reference introduces no Toric/Bloch Checker. A future backend
also needs operational refinement and resource safety. Python, `Fraction` and
this code remain trusted for these external calculations; no general resource
bounds or protection against reflective Python mutation are provided. Unsupported
operations and deferred obligations are never reported as mathematical acceptance.
