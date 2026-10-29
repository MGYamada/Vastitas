# Geometric settings, objects, families, and sheaves

[Design index](../design.md) · [References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:2:start -->
## 2. Two geometric settings

### 2.1 Ordinary schemes

`Scheme` denotes ordinary schemes, with an explicit base when relevant. Affine objects have the usual form

$$
X=\operatorname{Spec}(A).
$$

Typical initial coefficient domains are the integers, rationals, finite fields, and finitely presented algebras over supported exact bases. An executable representation is a finite description of such an object; it is not an enumeration of its points.

A morphism

$$
\operatorname{Spec}(B)\longrightarrow\operatorname{Spec}(A)
$$

is represented contravariantly by a ring homomorphism `A -> B`. This variance must be visible in the semantic core, even when surface code uses geometric direction. [S1]

### 2.2 Smooth schemes

`CInfScheme` denotes schemes over `CInfRing` objects in the sense of smooth algebraic geometry. A `CInfRing` has operations associated with smooth real functions, with identities respecting composition. This is richer than an ordinary commutative real algebra. [J1]

The standard affine smooth object is

$$
\mathbb A^n_\infty
=
\operatorname{Spec}_\infty C^\infty(\mathbb R^n).
$$

`CInfScheme` includes smooth manifolds and supported singular or infinitesimal objects. It must not mean “a manifold whose coordinates happen to be differentiable.”

The initial implementation should use explicit finite presentations and admitted smooth primitives. Having a semantic operation for every smooth function does not imply that every such function has a finite program or an equality decision procedure.

### 2.3 Shared interfaces without a false subtype relation

The two settings share interfaces for appropriate objects and operations:

| Concept | Ordinary setting | Smooth setting |
| --- | --- | --- |
| Local algebra | Commutative ring | `CInfRing` |
| Geometric object | `Scheme` | `CInfScheme` |
| Structure-preserving map | Scheme morphism | Smooth-scheme morphism |
| Standard affine object | `Spec(K[x_1,...,x_n])` | `SpecInf(CInf(R^n))` |
| Cotangent object | Relative Kähler differentials | Smooth cotangent module/sheaf |
| Typical numerical domain | Obtained through an explicit realization | Smooth open domains and manifold charts |

Neither setting is declared to be a simple subclass of the other. Forgetting smooth operations changes what maps and derivations are allowed.

A shared implementation interface may abstract over a geometric setting. It must preserve that setting's identity, base, topology, and admitted constructions. Mixing an ordinary scheme and a smooth scheme requires an explicit bridge.

### 2.4 An explicit real smooth realization

Let

$$
U:C^\infty\mathrm{Ring}\longrightarrow
\mathrm{CAlg}_{\mathbb R}
$$

forget smooth operations while retaining the underlying commutative real algebra. The inclusion of polynomial operations into smooth operations induces a left adjoint

$$
F:\mathrm{CAlg}_{\mathbb R}\longrightarrow C^\infty\mathrm{Ring},
\qquad
\operatorname{Hom}_{C^\infty}(F(A),C)
\cong
\operatorname{Hom}_{\mathbb R\text{-alg}}(A,U(C)).
$$

The categories include the zero ring. The real-algebra version of this adjunction is stated explicitly in [BM1, Remark 2.3]. On free objects,

$$
F(\mathbb R[x_1,\ldots,x_n])\cong C^\infty(\mathbb R^n).
$$

Consequently, for a supported finite presentation,

$$
F\!\left(\mathbb R[x_1,\ldots,x_n]/(f_1,\ldots,f_r)\right)
\cong
C^\infty(\mathbb R^n)/(f_1,\ldots,f_r).
$$

The quotient uses the generated ideal, without radicalization. Smooth operations descend to such quotients by Hadamard's lemma. [J1, Section 2.2]

On coordinate rings, the proposed `cinf_realization` is this adjoint. On supported affine schemes its geometric form is
\(\operatorname{Spec}(A)\mapsto\operatorname{Spec}_\infty F(A)\).
Its mathematical definition is therefore independent of the chosen presentation. Since a left adjoint preserves colimits, there is a canonical isomorphism

$$
F(A\otimes_C B)
\cong
F(A)\amalg_{F(C)}F(B),
$$

where the right side is a pushout of smooth rings. This gives compatibility with the corresponding affine fiber products. These are consequences of the adjunction, rather than independent conjectures about each presentation. Implementations still have to realize these maps and preserve their invariants.

Real infinitesimal structure can survive. Taylor expansion gives

$$
C^\infty(\mathbb R)/(x^2)
\cong
\mathbb R[\varepsilon]/(\varepsilon^2),
\qquad
[g]\longmapsto g(0)+g'(0)\varepsilon.
$$

This is not a claim that `F` preserves every nonzero nilpotent or every algebraic point. The function `x*x+1` is a unit in `CInf(R)`, with smooth inverse `1/(x*x+1)`, so

$$
F(\mathbb R[x]/(x^2+1))=0,
\qquad
\operatorname{Spec}_\infty(0)=\varnothing.
$$

Thus non-real closed points can disappear even for schemes defined over the reals. A nonzero nilpotent supported entirely on a discarded component can disappear with that component; for example, `F(C[epsilon]/epsilon^2)=0` when the input is viewed as a real algebra. The universal map `A -> U(F(A))` need not be injective.

Complex coefficients therefore require an explicit real-geometric interpretation that retains the intended complex structure separately. Merely forgetting a complex algebra to a real algebra and applying `F` is not such an interpretation. This issue controls the real spectral parameter in Section 10.3.

When the base is already a smooth ring `A`, adjoining a variable relatively means the free smooth `A`-algebra
\(A\{\lambda\}=A\amalg_{\mathbb R}C^\infty(\mathbb R)\).
For `A=CInf(B)` with `B` an ordinary smooth manifold, this is
\(C^\infty(B\times\mathbb R)\). This construction retains the existing smooth operations on `A`; it must not be confused with freely adding smooth structure to its underlying real algebra. Section 10.3 supplies a specific comparison after quotienting by a hyperbolic polynomial.

The adjunction fixes the ring-level bridge. Executable presentations, supported module and sheaf operations, and non-affine gluing still need specified implementations and appropriate preservation results. Ordinary schemes also have differentials; the purpose of the smooth setting is to supply its own smooth operations and chain rules.

<!-- draft-v0.3:2:end -->

<!-- draft-v0.3:3:start -->
## 3. First-class objects, points, and staging

### 3.1 What first-class means

A program can construct a scheme, bind it to a name, pass it to a function, return it, and use it to specify associated types.

~~~text
let X: Scheme = Affine(QQ, 2);
let Y: CInfScheme = Affine(CInfReal, 3);

fn product_over(base, X, Y) {
    FiberProduct(X, Y, over = base)
}
~~~

Scheme values are immutable semantic descriptions. Their implementations may use shared nodes, lazy constructions, or opaque verified constructors.

First-class status does not require eagerly constructing a topology, enumerating open sets, listing all sections, or solving every equation. It requires that the object and its associated operations have coherent program-visible identities and meanings.

The following names describe the proposed associated type families:

| Type family | Intended meaning |
| --- | --- |
| `Point<X, S>` | An `S`-valued point of `X` in the chosen geometric setting |
| `Morphism<X, Y>` | A structure-preserving map with those endpoints |
| `ModuleSheaf<X>` | A sheaf of modules over `O_X` |
| `Bundle<X, R>` | A finite locally free module sheaf of rank `R` |
| `Section<F, U>` | A section of `F` on a specified open `U` |
| `LinearMap<E, F>` | A linear map between modules or bundles over the same declared base |
| `CoTangent<X, x>` | A cotangent at the specified point `x`, relative to an explicit or inferred base |

These are semantic interfaces, not a requirement to implement unrestricted dependent type theory.

### 3.2 Generalized points

The foundational point interface is

$$
X(S)=\operatorname{Hom}(S,X),
$$

or `Hom_B(S, X)` when working over a base `B`.

`Point<X>` is permitted only when its test object is fixed by the context. For example, a real point of a smooth scheme uses the smooth point as test object. It must not silently mean the complete point theory of `X`.

A dual-number test object detects information that ordinary real points miss. The language must preserve the distinction between a reduced point and an infinitesimal thickening even if their ordinary point sets agree.

Generalized points also describe families. A map `B -> Grassmannian(...)` is a family of subbundles or quotients over `B`, not a list of unrelated numerical subspaces.

### 3.3 Object identity and isomorphism

Equal dimensions do not imply equal geometric objects, modules, or numerical endpoints.

Two presentations can describe isomorphic schemes without being definitionally the same program object. Transport between them uses a specified isomorphism or an admitted canonical normalization. The compiler is not expected to decide arbitrary scheme isomorphism.

Dynamic geometry requires a restricted form of dependent packaging:

~~~text
fn make_problem(parameters) {
    let X = construct_scheme(parameters);
    let x: Point<X> = construct_point(X, parameters)?;
    pack { scheme: X, point: x }
}
~~~

The caller opens this package under a fresh scoped identity. A point cannot escape as though it belonged to an independently constructed scheme.

The proposed elaboration uses generative indices and existential packages where ordinary generics are insufficient. The exact mechanism remains open. Indexing a type by a runtime description must not be confused with evaluating that description at compile time.

### 3.4 Three useful stages

| Stage | Available information | Appropriate behavior |
| --- | --- | --- |
| Static | Geometry, ranks, function targets, and methods are known | Normalize supported constructions and specialize kernels |
| Runtime, finitely described | Extents or presentations arrive as values | Retain descriptors and check combinations locally |
| Symbolic or opaque | The object is meaningful but lacks an admitted realization | Allow supported symbolic composition; diagnose unavailable execution |

A runtime dimension is a finite dimension, not an arbitrary infinite index set. Infinite-dimensional geometry, general function spaces, and integration require separate semantics and representations.

<!-- draft-v0.3:3:end -->

<!-- draft-v0.3:4:start -->
## 4. Constructions, families, and base change

### 4.1 Constructors carry mathematical structure

`Affine` and `Projective` are constructions and properties, not mutually exclusive subclasses in an object-oriented hierarchy. The same object may admit several presentations or additional structures.

The initial vocabulary should include:

- Affine schemes and affine smooth schemes.
- Projective bundles and Grassmannians.
- Supported open restrictions and closed zero loci.
- Products and fiber products over a declared base.
- Gluing from admitted overlap data.
- Pullback of supported sheaves, bundles, and maps.

`Projective` in the smooth setting requires a specified smooth construction or realization. An ordinary polynomial `Proj` implementation is not automatically a smooth one.

Not every set of equations, quotient, or functor is automatically representable by a supported scheme. A constructor must establish its claimed object or return a symbolic problem whose representability remains unresolved.

### 4.2 Fiber products are not vector-space tensor products

For ordinary affine schemes,

$$
\operatorname{Spec}(A)
\times_{\operatorname{Spec}(R)}
\operatorname{Spec}(B)
\cong
\operatorname{Spec}(A\otimes_R B).
$$

The tensor product here is a tensor product of coordinate algebras. [S1, S2]

In particular,

$$
\mathbb A^n_K\times_K\mathbb A^m_K
\cong
\mathbb A^{n+m}_K.
$$

This is different from the rank-`nm` vector object obtained by tensoring free modules.

In smooth geometry, the corresponding coproduct of `CInfRing` objects uses their smooth-ring structure. An ordinary algebraic tensor product of the underlying real algebras is not generally the required smooth coproduct. [J2]

The core should therefore spell geometric products as `Product` or `FiberProduct`. The common numerical `⊗` of Section 6 must not conceal this distinction.

### 4.3 Families are primary

A family is a morphism `pi: X -> B`. Its fiber over `b: S -> B` is a fiber product:

$$
X_b=X\times_B S.
$$

Changing parameters is expressed by base change. For `g: B' -> B`, the family becomes `X ×_B B' -> B'`.

Associated bundle data, operators, and supported observations must transform coherently with this change. Mathematical naturality is stronger than reproducing the same result at a few sampled parameter values.

Base change does not automatically commute with every derived construction. Kernels, cohomology, and numerical selections need their own hypotheses. In particular, pulling back a kernel and recomputing the kernel after specialization need not agree without an exactness condition.

### 4.4 Local data and descent

A global object may be represented by local charts and overlap maps. On triple overlaps, transition maps obey the appropriate cocycle law. Sheaf sections agree on overlaps and glue according to their stated sheaf law.

Vastitas should support this structure explicitly when the programmer constructs geometric objects. An ordinary numerical call need not carry a universal chart or proof ledger.

Initial gluing should be restricted to supported covers with construction-specific validation. General descent, arbitrary quotient stacks, and automatic search for gluing proofs are deferred.

### 4.5 Physical parameter spaces and singular regimes

In a physical model, the base of a family may represent couplings, boundary conditions, geometry, fields, temperatures, or other parameters. This interpretation is additional structure, not a new meaning of base change. A change of parameters must transport each dependent object and observable through the same declared map.

The mathematical family can survive a point where a preferred numerical chart, eigenvector frame, perturbative expansion, or effective description fails. Conversely, a physically meaningful phase boundary or limit is not automatically a smooth morphism in the initial `CInfScheme` fragment.

Finite-volume approximations, continuum limits, and thermodynamic limits need separate constructions and hypotheses. Ordinary specialization of a finite presentation must not be advertised as proof of a limiting physical statement.

<!-- draft-v0.3:4:end -->

<!-- draft-v0.3:5:start -->
## 5. Module sheaves and Grassmannian points

### 5.1 Modules before coordinates

For a geometric object `X`, `ModuleSheaf<X>` means an `O_X`-module sheaf in the selected setting. A `Bundle<X, r>` adds finite local freeness of rank `r`.

A general module sheaf need not be a vector bundle. Its rank can jump, its fibers can behave singularly, and it need not admit a dual with the evaluation/coevaluation laws used by finite tensor calculus.

The core must distinguish these capabilities. A matrix representation of one local presentation is not evidence that a globally free bundle exists.

Initial executable interfaces should cover finite free modules, admitted finite presentations, locally free bundles with supported charts, their maps, tensor products, and pullbacks. Closure under arbitrary kernels must not be assumed for the chosen finite-presentation fragment.

### 5.2 A precise Grassmannian convention

Use a quotient convention explicitly:

$$
\operatorname{GrQuot}_X(E,k)(S)
=
\left\{
q:E_S\twoheadrightarrow Q
\ \middle|\
Q\text{ locally free of rank }k
\right\}/\cong.
$$

Here `S -> X` is part of the data and `E_S` is the pullback of the finite locally free ambient bundle. Quotients are identified by compatible isomorphisms. The quotient and subbundle conventions must never share an unexplained rank parameter. [S4]

A proposed spelling is:

~~~text
let G = Grassmannian(E, quotient_rank = K);
let q: Point<G, B> = ...;
let Q = pullback(G.universal_quotient(), q);
~~~

For a rank-`k` subbundle `W` of a finite locally free bundle `V`, the dual quotient

$$
V^\vee\twoheadrightarrow W^\vee
$$

gives a point of `GrQuot(V^vee, k)`. Recovering the subbundle uses the finite locally free duality. The numerical interface may provide a subbundle-oriented constructor that elaborates to this convention.

A numerical subspace therefore has a Grassmannian meaning and an associated tautological bundle. It is not a separate foundational `SubSpace` universe. Convenient checked operations for inclusion, restriction, and projection remain important.

### 5.3 Plücker data is line-valued

For a quotient `q: E -> Q` of rank `k`, define

$$
L_q=\bigwedge^k Q,\qquad
\bigwedge^k q:\bigwedge^k E\twoheadrightarrow L_q.
$$

This is the quotient-convention Plücker point. The line `L_q` need not have a preferred trivialization.

After choosing an ambient basis, the coordinates

$$
p_I(q)=\bigl(\bigwedge^k q\bigr)(e_I)
$$

are elements of `L_q`. Turning them into scalars requires an explicit line trivialization. Their products live in tensor powers of that line.

For a rank-two quotient of a free rank-four module,

$$
p_{12}\otimes p_{34}
-
p_{13}\otimes p_{24}
+
p_{14}\otimes p_{23}=0.
$$

The construction should preserve its Grassmannian origin. An arbitrary projective point of the exterior power is not automatically a valid Plücker image.

This exact core guides representations and formalization; numerical programs need not materialize every Plücker coordinate.

This distinction between an intrinsic line-valued quantity and a scalar obtained after trivialization reappears for physical dimensions in Section 6.6. It does not identify a Plücker determinant line with a physical unit line; it identifies the relevant *structural discipline*.

### 5.4 Maps on a selected subbundle

An inclusion `i: E -> V` is intrinsic. An orthogonal projection `p: V -> E` additionally requires a suitable metric. For an invariant subbundle, restriction gives `H_E: E -> E` with

$$
Hi=iH_E.
$$

For a non-invariant subbundle, compression `pHi` is a different operation. It must not be mislabeled as invariant restriction.

Changing a private frame `i_j=i_i g_{ij}` transforms operator matrices by

$$
H_j=g_{ij}^{-1}H_i g_{ij}.
$$

The abstract operator, its endpoint identity, and its invariant observations stay the same. AD and optimization must respect this transformation law.

This is also a Physics 2.0 design constraint. Gauge or frame choices may be indispensable for computation, yet an intrinsic physical observable should not depend on a private choice of local frame. Berry connections, holonomies, and characteristic classes require their own additional structures and domain conditions; they are not automatically manufactured by selecting numerical eigenvectors.

<!-- draft-v0.3:5:end -->
