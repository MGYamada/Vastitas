# Tensor products, dimensions, and resource ownership

[設計書の索引 / Design index](../design.md) · [出典 / References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:6:start -->
## 6. The common tensor product

### 6.1 A shared typed interface

The common `⊗` is part of Vastitas's foundation.

For module sheaves on one base,

$$
E\otimes_{\mathcal O_X}F
$$

is again a module sheaf. For compatible linear maps,

$$
a:E\to E',\qquad b:F\to F',
$$

the tensor map has type

$$
a\otimes b:E\otimes F\longrightarrow E'\otimes F'.
$$

Tensor values, typed linear maps, and network diagrams must agree on this operation and its structural laws.

Objects on different bases require an explicit common base or an external tensor product, such as `p_X^*E ⊗ p_Y^*F` on `X × Y`. The compiler must not silently identify coefficient rings or bases.

### 6.2 Monoidal profiles

A monoidal profile specifies its objects, morphisms, unit, composition, tensor product, associators, and unitors. Their coherence and functoriality justify supported rewrites.

Additional structure is declared separately:

| Capability | What it permits |
| --- | --- |
| Duality | Typed evaluations and coevaluations, with the relevant snake identities |
| Symmetry or braiding | Exchanges of factors with their specified laws |
| Trace or pivotal/ribbon structure | Admitted loop and twist operations |
| Conjugation and dagger | Explicit conjugate and adjoint operations |
| Coordinates | Basis-dependent componentwise operations |
| Differentiation | Supported smooth parameter families and backward implementations |
| Numerical realization | Storage, kernels, structural maps, and numerical policies |
| Dimension grading | Typed quantity lines, degree-preserving addition, tensorial multiplication, and explicit unit trivializations |

The first numerical profile is finite real or complex linear algebra. The shared contract should leave room for further profiles without pretending that every profile has a solver, derivative, or representation.

A diagram must retain the structure its profile needs. In a symmetric profile, factor exchanges may normalize to permutations. Graded signs must survive. A future braided profile would additionally retain crossing orientation; ordinary connectivity alone is insufficient.

For mathematical physics, this keeps the door open to tensor categories and topological sectors beyond ordinary vector spaces. Any such profile needs its own stated categorical laws, representations, and executable capabilities. In particular, a braided or dagger structure must not be inferred merely from suggestive diagram syntax.

### 6.3 The meaning of `Affine(n) ⊗ Affine(m)`

A generic affine scheme has no canonical vector-space tensor product. The notation becomes meaningful when the objects carry compatible linear structure.

For the standard affine objects with their chosen free-module structure, a proposed elaboration is

$$
\mathbb V(K^n)\otimes_{\mathrm{lin}}\mathbb V(K^m)
:=
\mathbb V(K^n\otimes_K K^m)
\cong
\mathbb A_K^{nm},
$$

where

$$
\mathbb V(E)=\operatorname{Spec}\operatorname{Sym}(E^\vee)
$$

for a finite locally free module in the ordinary setting.

Thus `Affine(K,n) ⊗ Affine(K,m)` may be convenient syntax when this linear structure is retained and unambiguous. An erased `Scheme` descriptor, a general affine variety, or an affine torsor does not acquire it automatically.

The corresponding ordinary product still has dimension `n+m`. Coordinate-algebra tensor products, module tensor products, and geometric products have related but distinct roles.

The exact surface carrier for linear structure is deferred. The semantic requirement is fixed: the operation must identify which modules are being tensored.

### 6.4 A tensor need not factor

A general value

$$
t\in V\otimes W
$$

cannot be unpacked into a pair `(v, w)` with `t = v ⊗ w`. Such a factorization exists only for a decomposable tensor, and a chosen factorization need not be unique.

The tensor type retains factor identities and port structure. It does not promise separate values or separately owned storage for the factors.

A low-rank or factored representation is additional data with its own approximation, exactness, and ownership contract.

### 6.5 No implicit complex conjugation

The default contraction is algebraic dual evaluation:

$$
\operatorname{ev}:V^\vee\otimes V\longrightarrow K.
$$

It is bilinear. For `A: V -> W`,

$$
A^\vee:W^\vee\to V^\vee
$$

is the algebraic dual map; in dual bases its matrix is `A^T`.

Conjugation and metric adjoints are separate:

$$
\overline A:\overline V\to\overline W,\qquad
A^\dagger:W\to V.
$$

The adjoint requires the declared Hermitian structures. Its conjugation must not be introduced by ordinary wiring, tensor formation, or a generic wire reversal.

Fixed-coordinate Einstein notation may elaborate through declared dual bases. Dimensions alone do not authorize a contraction.

### 6.6 Dimension-graded quantities and unit choices

Physical dimensions are a proposed **graded monoidal profile**, not a second, unrelated type system. Fix independent base dimensions (such as length, time, and mass), with character group

$$
G=\mathbb Z^k,
\qquad\text{or }G_{\mathbb Q}=G\otimes_{\mathbb Z}\mathbb Q\cong\mathbb Q^k
\text{ when rational exponents are admitted.}
$$

For each degree $d\in G$ (or $G_{\mathbb Q}$), provide an oriented real line $L_d$ with its positive-frame $\mathbb R_{>0}$-torsor. Over a parameter base $B$, use the corresponding oriented line bundle; the assignment $d\mapsto L_d$ is a coherent symmetric monoidal functor from the additive degree group to the Picard groupoid of oriented real lines. A quantity field is a section of $L_d\to B$. A real-valued quantity is not required to be positive merely because its *frames* are positive. Complex quantities can take values in $L_d\otimes_{\mathbb R}\mathbb C$.

The profile provides coherent isomorphisms

$$
L_0\cong\mathbb R,\qquad
L_d\otimes L_e\cong L_{d+e},\qquad
L_d^\vee\cong L_{-d}.
$$

Thus multiplication adds degrees, dualization negates them, and addition and comparison require compatible degrees and basepoints. The line-valued principle is the same as the Plücker construction in Section 5.3: a numeric coordinate is obtained only after choosing a frame. No hidden unit conversion, degree erasure, or complex conjugation is inserted into the shared `⊗` of Sections 6.1–6.5. [U1]

A unit system chooses positive frames for the independent base lines and hence trivializations for their coherent tensor powers. Rechoosing these frames is the action of $(\mathbb R_{>0})^k$ on coordinate values. For a family of nonzero or otherwise suitably restricted quantities with dimension matrix $D=(d_1,\ldots,d_n)$, dimensionless monomials $\prod_i q_i^{a_i}$ correspond to $Da=0$; these are the invariant combinations underlying Buckingham's $\pi$ theorem. The existence and meaning of an individual fractional or negative *value* power still require its ordinary domain conditions.

The positive structure group has a unique positive $r$th root for every positive integer $r$. Consequently its associated rational tensor powers, and hence degrees such as $\tfrac12[\mathrm{Hz}]= -\tfrac12[\mathrm{time}]$, have canonical coherent constructions within this chosen profile. This is a statement about the dimension line, not a promise that a negative real number has a real square root, or that a general line bundle has a canonical square root. [U1]

Declaring natural units such as $c=\hbar=1$ supplies **specific nonzero physical constants and the resulting line isomorphisms**. At the level of a rational character group, the declared independent relations quotient the degree group by the span of the dimensions of these constants. This changes the coordinate convention and allowed identifications, not the underlying physical model or a measured constant into a theorem. The chosen identifications must remain in the model or realization identity so that an undeclared conversion cannot leak across boundaries.

An affine unit such as a Celsius temperature reading belongs instead to an affine torsor $A_d$ for the additive group of $L_d$. Differences of points are quantities in $L_d$; adding a displacement to a point is meaningful, whereas adding two affine points or blindly multiplying them is not. A change of temperature origin is an explicit affine map with scale and offset; differences in degrees Celsius have the same magnitude as kelvin differences. This separate affine structure is an extension of the graded profile, not another multiplicative dimension line. [U2]

The compiler's first finite fragment may normalize degree equations in $\mathbb Z^k$ or $\mathbb Q^k$. A full presentation of units, affine quantities, frame changes, and user-facing conversion syntax remains to be implemented. Degree information is also an input to metric checking in Section 9.3; it must survive elaboration and relevant lowering.

<!-- draft-v0.3:6:end -->

<!-- draft-v0.3:7:start -->
## 7. Ownership and tensor-network ports

### 7.1 Separate runtime resources and function construction

| Layer | Ownership discipline | Meaning |
| --- | --- | --- |
| Geometric description | Immutable, shareable handles | Schemes, bundles, maps, and construction data |
| Numerical representation | Affine move/borrow discipline | Buffers, views, residuals, device allocations, and scratch |
| Network occurrence | Linear connection capabilities | Each endpoint is connected or returned exactly once |
| Generic function under construction | Linear whole-function ownership | One owner or exclusive borrower edits the method family and carries its completion obligations (Section 8.3) |

“Affine” ownership means an at-most-once resource discipline. It is unrelated to the algebraic-geometric property of being affine.

Classical values may be reused or explicitly copied. Linear ports do not impose quantum no-cloning behavior on numerical values.

### 7.2 Fresh occurrences, reusable values

~~~text
let a = tensor_value(...);

network {
    let left  = node(&a);     // fresh occurrence and fresh ports
    let right = node(&a);     // same numerical value, different ports
    connect(left.output, right.input);
    return boundary(left.input, right.output);
}
~~~

Each `node` creates new connection authority. Reusing a tensor value does not duplicate an existing port.

Connections check endpoint role, object identity, extent, scope, and profile. A finalized graph must account for every endpoint. Deliberate caps, traces, diagonals, and copy maps are typed operations requiring the appropriate structure.

### 7.3 Factor rights are not disjoint memory

If `t: V ⊗ W` occupies one dense buffer, acting on its `V` factor and acting on its `W` factor can touch the same entries.

Consequently, owning two factor ports does not authorize two simultaneous mutable borrows of that buffer. Even mathematically commuting operations need a valid execution schedule or a justified fused kernel.

Independent mutable access requires a real storage partition or another verified aliasing argument. Tensor decomposition alone is not such an argument.

### 7.4 Mutation and reverse residuals

Local mutation may implement a pure transition between logical values. Exclusive access establishes alias safety; it does not prove that an overwritten primal is unnecessary for reverse differentiation.

The storage planner must retain, copy, or validly recompute data required by backward execution. Residuals may be one-shot by default. Repeated pullbacks require an explicit reusable representation or recomputation policy.

A scheme descriptor or invariant-bearing numerical wrapper must retain immutable inputs for as long as its invariants depend on them. Updating those inputs creates a new logical object or uses an operation that preserves the invariant.

<!-- draft-v0.3:7:end -->
