# Reverse differentiation and spectral geometry

[設計書の索引 / Design index](../design.md) · [出典 / References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:9:start -->
## 9. Differentials and reverse differentiation

### 9.1 A common cotangent pattern

For `X -> B`, the ordinary setting has relative Kähler differentials `Omega(X/B)`. A morphism `f: X -> Y` over `B` induces

$$
f^*\Omega_{Y/B}\longrightarrow\Omega_{X/B}.
$$

This is the geometric pattern behind reverse differentiation. Relative differentials also have their stated base-change compatibility. [S3]

In the smooth setting, derivations respect smooth operations:

$$
d\Phi_h(a_1,\ldots,a_n)
=
\sum_i
\Phi_{\partial_i h}(a_1,\ldots,a_n)\,da_i.
$$

The smooth cotangent object enforces this rule. Using arbitrary algebraic derivations of the underlying real algebra would change the semantics. [J1, J2]

On smooth manifold domains, the cotangent sheaf is represented by a vector bundle. At singular objects it can be a more general module sheaf. A geometric cotangent object may therefore exist even when a dense numerical reverse rule is not available.

### 9.2 Reverse maps retain basepoints

For a supported smooth map `f: U -> Y`,

$$
B_f(x,\eta)=D f_x^*(\eta),
\qquad
\eta\in T^*_{f(x)}Y,
\qquad
B_f(x,\eta)\in T_x^*U.
$$

The associated bundle map is

$$
f^*T^*Y\longrightarrow T^*U
$$

over `U`. It is not a basepoint-free function `T*Y -> T*U`.

The proposed public vocabulary is:

~~~text
let dx = pullback(f, x, eta);
let cotangent_type = CoTangent(X, x);
let gradient = grad(loss)(x);       // uses the declared metric
~~~

The seed must belong over the actual output `f(x)`. Matching array shapes is insufficient to justify the dependency.

The geometric vocabulary may expose `Omega` and its induced maps. A mandatory public JVP, tangent functor, or full-Jacobian interface is not part of the initial numerical AD core.

### 9.3 Differentials and gradients

For a real-valued loss `L`, reverse mode first computes the covector

$$
dL_x=B_L(x,1).
$$

A gradient additionally uses a nondegenerate metric identification:

$$
\operatorname{grad}_g L(x)=g_x^{-1}(dL_x).
$$

A declared Euclidean default is convenient on **dimensionless** standard coordinate objects, or when the programmer has explicitly supplied compatible metric scales. An arbitrary scheme or singular module does not receive a metric automatically. In particular, an affine parameter chart with $x$ of dimension length and $t$ of dimension time cannot silently inherit

$$
dx^2+dt^2:
\qquad [dx^2]=[\mathrm{length}]^2,
\quad [dt^2]=[\mathrm{time}]^2.
$$

Those summands lie in different dimension lines. For a dimension-graded parameter chart with coordinates of degrees $d_i$, a metric valued in a common line $L_h$ needs coefficients

$$
g_{ij}\in L_{h-d_i-d_j},
\qquad
g=\sum_{i,j}g_{ij}\,dx^i\otimes dx^j;
$$

its nondegeneracy and required symmetry remain separate obligations. A concrete dimensionless metric may use declared scales $\ell_0$ and $t_0$, such as $(dx/\ell_0)^2+(dt/t_0)^2$. If the loss itself is $L_s$-valued, its differential is also $L_s$-valued and raising an index with an $L_h$-valued metric produces the appropriately graded tangent-valued quantity; it does not magically erase units. Unless the relevant metric and conversion data are present, `grad` on mixed-dimension parameters is rejected with **missing metric / incompatible dimensions**, even though the covector `dL` can still be well defined. This makes the choice of gradient descent geometry, and hence its dependence on units and scales, explicit (Sections 6.6 and 15).

Complex numerical programs are differentiated over their underlying real geometry by default. A Hermitian profile can represent real cotangents through

$$
\langle A,B\rangle_{\mathbb R}
=
\operatorname{Re}\operatorname{tr}(A^\dagger B).
$$

Conjugation appearing in this explicit metric representation does not change the nonconjugating tensor contraction of Section 6. Holomorphic differentiation is a separate capability.

### 9.4 Smooth-open correctness

A primitive specifies its mathematical domain, numerical failure behavior, and backward implementation. On its admitted smooth open, the backward implementation must equal the true cotangent pullback.

For `f: U -> Y` and `g: V -> Z`, composition is valid on

$$
W=U\cap f^{-1}(V),
$$

and reverse composition satisfies

$$
B_{g\circ f}(x,\zeta)
=
B_f\bigl(x,B_g(f(x),\zeta)\bigr).
$$

These statements are library and compiler proof obligations. Users do not carry a universal domain, smoothness, or evidence-provenance ledger through every expression.

Structural types encode facts useful for composition. Private constructors and operation-local checks establish supported value-dependent conditions. Numerical tests at a point do not prove smoothness on an arbitrary neighborhood.

No `C<N>` or `c<N>` regularity budget is introduced. Unsupported smoothness questions are not answered by silently lowering a regularity counter.

### 9.5 Boundaries and selected backward rules

Ordinary value evaluation and differentiation have different domains.

For example, `abs(x)` and `relu(x)` are pure value functions but not globally smooth. A library may specify a selected backward convention at a kink. Such a convention is not the classical derivative there.

An optimizer must preserve the requested derivative semantics as well as values. Consider

$$
f(x)=\operatorname{relu}(x)-\operatorname{relu}(-x)=x.
$$

If both ReLU occurrences use the selected slope zero at zero, their compositional selected backward gives zero there; replacing the program by `x` gives one. A value-only rewrite changes that contract.

On a primitive-regular open, ordinary derivative correctness is the target. That open need not include every point where the composite value function happens to be smooth. For example, a constant expression built through `abs(0*x)` can lie outside the primitive's admitted regular domain at every input.

Generalized gradients, distributions, and conservative-field semantics are possible separate extensions. They must have distinct names and contracts.

### 9.6 Closure-free reverse execution and higher order

A reverse transformation may generate independent code and explicit residual data:

~~~text
(y, saved) = primal_with_residuals(f, x);
dx = backward_code(saved, eta);
~~~

This is an implementation sketch, not an additional mandatory public API. The residual has ordinary ownership and lifetime rules.

Higher reverse differentiation requires the backward program's primal and residual dependencies to remain differentiable. Freezing saved factors can produce a valid first derivative and an incorrect second derivative.

On a smooth manifold, differentiating a covector field is not automatically an intrinsic Hessian tensor. A covariant Hessian requires a connection or an appropriate special case. Differentiating `grad` also differentiates its metric when that metric varies.

### 9.7 Physical response is not merely automatic differentiation

A derivative of a predicted observable with respect to a parameter is a mathematical sensitivity. Identifying it with a physical response coefficient may additionally require an equilibrium state, a preparation protocol, causality, a source coupling, a limit order, or a fluctuation–dissipation or Kubo-type argument.

Vastitas should allow those hypotheses to be represented and checked where possible. It must not relabel `grad(observable)` as an experimentally meaningful susceptibility or transport coefficient solely because the derivative exists. Noncommuting limits, critical singularities, and approximate solvers also belong to the response contract.

<!-- draft-v0.3:9:end -->

<!-- draft-v0.3:10:start -->
## 10. Eigen as spectral geometry

### 10.1 Exact algebraic denotation

Let `R` be a commutative ring, `V = R^n`, and `H: V -> V`. Define

$$
\chi_H(\lambda)=\det(\lambda I-H),
\qquad
A_H=R[\lambda]/(\chi_H),
\qquad
\Sigma_H=\operatorname{Spec}(A_H).
$$

The monic polynomial gives a finite free coordinate algebra of rank `n` over `R`. Section 10.3.2 proves the corresponding comparison with the smooth quotient for hyperbolic families over an ordinary smooth manifold, including the Hermitian case.

Give `V` an `A_H`-module structure by

$$
\lambda v=Hv.
$$

Cayley–Hamilton makes this action well-defined. Equivalently,

$$
M_H\cong
\operatorname{coker}
\left(
\lambda I-H:R[\lambda]^n\longrightarrow R[\lambda]^n
\right).
$$

The proposed exact meaning of `eigen(H)` is

$$
\operatorname{eigen}(H)
=
(\Sigma_H,\mathcal F_H),
\qquad
\mathcal F_H=\widetilde{M_H},
$$

together with the structural projection and identification of the pushed-forward module with `V`. The coordinate action recovers `H`. This construction extends locally to finite locally free bundles and glues.

This design deliberately retains both the characteristic scheme and the spectral module. The module need not be a line bundle.

### 10.2 Multiplicity and Jordan structure

For

$$
H_0=aI_2,\qquad
H_J=
\begin{pmatrix}
a&1\\
0&a
\end{pmatrix},
$$

both characteristic schemes have coordinate ring

$$
K[\varepsilon]/(\varepsilon^2),
\qquad
\varepsilon=\lambda-a.
$$

The action of `epsilon` on `M_H` is zero for `H_0` and nonzero for `H_J`. The spectral module distinguishes the operators.

Replacing the characteristic scheme by the reduced set of eigenvalues loses multiplicity. Replacing its defining ideal by the module's annihilator can also change the characteristic scheme. Neither is an innocent optimization.

For an algebra map `R -> S`,

$$
A_{H_S}\cong A_H\otimes_R S,
\qquad
M_{H_S}\cong M_H\otimes_R S.
$$

These identifications follow from the characteristic polynomial and module-action presentation. A naive kernel-of-eigenvectors construction does not supply the same unrestricted base-change behavior.

### 10.3 Smooth spectral families

#### 10.3.1 The real parameter and the spectral hypothesis

For a smooth Hermitian family over an ordinary smooth manifold `B`, the characteristic polynomial has real smooth coefficients and every fiber polynomial has only real roots, counted with multiplicity. The corresponding smooth spectral object is the zero locus in `B × R` with coordinate algebra

$$
S_H=C^\infty(B\times\mathbb R)/(\chi_H).
$$

The generated ideal is retained; taking the reduced zero set would discard information. A cokernel presentation of `lambda I-H` supplies associated module data, and the descriptor retains the original bundle and operator.

The real-root condition matters before any choice of Riesz projector. If a real characteristic polynomial has no real root on a fiber, its smooth reciprocal exists on that real line and the fiber quotient is zero. For the rotation generator

$$
H=\begin{pmatrix}0&-1\\1&0\end{pmatrix},
\qquad
\chi_H(\lambda)=\lambda^2+1,
$$

the real smooth spectral scheme is empty.

The precise algebraic hypothesis for the comparison below is hyperbolicity: all roots of the monic polynomial are real in every fiber. Hermitian families satisfy it, but it does not require normality. A nonnormal real-spectrum family may satisfy it; the rotation example is normal and does not. Hermitian data remain the initial numerical scope because they also provide the metric and cluster structure used in Section 10.5.

For complex Hermitian data, `S_H` is still a real smooth ring. The spectral module uses its complexification as a coefficient algebra, retaining the complex structure explicitly. Numerical AD uses the underlying real parameter geometry.

#### 10.3.2 Hyperbolic polynomial comparison lemma

Let `B` be a finite-dimensional Hausdorff, second-countable smooth manifold without boundary. Let

$$
p(b,\lambda)=\lambda^n+a_1(b)\lambda^{n-1}+\cdots+a_n(b),
\qquad a_j\in C^\infty(B),\quad n\geq1,
$$

and suppose `p(b,-)` has only real roots for every `b`. Then the canonical comparison

$$
\iota_p:
C^\infty(B)[\lambda]/(p)
\longrightarrow
C^\infty(B\times\mathbb R)/(p)
$$

is an isomorphism of ordinary \(C^\infty(B)\)-algebras. The source acquires its smooth-ring structure through this isomorphism. In particular, the target is free of rank `n` over `CInf(B)` with basis
\(1,\lambda,\ldots,\lambda^{n-1}\).

Here is a proof using parameter-dependent Malgrange–Mather division, whose smooth germ form is recalled in [T1, Introduction].

1. **Injectivity.** By monic polynomial division, it suffices to consider a remainder `r` of degree less than `n`. If `r=p*q` for a smooth `q(b,lambda)`, then, for each fixed `b`, the polynomial `r(b,-)` vanishes at every real root of `p(b,-)` to at least that root's multiplicity. There are `n` roots counted with multiplicity, so `r(b,-)=0`. Its smooth coefficients therefore vanish on `B`.

2. **Local division near the roots.** Fix `b0`. Factor `p(b0,-)` into the relatively prime powers corresponding to its distinct real roots. The coefficient map for multiplying these coprime monic factors has invertible derivative, so the implicit function theorem gives smooth monic cluster factors `p_j(b,lambda)` on a neighborhood `U`. After shrinking `U`, their roots remain in disjoint intervals around the original roots. Apply smooth division near each cluster to an arbitrary `h` in `CInf(B × R)`, obtaining a remainder `r_j` of degree less than `deg(p_j)` with coefficients smooth on `U`. No smooth labeling of individual roots is required.

3. **Combine the local remainders.** The factors remain pairwise comaximal in `CInf(U)[lambda]`: their resultants are nonzero after shrinking `U`. Polynomial Chinese remaindering gives a remainder `r` of degree less than `n` satisfying `r = r_j mod p_j`. Near each root cluster, `h-r` is smoothly divisible by `p` because the other factors are units there. Away from the roots, divide directly by the nonvanishing `p`. The quotients agree on overlaps, since the complement of the zero locus is dense.

4. **Globalize.** Injectivity makes the remainder unique on every base overlap. The coefficient functions therefore glue over `B`, yielding `h=p*q+r` globally. This proves surjectivity. A partition of unity could also globalize local divisions; uniqueness makes it unnecessary here.

For the projection \(\pi:\Sigma_p\to B\), applying this argument on each open subset of `B` gives

$$
\pi_*\mathcal O_{\Sigma_p}\cong\mathcal O_B^{\oplus n}
$$

as modules. This is the specific finite-free, hence flat, statement justified for this smooth spectral construction, including at collisions. It does not assert that the spectral space is a smooth manifold, that the projection is a submersion, or that individual eigenvalue branches are smooth.

The comparison is natural under smooth base change between manifolds satisfying these hypotheses: the unique polynomial remainder pulls back to the unique remainder of the pulled-back function. The module-action presentation of Section 10.1 can consequently be transported through the comparison; locally for a bundle, the action remains `lambda*v=H*v`.

This lemma settles the stated manifold/hyperbolic case. It is not an automatic extension to arbitrary singular or nonreduced `CInfScheme` bases. Those bases and other smooth spectral representations require additional arguments.

#### 10.3.3 Complex parameters and multiple roots

For spectra that are not confined to the real line, an explicit candidate uses `z=x+i*y` in
\(\mathbb C\cong\mathbb R^2\) and the smooth quotient

$$
S_{\mathbb C}
=
C^\infty(B\times\mathbb R^2)/
(\operatorname{Re}\chi_H,\operatorname{Im}\chi_H).
$$

This records the real-geometric zero locus of the complex characteristic equation. At a simple root, Cauchy–Riemann gives

$$
\det
\frac{\partial(\operatorname{Re}\chi_H,\operatorname{Im}\chi_H)}
     {\partial(x,y)}
=
|\partial_z\chi_H|^2\ne0.
$$

The implicit function theorem therefore yields a smooth local eigenvalue point over the real base. This construction applies to non-real spectra whether or not the operator is normal.

At multiple roots, the same two-equation quotient has a different infinitesimal structure from the complex polynomial spectral algebra. For example, let `chi_t(z)=z*z-t` with real parameter `t`. Its fiber quotient is

$$
D_t=C^\infty(\mathbb R^2)/(x^2-y^2-t,\,2xy).
$$

For `t != 0` the two zeros are simple and \(D_t\cong\mathbb R\times\mathbb R\). At `t=0`,

$$
D_0\cong
\mathbb R[x,y]/(x^2-y^2,xy),
$$

with real basis \(1,x,y,x^2\). The cubic monomials vanish, so finite Taylor expansion identifies this polynomial quotient with the smooth one. The real fiber dimension jumps from two to four. After complexifying these structure algebras the complex dimensions also jump from two to four, whereas \(\mathbb C[z]/(z^2-t)\) always has complex dimension two.

Thus the simple-root construction does not establish a rank-`n` finite-free family through complex multiple roots, or a preservation theorem for complex spectral multiplicity. A supported complex extension must specify the intended local algebra and module, and prove its comparison separately.

An incidence construction can additionally retain eigenlines or invariant subbundles. Its fibers may be singular or change dimension; it does not itself choose a globally smooth eigenvector.

### 10.4 A lazy, information-preserving interface

~~~text
let spectral = eigen(H);                 // retain validated immutable H
let Sigma = spectral.scheme();           // geometric descriptor
let F = spectral.module();               // associated module descriptor

let values = spectral.values()?;         // checked numerical observation
let cluster = spectral.cluster(selector)?;
let E = cluster.bundle();
let h = cluster.operator();              // h: E -> E
~~~

The geometric accessors can be lazy. Descriptor construction does not require a characteristic-polynomial expansion, sheaf enumeration, or eigensolver call.

The numerical backend may use private frames. Their choices do not define the mathematical identity of `E` or `h`.

A numerical output depends on its representation policy and error behavior. Computing sorted eigenvalues at one input does not establish a smooth branch through nearby inputs.

### 10.5 Separated Hermitian clusters

For a Hermitian family and a contour separating a cluster from the rest of the spectrum,

$$
P(H)=\frac{1}{2\pi i}\oint_\Gamma(zI-H)^{-1}\,dz.
$$

This gives the cluster bundle `E = im(P)` and restricted operator `H_E` on the corresponding smooth domain. Internal collisions are allowed; external separation is essential.

For a perturbation `V`, write `P_perp = I-P`. The off-diagonal derivative is determined by

$$
H_\perp X-XH_E=-P_\perp VP,
\qquad
X=P_\perp XP,
$$

and

$$
\dot P=X+X^\dagger.
$$

The external spectral gap controls this solve. No denominator from an internal eigenvalue splitting is needed.

At a degenerate eigenspace, the compressed perturbation

$$
V_E=(PVP)|_E
$$

retains the first-order splitting operator. It depends linearly on `V`; extracting its ordered eigenvalues generally does not.

For general nonnormal operators, a Riesz projector can be oblique. It must not be identified with the metric orthogonal projector onto the same invariant subspace. This metric issue is separate from the real-spectrum requirement of Section 10.3: non-real spectral points are already absent from the real-line smooth realization. The initial numerical solver scope is Hermitian; broader observations require an explicit choice of spectral geometry and a separate numerical capability.

### 10.6 A minimal singularity example

Consider

$$
H(x,y)=
\begin{pmatrix}
x&y\\
y&-x
\end{pmatrix}.
$$

Its characteristic equation is

$$
\lambda^2-x^2-y^2=0.
$$

The branches `+sqrt(x^2+y^2)` and `-sqrt(x^2+y^2)` are not differentiable at the origin. Along dual numbers with `x=epsilon*a`, `y=epsilon*b`, and `lambda=epsilon*c`, the characteristic equation becomes `0=0` and loses the constraint on first-order splitting.

The retained operator still records the perturbation matrix. This is why the spectral scheme alone is insufficient, and why first-order tangents of a scalar equation must not be mistaken for smooth selected eigenvalue derivatives.

The full two-dimensional cluster is smooth through the origin. A single-eigenvalue cluster loses separation there. The invariant observation

$$
\operatorname{tr}(H^2)=2(x^2+y^2)
$$

is smooth throughout.

This example illustrates the physics-facing value of retaining geometry: a smooth invariant can pass through a degeneracy even when individual eigenvalue branches or eigenvectors cannot. The observable's relation to an actual experiment remains a separate question.

<!-- draft-v0.3:10:end -->

<!-- draft-v0.3:11:start -->
## 11. SVD as geometry with a retained map

### 11.1 Metrics and the connecting operator

SVD starts with

$$
A:V\longrightarrow W
$$

and declared positive-definite metrics. The original connecting map must be retained.

Gram operators alone lose information. For `A = exp(i*theta)` in one complex dimension with standard Hermitian metrics, both Gram operators equal one, while the map still carries its phase.

A useful exact specification is the graded Hermitian dilation

$$
D_A=
\begin{pmatrix}
0&A^\dagger\\
A&0
\end{pmatrix}
:V\oplus W\longrightarrow V\oplus W,
$$

with

$$
\Gamma=\operatorname{diag}(I_V,-I_W),
\qquad
\Gamma D_A\Gamma=-D_A.
$$

Its spectral geometry, grading, and identified ambient summands retain `A`. This is a denotation, not a requirement to form the dense dilation in production.

### 11.2 Positive singular clusters

For a separated positive singular cluster, the output contains

$$
E_R,\quad E_L,\quad
a=A|_{E_R}:E_R\longrightarrow E_L
$$

with inclusions satisfying

$$
Ai_R=i_La,
\qquad
A^\dagger i_L=i_Ra^\dagger.
$$

~~~text
let singular = svd(A);
let cluster = singular.cluster(positive_selector)?;
let ER = cluster.right_bundle();
let EL = cluster.left_bundle();
let a = cluster.map();                    // ER -> EL
~~~

This interface does not select public singular-vector frames. A trace belongs to an endomorphism such as `adjoint(a) * a`, not to an arbitrary map between distinct endpoints.

At zero, `ker(A)` and `ker(adjoint(A))` are distinct objects. Rectangular nullspaces may have different dimensions and no canonical pairing. Rank changes need not define a fixed-rank bundle family.

### 11.3 Smooth observations and numerical algorithms

Repeated positive singular values do not prevent every smooth observation. For full column rank,

$$
A=QB,\qquad
B=(A^\dagger A)^{1/2}>0,\qquad
Q^\dagger Q=I,
$$

and the derivative of `B` satisfies

$$
B\dot B+\dot B B
=
\dot A^\dagger A+A^\dagger\dot A.
$$

Its spectral denominators are sums of positive singular values. The rank and conditioning hypotheses still matter.

At a rank-changing boundary, the scalar example `svdvals([x]) = |x|` already rules out a general classical derivative. Symmetry in singular values alone does not repair that boundary.

Production SVD should use a numerically appropriate direct algorithm. The semantic dilation and Gram formulas do not mandate a numerically unstable normal-equations implementation.

In many-body approximations, truncating a singular spectrum is a model and algorithmic choice. A cutoff, discarded weight, and bond-dimension policy must be recorded by the operation that imposes them; they are not implied by the exact `svd` denotation.

<!-- draft-v0.3:11:end -->
