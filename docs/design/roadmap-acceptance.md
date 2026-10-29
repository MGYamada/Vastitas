# Implementation roadmap, acceptance criteria, and open questions

[Design index](../design.md) · [References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:14:start -->
## 14. Initial implementation sequence

The sequence below is a proposal, not a release schedule.

| Stage | Concrete deliverable | Completion criterion |
| --- | --- | --- |
| 0. Semantic skeleton | Small object/point/morphism core, explicit setting/base, nominal endpoints | A constructed object can be passed and returned with an associated point |
| 1. Pure executable core | Independent lambdas, whole-function assembly with compatible declarative deltas and scoped impact grants, finite nominal-and-static-capability dispatch checking, storage ownership, and basic linear algebra | Explicit-dependency programs execute; obligation transfer and repair work; delta merge is order-independent; unresolved ambiguity, unauthorized takeovers, missing coverage, captures, and stale environments are rejected |
| 2. Ordinary affine geometry | Supported exact rings, `Spec`, polynomial maps, module presentations, fiber products | Dual numbers and affine base change retain their scheme structure |
| 3. Smooth affine geometry and reverse AD | `CInfScheme` descriptions, admitted smooth primitives, dependent cotangents | Reverse composition works on a stated smooth fragment |
| 4. Bundles and tensor diagrams | Finite bundle presentations, Grassmannian constructors, common `⊗`, linear ports, and a finite dimension-grading profile | Subbundle operations and contractions preserve endpoints and ownership; incompatible degree arithmetic and dimensionally invalid default metrics are rejected |
| 5. Spectral observations | Lazy eigen/SVD descriptors, Hermitian clusters, direct numerical adapters | Invariant outputs and cluster derivatives work through internal degeneracies |
| 6. First physical-model vertical slice | One finite parameterized model with declared assumptions, dimension-graded quantities, an intrinsic observable, an approximation policy, and separately keyed numerical and evidence records | The system preserves model/observable identity; changing model, policy, or dataset versions invalidates prior comparisons and cannot silently present computation or formal proof as empirical validity |
| 7. Broader geometry and physics | Supported gluing, additional monoidal profiles, richer exact/numerical methods, and domain-specific scientific libraries | Each extension states and meets its own mathematical, numerical, and physical interpretation obligations |

Both geometric settings belong in the architecture from the beginning. Staging their implementations does not demote either to an afterthought or equate their algebras.

The first executable path should be small enough to inspect: construct a supported geometry, define a map, obtain a numerical realization, differentiate a scalar observation, and lower its tensor operations. The first Physics 2.0 demonstration should then add a physical interpretation, a model regime, a solver policy, and an explicit distinction between a prediction and an observation.

General stacks, derived schemes, cotangent complexes, arbitrary infinite-dimensional objects, full interacting quantum field theory, general renormalization, and comprehensive nonsmooth calculus are later extensions. They should not be required to execute the first example. Nor should the label “Physics 2.0” be used to declare an unimplemented physical-model library finished.

<!-- draft-v0.3:14:end -->

<!-- draft-v0.3:15:start -->
## 15. Acceptance examples and diagnostics

These are design acceptance criteria for a future implementation. They are not reports of tests already passing.

| Example | Required outcome |
| --- | --- |
| Return `{X, x: Point<X>}` from a function | Preserve the association when the package is opened |
| Identify `Spec(K[epsilon]/epsilon^2)` with `Spec(K)` because ordinary points coincide | Reject that identification without a valid isomorphism |
| Realize `R[epsilon]/epsilon^2` smoothly | Retain the dual-number algebra; do not radicalize the ideal |
| Realize `R[x]/(x*x+1)` smoothly | Obtain the zero ring and empty smooth spectrum |
| Compare polynomial and smooth spectral algebras for a hyperbolic family over a smooth manifold | Use the isomorphism in Section 10.3.2 and retain rank `n` through collisions |
| Infer degree-two finite freeness for the real two-equation model of `z*z-t` through `t=0` | Reject that inference; the fiber dimension changes from two to four |
| Compute `Affine(K,2) × Affine(K,3)` | Obtain affine dimension five over the same base |
| Tensor the standard rank-two and rank-three linear affine objects | Obtain the rank-six linear object, with the linear structure identified |
| Tensor two arbitrary `Scheme` values as vector spaces | Diagnose the missing linear structure |
| Connect equal-sized ports from unrelated endpoints | Diagnose the endpoint mismatch |
| Reuse a tensor through two fresh occurrences | Accept lawful wiring without duplicating an existing endpoint |
| Mutably borrow one dense tensor independently through two factor ports | Reject unless storage disjointness or another valid access rule is established |
| Contract complex values through algebraic dual evaluation | Perform no implicit conjugation |
| Capture a runtime parameter in an independent lambda | Diagnose the capture and identify the explicit parameter needed |
| Exclusively borrow an `Open` function and return it with an unresolved overlap | Preserve the added methods and transfer every residual obligation to the lender |
| Edit a function through its owner while an exclusive borrower holds it | Reject the competing edit authority |
| Merge the same complete declarative method delta through diamond dependencies | Deduplicate exactly, including contributor and region metadata |
| Assemble compatible declarative deltas from libraries B and C in the opposite order | Produce the same final method family, impact check, and sealing result |
| Let a normal library extension inspect `Open` and add `f(T,T)` only if a prior method is absent | Reject as a history-reading ordinary delta; permit only a separately identified, ordered integration action |
| Publish `f(TB,Any)` and `f(Any,TC)` without a resolver | Reject completion with a witness in `(TB,TC)` |
| Add `f(TB,TC)` through a later whole-function borrow | Accept when the entire final family and callable domain pass the checks |
| Contribute `f(Int,Int)` over owner's `f(Number,Number)` with `(Int,Int)` outside the borrower's approved $R_B$ | Reject the silent takeover even though there is no ambiguity |
| Contribute the same `f(Int,Int)` with `(Int,Int)` explicitly approved in $R_B$ | Permit the changed selection if all final checks pass; invalidate dependent certificates from the old environment |
| Give B the region `(TB,Any)` and C the region `(Any,TC)` with overlapping intersection | Permit overlapping regions without minting separate intersection ownership; check each final winner against its own region |
| Repair all original pair overlaps but leave a triple-intersection ambiguity | Reject completion and report the remaining most-specific candidates |
| Declare an empty generic function | Accept construction; reject any nonempty callable-domain promise until covered |
| Select a callable domain excluding an unresolved ambiguity elsewhere in the same admitted family | Reject completion; narrowing the public domain does not discard an obligation |
| Add a concrete subtype that inhabits two formerly disjoint abstract regions | Recheck the affected families before accepting the new environment |
| Install the same stable method through diamond dependencies | Deduplicate that identity; reject distinct competing definitions with the same canonical signature |
| Add a method that changes a previously unique target | Reject if outside its approved region; otherwise recheck or invalidate dependent compiled assumptions even if no ambiguity appears |
| Select methods by finite static nominal types and declared `HasMetric` or braiding capability atoms | Resolve with the nominal/capability product order; reject any remaining tie at a feasible key |
| Dispatch on a capability inferred from mutable runtime state or an unnormalized, open-world trait | Reject as outside the decidable static key fragment |
| Select a method using a lifetime-dependent capability predicate | Reject that dispatch condition unless selection is proved independent of the erased information |
| Share a reference to a completed function among several callers | Allow repeated calls without duplicating edit authority |
| Request `grad` without an appropriate metric interpretation | Diagnose the missing structure |
| Request default Euclidean `grad` on a parameter chart with length coordinate $x$ and time coordinate $t$ | Reject as missing metric/incompatible dimensions: $dx^2+dt^2$ is not a valid scalar sum |
| Supply positive scales $\ell_0,t_0$ and the metric $(dx/\ell_0)^2+(dt/t_0)^2$ on that chart | Allow supported `grad` with the graded cotangent and metric checks satisfied |
| Query eigenvalues at an internal Hermitian collision | Permit supported pointwise values without claiming smooth ordered branches |
| Differentiate a separated cluster containing an internal collision | Use the cluster rule and its external-gap conditions |
| Differentiate a scalar singular-value observation at zero | Report the classical-derivative boundary or use an explicitly requested convention |
| Request an unavailable numerical realization | Preserve the symbolic object and explain the missing capability |
| Assign a physical interpretation to a parameter-dependent operator on the wrong base | Diagnose inconsistent model/observable geometry |
| Add quantities of different degrees in the monoidal dimension profile | Reject the operation or demand an explicit dimensionally valid map |
| Form `sqrt(Hz)` as a dimension degree | Admit $-\tfrac12[\mathrm{time}]$ in the rationally graded profile; separately check the value's square-root domain |
| Declare `c = hbar = 1` and then cross an undeclared model boundary | Preserve the explicit natural-unit line isomorphisms; reject an untracked dimensional erasure |
| Add two absolute Celsius temperature readings as affine points | Reject; allow subtracting readings to obtain a temperature difference and explicit origin/scale conversion |
| Take a private eigenvector frame as a gauge-invariant observable | Require an invariant construction or explicitly identify the gauge-dependent representation |
| Treat a finite-volume result as an established thermodynamic-limit value | Require a limit construction and its hypotheses, estimate, or stated conjectural status |
| Advertise a converged numerical kernel as a proof of model correctness | Preserve the numerical claim; do not assign formal or empirical status |
| Present a theorem proved inside a Hamiltonian model as proof that the Hamiltonian describes an experiment | Preserve the mathematical theorem and report the separate physical interpretation obligation |
| Feed unverified AI-generated code or a generated proof sketch into a certified pipeline | Require the same checks and trust boundaries as for human-authored input |
| Compare a computed prediction against measurements with unspecified units, regimes, or uncertainty | Refuse an unqualified empirical-validation claim; request or mark the missing metadata |
| Replace or recalibrate the dataset used by an accepted physical comparison | Mark the previous comparison stale and require a new comparison or a valid dependency-based reuse justification |
| Extend the axioms of a fixed theory without changing a referenced formal derivation | Retain the derivation when its exact proof dependencies and trust boundary remain valid; do not infer persistent empirical support |

A compact geometric example is:

~~~text
let K = RationalField;
let D = Spec(K[eps] / (eps^2));
let X = Affine(K, 1);

let infinitesimal_point: Point<X, D> =
    morphism(D, X, coordinate = eps);
~~~

The `D`-valued point retains first-order information even though the underlying reduced test object has only one point.

A compact differentiable spectral example uses the family from Section 10:

~~~text
let B: CInfScheme = Affine(CInfReal, 2);
let H = hermitian_family(B, [[x, y], [y, -x]]);
let spectral = eigen(H);

let loss = spectral.trace_square();
let derivative = grad(loss);              // dimensionless B: Euclidean metric admitted
~~~

The mathematical result is `loss(x,y) = 2*(x*x+y*y)` and `grad(loss) = (4*x,4*y)`, including at the origin. This observation can lower directly to `trace(H*H)`.

A request for an individual smooth eigenvalue branch through the origin is a different operation and does not inherit this derivative.

Interpreting the matrix `H(x,y)` as a physical two-level Hamiltonian would require further declarations: what `x` and `y` represent, their dimensions, the system's regime, which state and measurement protocol are used, and how a scalar such as `tr(H²)` is related to the observable being tested. **The Euclidean example above is explicitly dimensionless**: if the parameters are reinterpreted with incompatible physical dimensions, its implicit metric is no longer justified. The smooth mathematical invariant remains correct independently of that interpretation. This is the proposed distinction between a Math 2.0 acceptance example and a Physics 2.0 acceptance example.

Diagnostics should state the failed mathematical or resource condition, the relevant object or endpoint, and the operation that needs it. Useful categories include incompatible base, absent linear structure, unavailable realization, ambiguous dispatch, unauthorized winning region, history-dependent extension, invalid port reuse, missing metric or incompatible metric degrees, lost spectral separation, incompatible physical dimensions, stale evidence, an unproved limit, and an attempted promotion of numerical or formal evidence into empirical certainty.

<!-- draft-v0.3:15:end -->

<!-- draft-v0.3:16:start -->
## 16. Open design questions

The following choices require further work before a language specification can be frozen.

1. **Indexed object elaboration.** What is the smallest combination of generative identities, existential packages, and static indices that makes first-class geometry convenient?
2. **Executable presentations.** Which exact rings, smooth primitives, ideals, open restrictions, and finite atlases are admitted initially? Which operations remain symbolic?
3. **Equality and transport.** Which canonical constructions normalize definitionally, and where must users or libraries supply an explicit isomorphism?
4. **Linear affine syntax.** How does `Affine(K,n)` retain or expose its free-module structure without suggesting that every affine scheme has it?
5. **Smooth realization beyond the established cases.** Section 2.4 fixes the left adjoint, presentation independence, and affine pushout compatibility. The hyperbolic comparison lemma in Section 10.3.2 establishes the finite-free spectral algebra for Hermitian families over smooth manifolds. Remaining work concerns executable presentations, general module and sheaf constructions, non-affine gluing, singular or nonreduced smooth bases, and a complex multiple-root model with the intended infinitesimal structure.
6. **Sheaf capabilities.** Which finite-presentation operations are executable, and how are unsupported kernels or rank-changing objects reported?
7. **Function assembly formalization.** Section 8.3 fixes whole-function linear ownership, borrow-scoped impact regions, history-free declarative deltas, ordered integration as a separate operation, finite nominal/capability dispatch, and final coherence, coverage, and impact checks. Remaining work is the surface syntax, authorization and borrowing proofs, proof of partial-join confluence, symbolic checking beyond the finite product kernel, and separate-compilation certificate/invalidation implementation.
8. **Effects and resources.** How do execution contexts, random state, and foreign effects appear without weakening the pure core?
9. **Representatives.** What explicitly scoped coordinate or frame interface is useful while preserving the frame-independent ordinary API?
10. **Boundary derivatives.** Which selected backward conventions belong in the initial numerical library, and which rewrites preserve them?
11. **Higher-order support.** Which residual and solver rules are differentiable enough for repeated reverse transformations?
12. **Verification scope.** Which semantic claims should be proved first, and which numerical obligations initially rely on validation and documented hypotheses?
13. **Physical model vocabulary.** Which of states, dynamics, symmetries, constraints, observables, and assumptions belong in a minimal shared protocol, and which are domain-specific library abstractions?
14. **Units and dimensions (core resolved; interfaces open).** Section 6.6 fixes the dimension character group, oriented line-valued graded monoidal profile, rational powers, explicit natural-unit identifications, and distinct additive torsors for affine units. What minimal surface syntax, coherent frame transport, conversions across model boundaries, and dimension-graded numerical backends should implement that structure?
15. **Evidence boundary (invalidation resolved; inference open).** Section 13.4 fixes versioned dependency invalidation for comparison records and distinguishes monotone formal entailment from defeasible empirical support. What specific observation schemas, uncertainty models, calibration protocols, statistical comparisons, and sound record-reuse certificates should populate that mechanism?
16. **Asymptotic and effective theories.** How can approximation order, finite-size extrapolation, continuum or thermodynamic limits, and noncommuting limits be expressed and checked in useful restricted fragments?
17. **AI-assisted scientific development.** What proof-certificate, semantic-diff, provenance, and numerical-regression workflows provide trustworthy boundaries around generated programs and proposed physical models?

These questions refine the mechanisms. They do not reopen the decision to make `Scheme` and `CInfScheme` first-class, the v0.2 commitment to separate formal, numerical, and empirical claims, or the v0.3 decisions on graded dimensions and history-free ordinary extension.

<!-- draft-v0.3:16:end -->
