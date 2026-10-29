# Pure functions and static dispatch

[Design index](../design.md) · [References](history-references.md#18-mathematical-and-language-references)

> Historical design proposal: Draft v0.3, 26 October 2026 (JST). Original section numbering and qualifications are retained. This document does not assert current implementation or proof coverage; see the [repository README](../../README.md) for the implementation status.

<!-- draft-v0.3:8:start -->
## 8. Pure functions, independent lambdas, and dispatch

### 8.1 Purity and geometric structure

An ordinary function `Fn<A,B>` is not automatically a `Morphism<X,Y>`.

Purity excludes hidden observable state changes from the function's mathematical meaning. It does not imply continuity, smoothness, algebraicity, termination, or availability of a derivative implementation.

A morphism constructor must use an admitted structure-preserving program fragment, a checked construction, or an explicitly identified library trust boundary.

Division illustrates the distinction: a rational expression is a regular morphism on its appropriate open domain, not necessarily on the whole affine scheme.

### 8.2 Closure-free first-class functions

Independent anonymous functions take runtime dependencies explicitly:

~~~text
let loss = fn(parameters, batch, configuration) {
    model_loss(parameters, batch, configuration)
};
~~~

Immutable compile-time definitions may be referenced. A runtime lexical variable is not silently captured:

~~~text
let scale = read_scale();

let f = fn(x) { scale * x };          // rejected: runtime capture
let g = fn(scale, x) { scale * x };   // accepted
~~~

An explicit record containing code and data can be useful, but it must not become an implicit environment attached to an ordinary function value. Any such callable-object interface needs separately specified application and ownership rules.

“Monad-free” describes the intended core programming interface: pure dataflow and explicit resources do not require monadic wrapping or bind syntax. Closure freedom alone is not a proof of purity, and the design makes no claim that monads are mathematically impossible or unnecessary in every library.

### 8.3 Statically resolved multiple dispatch

Supported generic calls are compiled against a fixed, identified method environment. The compiler establishes a unique most-specific applicable method, or elaborates explicit control flow among known targets whose individual calls meet that requirement. There is no silent runtime generic-dispatch fallback.

Closure freedom helps expose dependencies. It does not ensure that every first-class function value is statically known. Runtime extents and ordinary runtime branches remain possible when the operations themselves are resolved.

The following mechanism distinguishes **linearity of edit authority and responsibility** from **commutativity of ordinary library contributions**. The first is a whole-function ownership discipline; the second arises from declarative method deltas that cannot inspect the family assembled so far. Neither alone establishes safe dispatch behavior: completion also checks coherence, coverage, and authorized impact. This is a proposed formal core, not an implemented or mechanically verified type system.

#### 8.3.1 Own the whole generic function

A generic function `f` is one identified object containing a finite family of methods. Its construction-stage ownership is linear: there is one owner, and an exclusive borrower may temporarily exercise that owner's authority over the whole family. Methods and signature intersections do not have independently transferable *linear ownership* or orphan-style extension rights.

An owner may move the function or lend it exclusively. Imports and aliases identify the same function; they do not duplicate its ownership or mint extension authority. A borrow for contributor $X$ also carries an **approved impact region** $R_X\subseteq K_\Theta$, chosen or granted by the owner or explicitly authorized integrator. The borrower cannot enlarge that grant unilaterally. This region is an immutable scope restriction on the whole-function borrow, **not** a second linear ownership token for every overlapping intersection. Returning a borrow preserves all contributed methods and returns all remaining obligations. The lender cannot continue editing through a suspended alias.

Function ownership carries both the authority to edit and responsibility for completing the function's acceptance conditions. A borrow's authority to contribute does not authorize its methods to change dispatch outside its declared region, even when no ambiguity results. Whole-function ownership also does not grant permission to select a target arbitrarily when several methods remain equally specific.

Construction occurs during elaboration or program assembly. After completion, ordinary code can share immutable callable references and call the function repeatedly without moving its owner on every call. These references carry no right to add methods. Runtime storage ownership, argument borrowing, and ownership of a function under construction are distinct checks.

The generic-function/method distinction agrees with Julia's conceptual model. Julia permits cross-module extension through explicit imports or qualified names; the proposed Vastitas mechanism makes completion a prerequisite of executable publication and checks silent replacement of a previously selected method as an *impact* question distinct from ambiguity. [JL1, JL2]

#### 8.3.2 Construction states and responsibility

Use the following metanotation; these are compiler states, not committed surface type names:

| State | Meaning |
| --- | --- |
| `Open<f; Theta, M, Omega, Lambda>` | The linearly owned function can be extended. `M` is its accumulated method family; `Omega` records unresolved coherence and call obligations; `Lambda` records contributions, approved regions, and their provenance. |
| `Ready<f; E, D>` | The function has passed the completion checks in immutable environment `E` and supports calls in declared domain `D`. |
| `&Ready<f; E, D>` | A shareable callable reference to that completed function in that environment. |

`Theta` records the type hierarchy, finite static capability atoms and their admissible combinations, and other facts used for dispatch. A final environment `E` identifies this type environment, the participating functions, method identities, bodies and contracts, their provenance and impact grants, the declared integration plan (if any), and the dispatch policy. It identifies the environment shared by the assembled program, not a different accidental snapshot for each importing library.

`Omega` and `Lambda` are tracked by the compiler, including through moves and exclusive borrows. A borrower may return an incomplete function for another authorized borrower or the owner to finish; a borrow boundary does not itself demand completion. No party can drop an obligation or erase contribution provenance while retaining or publishing the function. Aborting an unpublished assembly publishes no callable function.

An `Open` function cannot yet be executed through ordinary generic application. Its method bodies may refer symbolically to itself or to other functions under construction. Such bodies are checked under declared contracts, with remaining call obligations discharged before their dependency group becomes executable. This permits recursion without exposing an incomplete method family to execution.

#### 8.3.3 Applicability, ambiguity, and coverage

For a fixed arity $r$, let $C_\Theta$ be the finite admitted concrete nominal types and $A_\Theta$ a finite set of declared **static capability atoms**, such as the availability of a monoidal dual, braiding, or a specified metric-bearing profile. The initial extended key space is a finite set of feasible combinations

$$
K_\Theta\subseteq C_\Theta^r\times\mathcal P(A_\Theta),
\qquad \kappa=(T_1,\ldots,T_r;\mathcal A_\kappa).
$$

The feasibility relation and capability evidence are fixed by $\Theta$. Not every formal subset of capabilities need be realizable. Finite declared implications between capability atoms are normalized by closure before comparing required sets and available evidence—for example, if the profile declares one capability entails another, the key and signature normal forms must respect that implication. Capability resolution must be deterministic, based on compile-time facts, and independent of erased lifetimes or runtime observations. An operation requiring an actual metric also needs a specified **metric witness or profile identity**; the bare atom `HasMetric` does not construct one. Identity-dependent distinctions must remain static, explicitly admitted specialization information if they are used to select a method.

A method $m$ has a stable identity and a signature $\sigma_m=(S_1,\ldots,S_r;\mathcal R_m)$ with finite required capability set $\mathcal R_m\subseteq A_\Theta$. It is applicable when each $T_i<:_\Theta S_i$ and $\mathcal R_m\subseteq\mathcal A_\kappa$. The nominal-only fragment is recovered with $A_\Theta=\varnothing$.

Write \(\kappa\models_\Theta\sigma_m\) for applicability. In this kernel, define the product preorder by

$$
(S_1,\ldots,S_r;\mathcal R)\preceq_\Theta
(T_1,\ldots,T_r;\mathcal Q)
\quad\Longleftrightarrow\quad
\bigl(\forall i:\ S_i<:_\Theta T_i\bigr)\ \land\ \mathcal R\supseteq\mathcal Q,
$$

and use its strict part for $\prec_\Theta$. More specific nominal arguments and **more required static capabilities** both narrow applicability. Normalize aliases and admissible capability equivalences before comparing signatures. The relation must be a strict partial order on canonical signatures, with sound applicability containment; equal coverage on the current finite keys alone is not a specificity rule.

Define

$$
\operatorname{App}_\Theta(M,\kappa)
=
\{m\in M\mid\kappa\models_\Theta\sigma_m\},
$$

$$
\operatorname{Best}_\Theta(M,\kappa)
=
\left\{
m\in\operatorname{App}_\Theta(M,\kappa)
\ \middle|\
\nexists m'\in\operatorname{App}_\Theta(M,\kappa):
\sigma_{m'}\prec_\Theta\sigma_m
\right\}.
$$

There is ambiguity exactly where more than one undominated applicable method remains:

$$
\operatorname{Amb}_\Theta(M)
=
\{\kappa\in K_\Theta\mid
|\operatorname{Best}_\Theta(M,\kappa)|>1\}.
$$

The unresolved coherence obligations `Omega` represent this set, together with the conflicting method identities and their origins. A compiler may use symbolic regions instead of enumerating keys, but an empty reported obligation set must imply that this entire ambiguity set is empty.

Coverage is a separate condition. For a declared callable domain \(D\subseteq K_\Theta\), define

$$
\operatorname{Hole}_\Theta(M,D)
=
D\setminus
\{\kappa\in K_\Theta\mid
\operatorname{App}_\Theta(M,\kappa)\ne\varnothing\}.
$$

Completing `f` requires

$$
\operatorname{Amb}_\Theta(M)=\varnothing,
\qquad
\operatorname{Hole}_\Theta(M,D)=\varnothing.
$$

Ambiguity is checked across the whole family's admitted domain, including keys outside `D`. Choosing a smaller public domain cannot hide an unresolved ambiguity. Coverage is required only where calls are promised; a generic function need not implement every combination of types.

An empty family is unambiguous but covers no nonempty call domain. It can therefore be constructed and freely extended by its authorized holder without being prematurely treated as callable. Unknown applicability or overlap is not evidence of disjointness: completion must obtain a sound certificate or reject that unsupported case.

**Noninterference is an additional completion condition.** For each contributed method $m$ with contributor $X$ and approved borrow region $R_X\subseteq K_\Theta$, define its *final winning footprint*

$$
W_\Theta(m,M_{\mathrm{final}})
=\{\kappa\in K_\Theta\mid m\in\operatorname{Best}_\Theta(M_{\mathrm{final}},\kappa)\}.
$$

Sealing requires

$$
\boxed{\forall X\ \forall m\text{ contributed by }X:\quad
W_\Theta(m,M_{\mathrm{final}})\subseteq R_X.}
$$

Because this checks the **final family**, it neither privileges installation order nor requires separate linear rights for intersections such as $(T_B,T_C)\in R_B\cap R_C$. A method's region may be large, but a borrower cannot grant itself the entire domain as an escape hatch. Grants are interpreted as certified regions of the **final** $K_\Theta$; changes to the type graph or feasible capability keys require revalidation of their scope and authority. The same rule applies to owner-originating revisions with their explicitly recorded scope (which the owner may authorize broadly). An overlap-free takeover outside the approved region is rejected, while an authorized change inside it changes the environment identity and invalidates affected compiled assumptions. Coherence alone would not detect such a takeover.

#### 8.3.4 State transitions and repair

| Operation | Required transition |
| --- | --- |
| Declare a function | Create one `Open` owner with a fresh function identity and empty method family. |
| Grant a scoped borrow | Suspend the lender's edit authority; give one borrower an exclusive whole-function borrow with owner-approved $R_X$. |
| Contribute an ordinary extension | Submit a declarative delta of methods and source identities without reading the current family; merge it and retain its approved $R_X$. |
| Move the function | Transfer the same identity, family, grants, and all obligations; invalidate the old owner binding. |
| Return the borrow | Restore the lender with the merged family, contribution provenance, and all remaining obligations. |
| Perform explicit integration | An authorized assembly program may inspect a named intermediate family and select further deltas, but must declare and record its ordered dependency on that snapshot. |
| Seal a dependency group | Consume its `Open` owners into `Ready` ownership only after final ambiguity, coverage, authorized-impact, body, and dependency checks pass in one environment. |

A new method does not have to preserve coherence immediately. It may introduce an obligation that another authorized party later discharges. Adding a repair method triggers the same checks as any other addition. Intermediate diagnostic order is not the semantics of the resulting immutable family: ordinary deltas are combined by the rule in Section 8.3.6, and **only the final family is sealed**.

For example, using illustrative signatures:

~~~text
owner adds:       f(TB, Any)
borrower adds:    f(Any, TC)
pending region:  (TB, TC)

later borrower adds: f(TB, TC)
pending region:      discharged if the whole-family check succeeds
~~~

If `TBsub <: TB` and a subsequent extension adds `f(TBsub, Any)`, it conflicts with `f(TB, TC)` on `(TBsub, TC)`. That creates a new obligation. Cross-library subtyping is not prohibited by this mechanism; its consequences participate in the final check. The repair's *own* final winning region must also be within its contributor's approved grant.

Pairwise overlaps alone are not the acceptance criterion. With three arguments, repairing each original pair of broad methods can leave three repair methods tied at the triple intersection. Completion examines the final most-specific candidates, not a checklist saying that each old pair once received a repair.

For noninterference, suppose the owner initially supplies `f(Number, Number)` and borrower B adds `f(Int, Int)`. No ambiguity appears: `(Int, Int)` now selects B's method. If `(Int, Int)\notin R_B`, sealing **rejects** the takeover despite coherence and coverage. If the owner expressly granted that key, completion may accept the new selection after checking all remaining obligations and invalidating the prior environment's dependents. The region restriction protects ungranted calls, not historical behavior *inside* the grant.

Initial assembly is additive. Repeating the **same complete contribution record** through diamond dependencies is idempotent. Distinct definitions with the same canonical signature are a duplicate-definition error; import order does not choose a winner. Body replacement requires an explicit new build revision. Unrepresentable intersections and bodies whose contracts cannot be satisfied are legitimate reasons for a composition to fail.

An unresolved-obligation diagnostic identifies the function, the current owner or borrower, the conflicting method identities and source locations, a witness key or overlap region, and the completion boundary that cannot proceed. A noninterference diagnostic additionally identifies the winning contributed method, a witness key in $W_\Theta(m,M_{\mathrm{final}})\setminus R_X$, and the authority that would have to approve a broader region. It may suggest a resolving signature, but choosing the method's scientific meaning remains an implementation responsibility. A compiler or AI tool cannot discharge coherence or impact merely by suppressing a diagnostic or choosing an arbitrary priority.

#### 8.3.5 A decidable initial checking kernel

A concrete first checker can use this restricted fragment, enlarged just enough to cover the language's static monoidal capabilities:

- A finite, fully known nominal subtype graph with a specified set of concrete ground types; cross-library subtype edges are allowed.
- Fixed-arity method signatures that are products of nominal argument types, with `Any` as the top type, **and** a finite conjunction of named, compile-time capability atoms.
- A finite set of ground generic instantiations admitted by the compilation domain.
- An explicit finite table or decidable normalization of feasible capability evidence for each admitted ground key, fixed before method selection.
- No dispatch predicates whose truth depends on arbitrary program execution, unresolved open-world traits, lifetimes, runtime profile state, or erased generative identities.

The specificity relation is the nominal/capability product order of Section 8.3.3. Its canonical forms use the declared subtype graph and capability atoms even when two distinct signatures happen to have the same concrete inhabitants in the current build. A capability claim is an admissible static fact with identified evidence; it is not a silently evaluated predicate on a runtime value.

For example, `f(Linear, requires = {})` and `f(Any, requires = {HasMetric})` can both apply to a `Linear` key with an admitted metric. Neither signature dominates the other in the product order. Adding `f(Linear, requires = {HasMetric})` provides a more specific candidate there, subject to the usual final ambiguity, coverage, and contributor-impact checks. This illustrates why the finite kernel must know the capabilities used by tensor and `grad` libraries, rather than dispatching only on nominal types.

Enumerate the finite feasible keys $K_\Theta\subseteq C_\Theta^r\times\mathcal P(A_\Theta)$, compute applicable and undominated methods, check ambiguity and coverage, and for each contributed method enumerate its winning footprint and verify $W_\Theta(m,M_{\mathrm{final}})\subseteq R_X$. This terminates and decides **all three** completion conditions for the stated fragment. A capability powerset can be exponentially large; enumeration is a reference algorithm, and symbolic intersections and incremental checking may implement the same condition more efficiently.

The finite set must describe all keys permitted by the finalized interface or program, not a sample of observed calls. A reusable interface quantified over additional types remains conditional until instantiation or until a sound symbolic checker proves its obligations. An infinite specialization chain cannot be accepted merely by inspecting a finite prefix.

This kernel establishes an executable starting point, not a decision procedure for all Julia signatures or all of Vastitas's geometric types. Unions, inferred or open-world traits, arbitrary dependent predicates, variadic signatures, and broader parametric families require their own sound checking extensions. Monoidal profile capabilities whose evidence cannot be reduced to a finite static atom remain outside this dispatch fragment, even though they can still be ordinary typed operation preconditions. Ordered orphan rules are not prerequisites for this kernel: they can be viewed as conservative *syntactic approximations* to restrictions on authorized impact, not substitutes for the final semantic check.

#### 8.3.6 Library composition and fixed environments

A normal library extension is a **declarative delta** $\Delta_X$ produced without observing the current contents of `Open<f>`. It contains a finite set of contributions $(\mathrm{id}_m,\sigma_m,\mathrm{body}_m,\mathrm{contract}_m,X,R_X)$, with stable identities and an owner-approved scope $R_X$. A library may prepare such a delta against a declared interface; applying it requires ownership or an exclusive borrow of the *whole* generic function. The delta is not an independently transferable fragment of linear edit authority, and its record cannot grant itself a larger impact region.

For two compatible deltas, define $\Delta_X\sqcup\Delta_Y$ by union on stable contribution identities. Two copies of the **same full record**, including body, contract, contributor, and approved region, merge idempotently; inconsistent records for one identity or distinct method identities with the same canonical signature are conflicts, not priority choices. On compatible deltas the partial join is associative, commutative, and idempotent. The final method family is

$$
M_{\mathrm{final}}=M_{\mathrm{owner}}\cup
\bigcup_X\operatorname{methods}(\Delta_X).
$$

Coherence, coverage, and authorized-impact checks occur **after** this union. Ambiguous but otherwise well-formed unions can therefore await a later repair delta. There is no requirement that each intermediate accumulated family be coherent. Because the ordinary delta cannot inspect the current method set, two libraries cannot both implement a conditional “add `f(T,T)` if no such method exists” extension whose result depends on which was installed first. That would require an explicitly different assembly operation.

An authorized **integration action** may inspect an identified intermediate snapshot, diagnose the remaining obligations, and select or synthesize a repair delta. Such an action is kept outside the commutative library-extension fragment: the assembly program must specify its inputs, order, authority, and resulting contributions. A fixed integration plan can be checked and reproduced, but an arbitrary permutation of its state-reading steps is **not** claimed to be equivalent. Integration must respect the same approved-impact and sealing rules as any other contribution.

Libraries can be developed and checked against interfaces independently. Their artifacts retain declarative deltas and unresolved composition requirements. The program's assembly context holds the unique owner, applies the chosen deltas under scoped borrows, and retains residual obligations; an integration library can use a separately ordered action to provide cross-library methods. Independent acceptance of two libraries does not promise that their combination will need no additional methods or checks.

A component can refer to an imported function by its stable identity without capturing a partial method snapshot. The final environment is assigned consistently to those references. Mutually recursive dependencies are sealed as a group after their declared call contracts and bodies are checked.

Changing the subtype graph or feasible capability evidence can create overlap even without adding a method. A more-specific method may change a previously unambiguous target **inside a permitted impact region**. Any change to the dispatch-relevant nominal types, capability atoms or evidence, method records, approved grants, integration plan, bodies, contracts, or policy changes the environment identity and invalidates affected certificates and compiled assumptions. A new build must recheck them or justify reuse through sound dependency tracking. The dependency identity includes the normalized content of deltas, not their accidental application order.

Dispatch certificates, call elaborations, and scientific evidence use one underlying **versioned dependency graph**: a record names the assumptions, policies, datasets, environments, and artifacts on which it depends; changing an identity makes every dependent record stale until a sound reuse argument or recheck is supplied. This is an infrastructure mechanism, **not** a claim that coherence certificates and empirical support obey the same logical rules (Section 13.4).

There is no in-place runtime extension of a `Ready` environment in the initial design. This gives a simpler execution boundary than Julia's world-age mechanism, which manages which changing definitions are visible to running code. It does not eliminate build-time dependency tracking. [JL3]

Related modular multimethod research assigns checking responsibilities to extension modules and uses linking conditions to ensure that those responsibilities have been met. This is relevant precedent, but its soundness results do not prove Vastitas's proposed ownership mechanism. [MC1]

#### 8.3.7 Calls, erasure, and the full completion boundary

In addition to empty ambiguity, coverage, and authorized-impact obligations, sealing requires:

1. A valid whole-function ownership and borrowing derivation, with no outstanding edit borrow.
2. A consistent set of declarative delta records and recorded integration decisions, with each contribution's final winning footprint within its owner-approved impact region.
3. Well-formed method identities and signatures, and method bodies checked against every applicable exported call contract, including result, effect, and endpoint requirements.
4. An identified final environment for all executable dependencies, including recursive groups.
5. Applicability and specificity that are independent of information erased before target selection, including capability evidence.
6. Call elaboration that selects a unique known target or explicit control flow among known targets; unsupported unresolved generic calls remain errors.

Lifetimes, borrow-region relationships, and erased generative identities may establish that a call is well typed. They must not distinguish its dispatch target. A declared static capability atom **may** distinguish a target if its evidence and identity survive specialization; no unnormalized or erased trait obligation may do so. The check includes indirect dependencies, not just explicit annotations on a signature. Rust's specialization RFC explains why erased lifetime information and indirect trait dependencies matter here. [R1]

A static dimension or other static parameter can participate when it is an admitted specialization key retained in the selected code identity. Distinct reference constructors can likewise remain distinct types; excluding lifetime-dependent selection does not require identifying `T`, `&T`, and `&mut T`.

For every accepted call, its possible keys must lie within an admitted callable domain and satisfy its typing and resource preconditions. A globally coherent method family alone does not make a runtime-unknown function target statically known. Likewise, a unique selected method is not evidence that its body implements the intended scientific operation.

#### 8.3.8 Conditional dispatch lemma

Assume finite method families and feasible static capability keys, a strict partial specificity order with sound applicability, sound coverage and coherence checks, authorized winning footprints, valid whole-function ownership transitions, erasure-independent selection, and preservation of the finalized environment by lowering.

Then every well-typed call admitted through `Ready<f; E, D>` has one most-specific applicable method in `E`.

The argument is direct: coverage gives a nonempty applicable family; finiteness and the strict partial order give at least one undominated member; the empty ambiguity set gives at most one. The fixed environment and erasure condition preserve that choice during execution. **For the same final method set**, type facts, capability evidence, and dispatch policy, selection is independent of the order in which methods were installed.

Two additional conditional properties must be distinguished. **Delta confluence:** if all library extensions are declarative and their contribution records are compatible, applying the same multiset of deltas in any order produces the same final method family and thus the same completion verdict. This stronger assembly statement does *not* follow from linear ownership alone and does *not* extend to the separately ordered state-reading integration actions. **Bounded noninterference:** for a fixed $\Theta$ and a coherent covered baseline $M_0$, if $M_{\mathrm{final}}$ only adds methods subject to the impact rule, a call key outside the union of the new contributions' approved regions retains its former selected method. If it changed, some newly added method would have to be a final most-specific candidate there, contradicting its region constraint. The claim concerns selection, not scientific equivalence of changed bodies, and excludes changed type or capability facts without their required environment revalidation.

These are conditional lemmas about selection, declarative composition, and bounded impact, **not machine-checked theorems**. A complete Vastitas soundness theorem still needs formal typing, borrowing, delta compatibility, grant checking, body checking, call elaboration, and lowering proofs. Completion need not always be possible, and coherence does not prove termination, semantic compatibility *inside authorized impact regions* with older builds, or numerical correctness.

### 8.4 Effects at explicit boundaries

I/O, random sampling, external mutation, and device operations need explicit semantics. Random state can be passed as data where appropriate. Pure local state transitions can lower to imperative code.

A public effect system is not fixed by this draft. The first AD implementation targets deterministic pure regions; replaying arbitrary effects during checkpointing is outside that claim.

<!-- draft-v0.3:8:end -->
