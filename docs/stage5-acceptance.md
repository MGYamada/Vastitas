# Stage 5 spectral observations acceptance

This map links each acceptance condition of historical Stage 5 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 5 is a finite, checked profile of exact spectral
observations of polynomial matrix fields over QQ, on top of the smooth affine
profile of Stage 3 and the polynomial matrices of Stage 4
([tracker #806](https://github.com/MGYamada/Vastitas/issues/806)). It does not
include performance: the Fast like C verdict stays with #222.

The stage is in progress. Every condition below is Planned until its row
records evidence. The Reference and guide chapters, the protocol and
verification sections and the specification claims are written by the last
batch of the stage, and this map links them when they exist.

## Scope and decisions

The conditions are the checklist C1–C20 of #806, which turns the Stage 5
example of the [historical roadmap](guide/historical-roadmap.md#stage-5-spectral-observations)
into executable checks.

Decisions taken with the user (15 November 2026):

- **Core and branches.** The profile has polynomial matrix fields, the exact
  spectral pair, trace-power and characteristic-coefficient invariants with
  the gradients of Stage 3, and simple eigenvalue branches on a finite chart
  certified by a unit witness, with the branch differential and the
  eigenprojector. Numerical eigensolvers (#324) and the covers, image opens
  and cluster splits of #765 are outside it.
- **Daleckii–Krein.** The mathlib bridge proves steps 1 and 2 of #471, the
  typed Hermitian lift and the cotangent action with the pairing Re tr(KX),
  and that the emitted reverse Core of an accepted trace-power invariant
  computes the Daleckii–Krein cotangent composed with the derivative of the
  field. The C∞ comparison (#361), the general correspondence of #290 and
  pass preservation (#164) stay open.
- **Public home.** The vocabulary lives in `std::linalg::spectral`, as #337
  names it.

Design decisions of the plan that the user approved:

- **Field.** QQ only, as in Stages 3 and 4. Exact `Rat` stays inside the
  runtime.
- **Certificates.** The kernel computes the characteristic polynomial and the
  adjugate by the Faddeev–LeVerrier recursion and checks them by cofactor
  expansion. Every identity modulo χ is checked against a quotient that the
  kernel computes, so no theorem depends on a division routine. No
  certificate comes from the wire.
- **Fiber coordinate.** `eigen(H, t)` names the coordinate of the
  characteristic polynomial; it is the last variable of every polynomial in
  `A[t]`.
- **Symmetry.** `symmetric` is explicit and checked. It selects the pairing
  that the eigenprojector and the Daleckii–Krein statements use.
- **Invariants.** A trace power or a coefficient is an ordinary smooth map
  into the line. Its differential, its gradient and its compiled reverse pass
  are those of Stage 3.
- **Branches.** A branch observation takes the eigenvalue as an input. No
  primitive computes, orders or chooses an eigenvalue.

Approved provisional names: the families `FreeModule`, `Endomorphism`,
`Spectrum` and `Branch`; the declarations `free_module … = basis(…)`,
`endomorphism … = rows(…) of V [symmetric]`, `spectrum … = eigen(H, t)` and
`branch … = simple(S, localize = …, witness = …, exponent = …)`; the
morphisms `trace_power` and `char_coefficient`; the primitives `annihilates`,
`action_entry`, `on_branch`, `branch_differential` and `branch_projector`; the
code `E_SPECTRAL`; the limits `spectralRank` (4) and `spectralPower` (8).
[ADR 0001 §12](adr/0001-mathematics-first-stdlib.md#12-exact-spectral-pairs-and-simple-branches-of-polynomial-matrix-fields-amendment-2026-11-15)
admits the module.

### Roadmap sentences

| Roadmap sentence | How this profile meets it | Rows |
| --- | --- | --- |
| For an exact finite endomorphism H, retain its characteristic scheme and the module on which the coordinate acts as H | `eigen(H, t)` derives χ_H in `A[t]` and keeps H as the action of t; Σ_H is never replaced by a reduced or annihilator locus | C2, C3 |
| A scalar matrix and a nontrivial Jordan block can have the same characteristic polynomial and different module actions | 2I against the Jordan block with eigenvalue 2, and 0 against the nilpotent block: equal χ and invariants, different module observations | C3 |
| A numerical adapter must identify the observation it computes | No numerical adapter; every observation is exact and named. Numerical eigensolvers stay with #324 | — |
| For the symmetric matrix with rows (x, y) and (y, −x), the eigenvalues ±√(x² + y²) meet at the origin | The branch chart D(x² + y²) excludes the origin | C9 |
| tr(H²) = 2(x² + y²) has gradient (4x, 4y) everywhere for the declared dimensionless Euclidean chart | `trace_power(H, 2)` is a smooth map; its gradient through a Euclidean metric with a dimensionless reading is (4x, 4y) | C4, C5 |
| A cluster derivative additionally needs a gap to the rest of the spectrum | A branch needs a checked unit witness on D(g); its observations read ⊥ off the chart | C8–C11 |
| The typed Hermitian lift, cotangent action and agreement with emitted reverse Core remain open | Steps 1 and 2 of #471, and the agreement for trace powers | C7 |

### Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0: the tracker, ADR 0001 §12, the skeleton of this map, the status of the roadmap | Planned | — |
| S1: the shared skeleton: every spectral form exists and is rejected until it is implemented | Planned | — |
| B-prereq: the Daleckii–Krein steps 1 and 2 and the algebra prerequisites in the bridge | Planned | — |
| Batch 2: spectral declarations, certificates and runtime; the Rust parser | Planned | — |
| Batch 3: primitives, code generation and native code; oracle soundness | Planned | — |
| Batch 4: oracle acceptance, bridge integration, `std::linalg::spectral`, the acceptance program, the book | Planned | — |
| Review: the independent whole-stage review | Planned | — |

### Status terms

- **Proved (oracle)** is a theorem about kernel data and runtime definitions in
  `lean/VastitasOracle/`, mathlib-free, about the checker that accepts the
  input.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
  Testing is not a proof of all inputs.
- **Assumed** is a trusted component of the proof boundary.
- **Not claimed** is outside this profile.
- **Planned** has no evidence yet.

<a id="acceptance-conditions"></a>

## Acceptance conditions

The acceptance program is planned as the example package
spectral-observations. It depends on std and nature and prints `42`. Each observation has its own
failure code, and a mutation test flips every one.

| Condition | Status and evidence |
| --- | --- |
| <a id="c1"></a>C1. Fields and modules: basis names, at most four basis vectors, one object, `symmetric` checked, presented objects rejected, `E_SPECTRAL` cases, `E_LIMIT` | **Planned** |
| <a id="c2"></a>C2. Spectral pair: Faddeev–LeVerrier producer, cofactor checker, the adjugate identity, the Jacobi trace, Cayley–Hamilton, idempotence and Jacobi's formula against kernel-computed quotients; no certificate on the wire | **Planned** |
| <a id="c3"></a>C3. Scalar against Jordan: equal χ and invariants, different module action; Σ_H never reduced | **Planned** |
| <a id="c4"></a>C4. Invariants as smooth maps: equal to a declared reference map; Newton's identity; a zero differential is not ⊥ | **Planned** |
| <a id="c5"></a>C5. Roadmap gradient: (4x, 4y) on the dimensionless Euclidean chart, the origin included | **Planned** |
| <a id="c6"></a>C6. The reverse Core of an invariant is the reverse pass of Stage 3; no reverse rule of its own | **Planned** |
| <a id="c7"></a>C7. Daleckii–Krein: typed Hermitian lift, cotangent action with the pairing Re tr(KX), a noncommuting order regression, and emitted reverse Core of a trace power equal to the Daleckii–Krein cotangent composed with the derivative of the field | **Planned** |
| <a id="c8"></a>C8. Gap certificate: finite charts only, a reduced witness, the checked identity; the localizer 1 for the Stage 5 matrix has no witness; a Jordan block and a perturbed witness are rejected | **Planned** |
| <a id="c9"></a>C9. Branch points and ⊥: on and off the chart, the origin | **Planned** |
| <a id="c10"></a>C10. Branch derivative: −∂ᵢχ/∂ₜχ and tr(P ∂ᵢH); (3/5, 4/5) at ((3, 4), 5) | **Planned** |
| <a id="c11"></a>C11. Eigenprojector: P² = P, tr P = 1, HP = tP, a symmetric P, P₊ + P₋ = I | **Planned** |
| <a id="c12"></a>C12. Degenerate cases: H = 0, rank 1, the origin, four basis vectors at the limit | **Planned** |
| <a id="c13"></a>C13. Weakening: no binding of Stages 3 and 4 changes; spectral bindings are environment-free and metric-free | **Planned** |
| <a id="c14"></a>C14. Wire: protocol 9 only; protocols 7 and 8 give `E_PROTOCOL`; forged invariants and tampered embedded data are rejected | **Planned** |
| <a id="c15"></a>C15. Independent reference: a fixture from the étale and finite spectral reference models agrees with the kernel | **Planned** |
| <a id="c16"></a>C16. Limits: rank, power, terms and work give `E_LIMIT` before any comparison, within seconds | **Planned** |
| <a id="c17"></a>C17. Library: `std::linalg::spectral` is usable from a path package; name audit; boundary rule | **Planned** |
| <a id="c18"></a>C18. Native: the program checks, builds and prints 42; mutations flip every code; the rejected packages print their recorded diagnostics | **Planned** |
| <a id="c19"></a>C19. CI: green, with the operating systems of each job | **Planned** |
| <a id="c20"></a>C20. Independent whole-stage review, with each finding fixed or filed | **Planned** |

## Not claimed

Each gets a follow-up issue when Stage 5 closes, unless an issue already owns
it:

- covers by several charts, image opens and cluster splits by Bézout
  identities, and charts whose localizer is not in the base (#765);
- Σ_H as a presented affine object, and the branch as a smooth function on an
  open (#606);
- derivatives of eigenprojectors and eigenvectors, and higher derivatives;
- similarity and base change of spectral pairs, evidence that the module is
  locally free of rank one, and the band-crossing consumer (#337, #247);
- Hermitian fields over QQ(i), physical units of eigenvalues and
  floating-point realizations;
- numerical eigensolvers and checked extraction adapters (#324);
- steps 3 to 5 of #471;
- performance (#222).

## Validation

The commands and their results are recorded when the stage closes.
