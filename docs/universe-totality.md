# Least-fuel meaning for accepted scalar Core

This is the first finite implementation of the totality obligations in
[#350](https://github.com/MGYamada/Vastitas/issues/350). It is independent of the
unmerged universe admission model in
[#368](https://github.com/MGYamada/Vastitas/pull/368). It does not complete the
Universe Charter, general stateful semantics, or CF.

## Profile and connection to the implementation

`lean-kernel/VastitasKernel/ScalarFuel.lean` operates on the existing
`Indexed.Core.Term`, `Module`, `Function` and `Semantics.Value`. It reuses the
existing scalar operations; it does not define a parallel expression language.
The supported syntax consists of literals, variables, unary/binary operations,
homogeneous pairs and projections, Nat-to-Int conversion, ascriptions, scopes,
branches and `letE`. Values are arbitrary-precision Nat/Int, Bool, Unit and the
existing homogeneous pairs. “Finite profile” limits constructors, not integer
values or input cardinality.

`supported` inspects both branches and every nested term. Calls, primitives,
packages and unpacking are outside the profile, even in an unselected branch.
The existing public evaluator, checker and native generator are unchanged.
This observer is internal proof/test infrastructure, not a public interpreter.

`AcceptedHom a b` retains the actual module input, the exact successful
`Typing.checkModule input false` equation and returned `CheckedModule`, the
selected function ID and lookup equation, its input/output signature, and the
profile evidence. `stage` runs that existing independent audit before applying
the profile restriction. The initial interface admits one parameter at Core
symbol zero; pairs allow the existing two-component scalar input. An accepted
certificate cannot be obtained from `supported` or a mathematical function
alone. `accepted_actual_core` proves the returned module is the input module.
These are Core-level facts; this adapter does not claim source elaboration,
target representation, or code-generation refinement.

## Outcomes and fuel

`EvalOutcome A` distinguishes `outOfFuel`, `success A`, and `failure Failure`.
Failures record a missing variable, an invalid operand, or an unsupported
observer form. They are operational failures of this observer. They do not
implement `monad::safediv`, and a pure error returned as a language value would
instead be a success. Unsupported-form rejection is not a claimed semantics
for calls, packages or other excluded operations.

`evalFuel` keeps the existing evaluator's depth-fuel convention and evaluation
order. Children receive the remaining depth independently. Consequently fuel
is neither elapsed time nor an instruction count, and sequential bounds use
`max`, not addition. `evalAccepted` decodes into the actual codomain `El b`.

The following are Lean theorems, not sampled test observations:

| Theorem | Established statement |
| --- | --- |
| `evalFuel_terminal` | For fixed term and environment, any terminal result at `n` is exactly preserved at **every** `n' ≥ n`, including failures. |
| `evalFuel_erases` | For every fuel and supported term, erasing the refined outcome to `Option` equals the existing `Semantics.eval` on that exact term. |
| `evalAccepted_success_iff` | At each fuel, typed success is equivalent to the existing checked-body evaluation returning the encoded value. |
| `accepted_total` | Every accepted arrow in this profile has a successful fuel for every typed input, derived from `IndexedProgramSafety.checked_functions_total_and_typed`. |
| `letE_budget` | A successful first computation at `n` followed by a terminal body at `m` gives that body outcome at every fuel at least `max n m + 1`. The second bound may depend on the intermediate value. |

The raw terminal theorem needs no typing assumption, so it covers failures of
malformed scalar terms as well. Accepted typed arrows have no operational
failure: totality and terminal stability exclude it. There is no mutable heap,
resource state or effect trace in this profile; `Values` is a fixed immutable
environment, extended locally by `letE`.

## Least fuel and derived meaning

`VastitasOracle.LeastFuel` implements a Nat.find-style search using only Lean
core accessibility recursion and an executable `DecidablePred`. An existential
success witness proves accessibility starting at zero; the search advances by
one while the predicate is false. `least_spec` proves success and
`least_minimal` proves minimality. No custom axiom, `sorry`, `native_decide`,
Mathlib import or choice-based witness extraction is used.

The search is a **specification-level `noncomputable def`** using `Acc.rec`;
it is not advertised as a compiled runtime implementation or a promise of
kernel normalization on arbitrary proof terms. Each fuel observation and its
`IsSuccess` predicate are executable independently of that definition.

`TotalHom a b` is the subtype of `AcceptedHom a b` carrying
`∀ x, ∃ n, IsSuccess (evalAccepted f n x)` in `Prop`. `certify` supplies the
proved certificate for this profile. `denoteTotal f x` extracts the value at
the **least successful fuel**; no independent function is stored or assumed.

`leastFuel_success`, `leastFuel_minimal`, `denoteTotal_agrees` and
`denoteTotal_actual_core` establish existence, minimality, universal
sufficient-fuel agreement, and agreement with the actual checked Core.
`successful_value_unique` covers any observed success, while
`before_least_outOfFuel` shows every smaller observation is exhausted.
Changing only the totality certificate gives definitionally identical meaning;
the required proof-irrelevance regression is literally `rfl`.

## Validation

`VastitasOracle.ScalarFuelRegression` is imported by the normal oracle root,
so the existing oracle build and transitive axiom CI audit cover the new
definitions and proofs. The search and its two specifications depend only on
the permitted `propext` and `Quot.sound`; the axiom audit additionally rejects
`Classical.choice` in those three declarations. The connected Core evaluator
and totality bridge retain the existing transitive `propext`, `Classical.choice`,
`Quot.sound` assumptions, as does the original `Semantics.eval`. There are no
new logical axioms. Kernel-checked examples include a selected branch with
least fuel 2 for `true` and 3 for `false`, its derived mathematical value,
terminal failures, exhaustion, `letE`/pair evaluation, saturating subtraction,
mixed-type rejection and certificate proof irrelevance. A concrete admission
equation uses logical typing/order evidence checked by Lean; it does not rely
on native evaluation of the checker's internal hashing. Separate executable
regressions exercise stage acceptance, wrong signatures, an absent function
and an invalid unused branch; these tests do not provide proof authority.

Relevant checks:

```sh
lake -d lean-kernel build
lake -d lean build
bash scripts/check_kernel_regressions.sh
python3 scripts/check_boundaries.py
cd lean
lake env lean ../scripts/audit_axioms.lean
lake env lean ../scripts/check_oracle_core.lean
```

## Remaining obligations

- Extend outcome refinement and exact evaluator correspondence to calls,
  general recursion/divergence, primitives and packages. This work does not
  replace the general evaluator's `Option Value` result.
- Give stateful/ownership-sensitive evaluation separate initial/final heap,
  resource and trace indices; prove preservation of every terminal failure
  **including its state and observable trace**, at all larger fuel.
- Prove accepted composition construction/closure, identity and associativity,
  representation/ownership compatibility and the denotation composition law.
  `letE_budget` is an operational sequencing lemma, not those category laws.
- Extend the pure `TotalHom` bridge to the Charter's target/context/representation
  boundary and additional runtime codes. This local `PureType`/`El` instance
  does not supersede #368's universe admission model.
- Connect the exact source/selected-method/environment/revision identities,
  staging and proof erasure through the compiler and cache, then establish
  native refinement under explicit backend assumptions.
- Connect admitted mathematical constructions to CF and any future partial or
  operational CF formulation. Total evaluation and least-fuel meaning alone
  establish no algebraic law, mathematical algorithm specification, or CF claim.
