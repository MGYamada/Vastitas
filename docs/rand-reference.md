# Finite random-supply reference

This executable Python reference tests the associativity and reproducibility
foundations of [#249](https://github.com/MGYamada/Vastitas/issues/249). It is not
public `.vast` syntax, a production sampler, compiler acceptance, or a Lean proof.
It does not complete #249. No PRNG, entropy source, Float transform, or
Box–Muller implementation is selected or introduced.

Run from the repository root, using only Python's standard library:

```sh
python3 scripts/demo_rand_reference.py
python3 -m unittest discover -s scripts -p 'test_rand_reference.py' -v
```

The existing CI command `python3 -m unittest discover -s scripts -p 'test_*.py'`
discovers these tests. Implementation: [rand_reference.py](../scripts/rand_reference.py);
regressions: [test_rand_reference.py](../scripts/test_rand_reference.py).

## Responsibility boundaries

| Layer | Owner and scope |
| --- | --- |
| Mathematical Monad | `std::category::Monad` ([#199](https://github.com/MGYamada/Vastitas/issues/199)): endofunctor, unit, multiplication, naturality, and law evidence. |
| Pure probability | `std::distribution` ([#248](https://github.com/MGYamada/Vastitas/issues/248)): measures and kernels; the canonical mathematical Giry instance. `FiniteDist` models only finite rational measures here. |
| Execution interface | `monad::kleisli` ([#206](https://github.com/MGYamada/Vastitas/issues/206)): derive the extension/triple and sequencing interface from the same certified mathematical instance. No second law authority. |
| Sampling realization | `monad::rand` (#249): explicit supply, sequential state threading, separately requested splitting, and logical address ownership. |

`compose_dist` is a finite mathematical sum/product calculation, not a proposed
operational `std` API. Python callbacks and closures are convenient test notation;
they do not relax Vastitas's closure-free/ownership rules. No `State` or `Except`
package, new Domain Checker, or named certified Monad instance is installed by
this reference.

## State transitions and explicit splitting

`Supply` stores immutable bit/address tuples and a cursor. A successful read
returns the bit, the advanced supply, and a `Read(address, bit, consumed=True)`
audit event. Sequential `bind` passes the exact returned supply to its
continuation, without splitting. It concatenates audit events in execution order.
Tests compare the entire result, including output, remaining bits/position, and
trace, rather than only the final distribution.

The intended successful state transition is `S -> (A, S)`. To model finite
exhaustion explicitly, this reference adds an absorbing `Exhausted` result that
retains the current supply, requested capacity, and consumed-prefix trace. This
is a failure-and-trace extension of State, not a total finite-bit sampler for
arbitrarily many draws. Later continuations do not run after exhaustion. Ordinary
Python exceptions are outside the modeled outcomes and propagate as errors.

`split_at(k)` is an explicit operation: the next `k` remaining bits go to the
left child and all others to the right, with their original addresses. The
returned parent has no available bits. No bits are duplicated, omitted, or
renumbered; already-consumed bits are excluded. Insufficient capacity fails
without a partial partition. Empty children are permitted. This fixed contiguous
partition is a finite fixture, not a production key-derivation algorithm.

Supply snapshots remain inspectable and copyable Python values so that the
negative State examples and extensional comparisons can be expressed. Retaining
the old parent or manually rebuilding a child is **not prevented in Python**.
Production opacity, legal moves, disjoint-domain ownership, and compiler checking
remain separate obligations. The reference does not certify arbitrary callbacks
as admissible samplers.

The deliberately incorrect `bad_split_bind` splits by syntax-tree position. Its
two bracketings produce `(LL, LR, R)` and `(L, RL, RR)`. A single six-address
bit table witnesses different outputs, while exhaustive uniform enumeration of
that same table gives the same three-bit output law for both. Equal distributions
therefore do not establish identical fixed-supply execution.

## Exact finite laws and the independence boundary

`FiniteDist` requires normalized, nonnegative `Fraction` weights and hashable
outcomes. Repeated outcomes are aggregated exactly; floats are rejected.
`uniform_bits(n)` enumerates the declared uniform product measure on `{0,1}^n`,
including the singleton empty supply for `n=0`. Enumeration is capped at 12 bits
because it is exponential. This explicitly chosen probability space is not a
claim about a deterministic seed or any real PRNG.

`execution_law(program, source)` computes the exact finite pushforward into
`Returned(value)` or `Failure.SUPPLY_EXHAUSTED`. Successful `None` remains distinct
from shortage. `output_law` projects to values only when all source mass succeeds;
otherwise it rejects. It never discards failure mass or conditions on success.

For the two-consuming-read example, under the explicitly independent two-bit
source, the finite bind equation agrees with mathematical kernel composition:

```text
P((0,0)) = P((0,1)) = P((1,0)) = P((1,1)) = 1/4.
```

By contrast, two `unsafe_peek_bit` calls reuse the same bit without advancing:

```text
P((0,0)) = P((1,1)) = 1/2;  P((0,1)) = P((1,0)) = 0.
```

Each individual peek has the same fair marginal as a consuming read, but
`P(first == second)` is `1` rather than `1/2`. The peek program still satisfies
the ordinary sequential **State** equations in the finite tests. What fails is
the proposed unrestricted independent-law interpretation.

Correct consumption or disjoint split addresses alone also do not prove source
independence: a source supported on `00` and `11` remains correlated after either
operation. The tests retain this second negative case. A mixed success/shortage
fixture gives each outcome mass `1/2` and cannot be exposed as an output-only law.

For an eventual `law_ideal` morphism, the admissible fragment must use fresh,
independent ideal supply, preserve the required residual-source invariant, and
exclude arbitrary introspection/replay. Measurability and any termination/totality
hypotheses also belong to that theorem. Finite variable-consumption examples
must track remaining capacity; the cursor/remaining length itself may reveal
previous results. The relevant freshness concerns unread bit values conditional
on the permitted consumption history, not independence of the entire cursor
state. This reference tests both fixed and bounded value-dependent consumption
with enough bits; it does not decide admissibility or prove the general morphism.

## Logical address ownership and schedules

`LogicalAddress` is the explicit tuple
`(profile, seed, namespace, logical_index, draw_index)`. The fixed profile name
`finite-logical-address-v1` describes only this reference schema, not a PRNG.
Logical/draw indices are in `[0, 2^32)` with overflow rejected, never wrapped.
The seed is a nonnegative integer label; it is not expanded into random bits.

`LinearKey` is a one-use handle at the level of each Python object. Two separately
constructed handles can consume the **same address**, despite each being used
only once. `AddressBook` additionally owns a finite domain and retains the complete
allocation history for one run. It rejects overlapping domain entries, outside
addresses, and duplicate claims both before and after the first handle is spent.

The scheduling regression fixes a table of eight bits for four logical tasks,
each with two draws. Across all 24 task execution orders, it reconstructs addresses
from task/draw identity and checks the complete task-to-address/value mapping.
Allocation order and physical worker identity are absent from the address.
This tests schedule-independent addressing and lookup, not randomness quality.

All claims in a run must use its single domain owner. The example simulates
schedules sequentially; it is not a thread-safe/distributed allocator. A fresh
book explicitly starts a separate run/replay and does not provide cross-run
deduplication. Python attribute access/copying is not a security or static
linearity boundary. Production disjoint tokens, parallel allocation, intentional
replay policy, and ownership refinement remain future work.

## Evidence ledger and future proof work

| Status | What this increment establishes or leaves open |
| --- | --- |
| Executable finite tests | All eight three-bit supplies; both sequential bracketings including residual state/trace; unit and associativity cases with branching, nonzero cursors and shortage; explicit split; exact rational laws and counterexamples; all 24 task schedules; duplicate/overflow rejection. |
| Conditional mathematical correspondence | Intended `law_ideal` return/bind equations on an admissible fragment under explicit fresh-source and other mathematical hypotheses. No Python return value is evidence for that general theorem. |
| Future Lean proofs | Formalize sequential transitions and error/trace extension, prove unit/associativity extensionally, establish the residual-source invariant and conditional law morphism, prove split-domain disjointness/address uniqueness, and connect actual checked implementation and derived Kleisli evidence to the canonical mathematical Monad. |
| Unsupported here | Production PRNG/version/known-answer vectors, entropy, continuous distributions, Box–Muller, Float/GPU equality, compiler integration, static ownership certification, and general ideal-source independence. |

The finite negative examples refute specific unrestricted claims. Passing the
positive tests is regression evidence for these fixtures, not a universal proof,
an independence certificate, or completion of #199/#206/#248/#249.
