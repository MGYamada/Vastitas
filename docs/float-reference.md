# Float / SafeFloat executable reference

This is a bounded Python reference for [#318](https://github.com/MGYamada/Vastitas/issues/318),
following its current Slice A and the pure-reference/execution split in
[#322](https://github.com/MGYamada/Vastitas/issues/322). It does not complete either
issue or install public `std::float` / `monad::float` packages. The mathematical
contracts in [#310](https://github.com/MGYamada/Vastitas/issues/310) and
[#313](https://github.com/MGYamada/Vastitas/issues/313) are unchanged.

Run from the repository root with Python's standard library only:

```sh
python3 scripts/demo_float_reference.py
python3 -m unittest discover -s scripts -p 'test_*float_reference.py' -v
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The existing CI unittest discovery includes both new test files; no compiler,
Lean, BLAS or third-party Python dependency is needed for these reference tests.

## Two layers, one primitive definition

| File | Responsibility |
| --- | --- |
| [float_reference.py](../scripts/float_reference.py) | Integer bit carrier, finite rational decoding, explicit rational conversion, add/sub/mul/raw division, and operation-local symbolic flags. Imports no execution layer. |
| [safe_float_reference.py](../scripts/safe_float_reference.py) | Dedicated `Float` / `SafeFloat`, immutable Unit configuration, `pure`, `bind`, canonical lift, checked division, lazy branching, and internal audit events. Reuses the same reference primitives. |
| [test_float_reference.py](../scripts/test_float_reference.py) | Representation and arithmetic checks independent of sequencing laws. |
| [test_safe_float_reference.py](../scripts/test_safe_float_reference.py) | Separate unit/associativity, flag monoid, morphism, equality, failure, and operational-trace tests. |

There is no general Reader/Writer/Except/State or transformer API. `Ok` and `Err`
are ordinary tagged reference Result values, not a new production exception
runtime. Python callbacks/closures express test programs; they do not change
Vastitas's capture/ownership rules. The laws admit deterministic, effect-closed
callbacks only. Python does not establish this admissibility for arbitrary code;
Python exceptions propagate as model/programming errors, not `DivisionByZero`.

## Fixed binary64 profile

The pure profile is `binary64-rne-gradual-tiny-after-first-nan-v1`:

- Binary64 only, `roundTiesToEven`, no excess precision or FMA contraction.
- Gradual underflow, no DAZ input conversion and no FTZ output conversion.
- Underflow is flagged for an inexact result that is tiny **after rounding**.
  An exactly represented subnormal does not raise underflow. A value that rounds
  up to the smallest normal raises inexact, but not underflow in this profile.
- Arithmetic selects the first NaN operand, left before right, preserves its
  sign/payload and quiets it. Any signaling operand adds `INVALID`, even if a
  different NaN is selected. Invalid arithmetic without a NaN operand produces
  `0x7ff8000000000000`. This is a named deterministic choice, not a claim that all
  hardware or all IEEE implementations choose the same NaN.
- `F64(bits)` and monadic `pure` preserve every admitted bit, including signaling
  NaNs, without quieting, rounding, or emitting flags. Arithmetic/conversion are
  explicit operations. Finite decoding returns an exact `Fraction`; NaN and
  infinity have no RR/rational denotation.
- Conversion accepts explicit `Fraction` inputs, not arbitrary RR, Python
  floats, implicit casts or real-number proof objects. The pure conversion also
  permits an explicit negative sign for exact zero; rational zero alone is +0.

Rounding computes an exact rational significand, integer quotient/remainder,
and tie parity. The pure primitives use no host floating arithmetic or floating
environment APIs. `Flags` are five **symbolic bits** derived from those rules:
invalid, divide-by-zero, overflow, underflow, inexact. They are not measurements
of CPU/GPU flags. Arithmetic rules have executable and regression status only;
there is no claim of full IEEE conformance or a proved rounding implementation.

The execution profile appends `/left-to-right-short-circuit-v1`. `Config` is
immutable Unit: there are no dynamic choices within this profile. Directed
rounding, alternate NaN profiles, binary32, complex arithmetic, arrays, mutable
rounding state, flag inspection/clearing, traps, and native execution are outside
this increment. Unsupported primitive names/configurations are rejected.

## Denotation and equality

```text
Float<A>     = Unit -> (A, Flags)
SafeFloat<A> = Unit -> (Result<A, DivisionByZero>, Flags)
```

`run` returns exactly these pairs. Raw `bind` evaluates the first computation,
then its continuation with the same configuration, and unions their flags.
Safe `bind` stops on `Err`, retaining all accumulated flags. `pure` adds no flags.
`lift` wraps the raw value in `Ok`, preserving flags; lifting a raw Result yields
`Ok(Err(...))`, not a short-circuiting error. Raw `Float<Result<...>>` bind and
dedicated `SafeFloat` bind are therefore tested as distinct operations.

`same_observation` compares Result tags/error identities, accumulated flag masks,
and `representation_key` of successful values. The bounded equality carrier is
`F64`, bool, int, None, tuples and nested Results. F64 identity compares integer
bits; it is reflexive on NaNs and distinguishes signs/payloads/signaling bits.
It distinguishes +0 from -0, which raw `1/x` can distinguish. Native Python float
values are rejected by this comparator, rather than falling back to numeric
`==`. Equality of computations is pointwise equality at every admitted config;
there is only one config here. No general equality decision for callbacks exists.

The tests independently check left unit, right unit and associativity for both
monads, and both lift equations. They exhaust all continuations on a two-value
carrier and four masks `{empty, underflow, inexact, underflow|inexact}`: 32,768
raw and 248,832 safe associativity cases, including failure at each step. The
five-flag monoid is separately checked on all 32 masks (all 32³ triples). Lift
bind tests cover all 32² mask pairs with ten special-bit values. Additional law
tests use the actual arithmetic/checked primitives, including NaNs and ±0.
These are finite regressions, not universal Lean proofs. Bind associativity does
not permit reassociation of arithmetic: a separate negative test demonstrates
different binary64 results for the two additions around `2^53`, `1`, and `-2^53`.

## Division, ordering and failure

| Input | Raw reference division | Checked division |
| --- | --- | --- |
| finite nonzero / ±0 | Signed infinity, `DIVIDE_BY_ZERO` | `Err(DivisionByZero)`, no local IEEE flag |
| 0 / ±0 | Default quiet NaN, `INVALID` | Same typed error, no local IEEE flag |
| infinity / ±0 | Signed infinity, no flag | Same typed error, no local IEEE flag |
| NaN denominator | Selected quiet NaN, signaling policy applies | Guard passes; same raw result/flags |

Mathematical totalized division remains `a/0 = 0` in the selected exact Field;
this reference neither implements nor changes that mathematical model. It does
not extend #310's exact-Field guard to bare meadows. No field law is granted to
F64. `checked_div` guards the evaluated, operation-effective represented divisor.
With this fixed no-DAZ profile that is exactly the two signed-zero bit patterns.
A guard failure runs no raw division, including when the numerator is signaling
NaN. Success does not promise a finite result or exact mathematical nonzero.

`divide(left, right)` explicitly runs the left operand, then the right operand,
then the guard. Failure in the left operand skips the right operand and guard;
prior effects from both successful operands survive a later guard failure.
`choose` uses a represented Boolean and branch thunks, so an unselected branch
is neither constructed nor executed. No exact mathematical branch refinement is
inferred. Failed conditions skip both branches. Tests also retain failures in
`0 * checked_div(1, 0)`, self-division at zero, and nested checked division.

Boundary witnesses include:

- Exact `2^-1075 != 0` converts to +0, with underflow/inexact; checked division
  then fails and retains those flags. Exact nonzero evidence cannot remove this
  represented guard.
- Exact `1/10 + 1/5 - 3/10 = 0`, but the separately converted/evaluated denominator
  is `0x3c90000000000000` (`2^-54`); checked division succeeds. That success is
  not evidence for the ideal domain. No enclosure or ideal-domain certificate
  is fabricated.
- A representably nonzero approximation to `10^-200` passes a primal guard but
  its rounded square is zero. Guard evidence does not transfer to an AD divisor.
- `fl(49 * fl(1/49)) != 1` in the profile, although 49 passes the floating guard.
  The exact meadow unit equation is not the floating zero test.

## Internal trace is a separate check

`audit` returns an immutable internal trace from the **same evaluator** used by
`run`. Events contain site, operation and local flags; `pure`/`bind`/`lift` add no
events, and bind concatenates executed events in order. No second interpreter
or mutable side-channel trace drives the semantics. The trace is projected out
of the minimal observation and is not available to admitted continuations.

Two programs that first fail at sites A and B can both return
`(Err(DivisionByZero), emptyFlags)`. The regression explicitly establishes their
equal minimal observations and **different** internal traces. Consecutive checked
zero divisions record only the first executed guard. Associative bind bracketings
retain the same first failure and prior trace. Reordering underflow across a
failure changes retained flags and is detectable even without a trace.

Repeated raw zero division executes twice but sets just one sticky flag bit;
repeated underflow similarly leaves one bit while the trace has two occurrences.
Subtracting old from new flags cannot recover such repetitions. These diagnostic
trace checks are not extra failing-site identity in #310's public error or a
proof that a future optimized backend must preserve an unobserved site. A future
site-observing profile requires its own explicit trace-refinement theorem.

## Evidence and remaining obligations

| Layer | Status of this increment |
| --- | --- |
| Executable reference | Implemented and regression-tested Python primitive and sequencing layers; fixed binary64 real profile only. |
| Lean monad/lift proofs | **Not implemented.** Prove flag-union laws, both unit laws and associativity by failure cases, and both lift equations extensionally at representation equality. Establish equality congruence for admitted continuations and the trace projection separately. |
| Lean arithmetic proofs | **Not implemented.** Prove finite decoding/rounding and each operation's result/flag contract under the selected NaN, underflow and rounding policy; monad laws alone cannot prove these. |
| Production Source/Core connection | **Not implemented.** Preserve operation identities, computational presentation, model/profile/revision provenance, accepted Core, branch schedule and guard evidence. No parser/protocol/checker/stdlib admission change here. |
| Native refinement | **Not implemented or tested.** No CPU/GPU flags, fenv restoration, ABI, compiler optimization, BLAS/CUDA or native/reference conformance claim. |
| Mathematical accuracy/certification | **Not implemented.** Selected ideal RR/CC specifications, error/enclosure proofs and ideal nonzero evidence remain distinct obligations under #244/#313. |

Future native work must compare represented results, retained flags, typed
failures and branch/short-circuit observations against this selected reference,
declare environment isolation/restoration and DAZ/FTZ/FMA policies, and separately
prove refinement. Differential execution is useful evidence, not a substitute
for that proof. The same applies to any promised first-failure-site trace.

No acceptance checkbox in #318/#322, constitutional theorem, public Monad
instance, or mathematical contract is marked complete by this reference.
