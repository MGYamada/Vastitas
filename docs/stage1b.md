# Stage 1b: independent lambdas and static higher-order functions

Stage 1b extends the scalar/geometry core and [Stage 1a dispatch](stage1a.md)
with capture-free function values. It does not complete historical Stage 1.
Abstract types/method contracts, function editing, borrowing, storage ownership
and linear algebra remain later work. Tracking: [#50](https://github.com/MGYamada/Vastitas/issues/50).

## Syntax and values

| Contract | Type |
| --- | --- |
| One Int argument | `Fn<Int, Int>` |
| Two Int arguments | `Fn<(Int, Int), Int>` |
| Zero arguments | `Fn<(), Int>` |
| One Unit argument | `Fn<Unit, Int>` |
| Function argument and result | `Fn<Fn<Int, Int>, Fn<Int, Int>>` |

Parentheses inside the first Fn slot describe a parameter sequence. They do
not introduce general tuple values or tuple types. `Fn` is reserved in Rust
and Lean. The old proposed type spelling `fn(Int) -> Int` is rejected.
Anonymous expressions use `fn(x: Int) -> Int { x + 1 }`; all parameter and
result types are explicit. Supported function contracts recursively contain
Nat, Int, Bool, Unit and Fn. Geometry-dependent function contracts are rejected.
Existing ordinary functions can still accept/return geometric values, and a
scalar-signature lambda can perform checked geometric operations internally.

```vast
fn invoke(callback: Fn<Int, Int>, x: Int) -> Int { callback(x) }
fn keep(callback: Fn<Int, Int>) -> Fn<Int, Int> { callback }
fn main() -> Int {
    let increment = fn(x: Int) -> Int { x + 1 };
    let alias = keep(increment);
    invoke(alias, 41)
}
```

Named ordinary functions are also values. Values can be bound, aliased, passed,
returned and invoked, including chained applications such as `factory()(42)`.
Each lambda has independent parameters and local bindings. Referring to an
outer argument, local function value, or local geometric endpoint is
`E_CAPTURE`; pass needed values explicitly. Top-level functions, generics and
builtins remain callable. Nested lambdas obey the same independent-scope rule.

A generic family is not a Fn value. Use an ordinary function or lambda wrapper
to call it. Generic and ordinary/lambda bodies may call one another. Function
values do not extend dispatch keys or method selectors/results; dispatch
remains over Nat/Int/Bool/Unit with its existing product order.

## Static target rule

After substituting function arguments, every application must resolve to one
backend definition. An `if` returning a function is accepted only when both
branches have the same type and resolve to the same definition. Passing the
same function as both parameters to a selector is therefore permitted.
Two separately written lambdas have distinct identities even when their text
or diagnostic spans match. Different targets produce `E_STATIC_CALL`, even
with a literal `true` condition; there is no constant-folding exception.

No runtime closure or function-pointer selection is introduced. Runtime scalar
computations involved in producing a function value are checked and retained
when function values are erased. Function-returning definitions become Unit
results in the internal core; their static result target is carried separately.

## Checking and specialization

Protocol 2 adds surface types, lambda expressions and expression invocation.
The surface tree is separate from the unchanged core's Raw/Checked syntax.
Requests without function constructs retain the exact legacy checker path.
The public entry point is `checkSurfaceProgram`.

Lean independently checks lambda free names, assigns lambda IDs by syntax
traversal, validates signatures, and constructs every applicable dispatch
specialization. Whole-key ambiguity, explicit-domain coverage, nonwinning
methods, out-of-domain applicable bodies, and the 4096-key bound remain intact.

All definitions, including unused higher-order functions and lambdas, undergo
a signature-probe checking pass. Abstract function parameters can supply typed
probe results only in this pass; arguments and erased computations are still
checked. The resulting audit module is passed through the core checker.
A separate pass with fresh state specializes executable calls by definition ID
and function-argument IDs. Audit probes never enter that pass or native output.
Each pass permits at most 4096 higher-order instances in a compilation unit;
plain first-order functions do not consume that budget. Limits report `E_LIMIT`.
Recursive specialization is rejected, followed by the core dependency audit.

An independent structural predicate checks the recorded static target and
erased function-argument signatures against backend definitions. The actual
returned core then passes the existing whole-module typing and dependency
audits. Only after those checks does code generation retain functions reachable
from the validated `main` entrypoint. Unused bodies cannot escape checking by
being absent from generated code.

The oracle proves capture freedom, static signature consistency, and typing,
dependency order and termination of the exact returned core through the actual
public acceptance path. Full operational correspondence from surface lambda
syntax through specialization, Rust/JSON correctness and native code equivalence
remain outside these proofs. See [verification boundaries](verification.md).

## Homogeneous data pairs

The data extension adds `Pair<Nat>` and `Pair<Int>` to ordinary function
parameters/results, local bindings and equal-type branches. `pair(x, y)` infers
both operands independently and requires identical Nat or Int types;
`pair(1, 2)` is always `Pair<Int>`, even under an expected `Pair<Nat>` annotation.
`pair_first(p)` and `pair_second(p)` return the ordered components with exactly
the element type. A bound producer is evaluated once, with ordinary let sharing.

Heterogeneous, nested, Bool/Unit and geometric pairs are unsupported. Pair is
not a dispatch key/selector or part of a Fn contract; a scalar-signature lambda
may use Pair internally. `Fn<(A, B), C>` remains an argument sequence, not a Pair.
Methods may return Pair; their selected signature determines the call and
projection types in both first-order and function-containing programs. Promotion
itself is a subsequent stdlib increment.
See [the executable example](../examples/pairs.vast) and [protocol](protocol.md).

The actual core carries finite Pair types and primitive operations. Native code
uses Lean `Prod Nat Nat` or `Prod Int Int`. Independent typing and the existing
source-correspondence, evaluation and termination proofs include these cases.
They do not establish general tuple, abstract-type or source-function rewriting
semantics.

## Regression coverage

`tests/functions.rs` checks native calls, aliases, parameters/results, nested
Fn contracts and lambdas, zero/Unit/multiple arguments, dispatch, multiple
explicit libraries, captures, invalid unused bodies, mismatched types/arity,
runtime target choices, recursion, the 4096-instance boundary and forged IR.
`VastitasKernel.FunctionRegression` checks public acceptance and forged static
signature ledgers directly without Rust. Both macOS and Linux CI run these
with no oracle/mathlib checkout; a separate job builds and audits the proofs.

`tests/pairs.rs` checks Pair source/raw-IR typing and native execution in both
input modes. `VastitasKernel.PairRegression` forges checked Pair construction,
projection and call annotations and exercises the code-generation audit boundary.
