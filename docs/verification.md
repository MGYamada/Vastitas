# Stage 0 verification boundary

The proof oracle in `lean/` imports the implementation's definitions from
`lean-kernel/`. It has no executable target and is not consulted when compiling
or executing `.vast` programs. mathlib is pinned to v4.35.0; the executable
kernel and generated runtime depend only on the Lean distribution.

The combined theorem, `VastitasOracle.checkModule_sound`, starts with success
of the actual public checker. It establishes source correspondence, independent
typing, a strict function dependency order, and finite evaluation with the
declared result type for every well-typed argument environment. The constituent
results and their limits are described below.

## Checked language and independent audits

The checked `Term` language retains normalized integer literals, finite
operator and builtin constructors, resolved variable and function symbols,
types, object references, and dependent call substitutions. Object identity
metadata remains available through checking and is erased during code
generation. The formal evaluation relation operates on this actual `Term`
language and uses the actual runtime objects, points, morphisms, and packages.

Successful `checkModule` runs two independent audits after elaboration:

- `Typing.auditModule` checks the structural typing rules for every term,
  including variable lookup, operand types, dependent arguments and their
  final substitutions, branch identities, packages, parameter and return
  scopes, and uniqueness of function IDs and fresh nominal references.
- `Dependency.auditModule` checks that every call refers to an earlier
  function in the finalized order. This establishes acyclicity independently
  of the topological sorter's implementation.

The typing rules are defined separately from the elaborator's control flow;
they are not defined as the statement that elaboration succeeded.
`VastitasOracle.checkModule_typed_and_ordered` unfolds the actual public checker and proves
that acceptance yields its actual elaborated module satisfying both
`Typing.ModuleWellTyped` and `Dependency.ModuleOrdered`.

`CertifiedModule` still carries the smaller annotation postcondition:
compatible endpoint bases and agreement between each body's annotated result
and its declared return type. `certifiedModule_annotation_property` is the
projection of that subtype property. It does not establish the stronger
typing, dependency, or source-correspondence results. The public
`Codegen.generate` boundary repeats the independent audits, so constructing
this weaker certificate directly cannot bypass them.

## Source correspondence and type safety

`VastitasOracle.Elaboration.checkModule_source_correspondence` proves the independent
`ModuleCorresponds` relation between an accepted decoded `RawModule` and the
actual checked module. Parameter and return annotations retain their source
type and index resolution. Expression and block correspondence covers name
resolution, normalized literals, finite operators, calls, local annotations,
lexical scope, and `let`/`pack`/`unpack` lowering. Every source declaration has a
corresponding checked function, every checked function has a source
declaration, and reordering cannot drop or synthesize functions. The selected
entrypoint corresponds to the finalized function named `main`.

`VastitasOracle.Safety.evaluation_total_and_typed` proves finite big-step evaluation and type
preservation for every checked term constructor, assuming typed contracts for
its callees. The verified dependency order discharges those contracts for the
entire module. The public result,
`VastitasOracle.ActivationSafety.checkModule_total_for_arguments`, states that if the actual
`checkModule` accepts, every function in its result evaluates to a value of its
declared return type for every well-typed argument environment. The caller
does not need to supply an additional freshness or injectivity hypothesis.

Nominal references are interpreted in a world local to each function
activation. These interpretations are deliberately **not injective**:
different static identities may denote equal runtime descriptors. For example,
an object-returning helper can give its result a new static identity while
returning the same descriptor it received. Fresh activation and local
allocation preserve existing meanings without equating distinct identities.

For `Point<X, S>`, value typing states that the runtime point's target and
source equal the interpretations of `X` and `S`. Morphisms preserve the same
endpoint correspondence. Packages hide their object's identity while retaining
the association with their point; opening a package introduces a fresh local
reference. The proofs also connect the actual `checkApply`, `checkCompose`,
`checkPack`, scope-checking rules, and dependent substitutions to these runtime
properties. Scope permits canonical bases and references already represented
by enclosing object bindings or the types of enclosing values.

The proofs contain no `sorry`, `admit`, or project-specific unproved axioms.
CI audits the oracle namespace against Lean's standard logical axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

## What is outside these claims

The source-correspondence theorem starts at decoded `RawModule`. It does not
verify Rust lexing, parsing, source-library composition, JSON serialization or
decoding, diagnostic spans, or the accuracy of diagnostic prose. The
correspondence relation records elaboration into checked syntax; it is not a
separate operational-equivalence theorem for source text.

The big-step semantics evaluates both operands of Boolean `&&` and `||`;
generated Lean uses short-circuit evaluation. The proved contract concerns
values and types in the pure, terminating Stage 0 core. It does not assert
identical evaluation order, execution traces, or resource costs. Nor is there
a proof that generated Lean source, Lean's compiler, generated C, the C
toolchain, linker, OS, and hardware preserve the denotation. Native regression
tests establish observed results for tested programs across that boundary.
Mathematical termination is not a bound on compilation or execution time,
memory use, or stack consumption.

The ordinary/smooth affine descriptors remain a restricted geometric core.
These results do not formalize all schemes or C-infinity schemes, prove
general geometric constructions, establish numerical accuracy, or certify
physical adequacy. The auxiliary coordinate interpretation is limited to the
stated zero/identity fragment. Stage 1a dispatch, independent lambdas,
ownership, iteration, and recursion are not implemented or covered by these
theorems.

## Validation

Run from the repository root:

```sh
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
lake -d lean-kernel build vastitas-kernel
lake -d lean-kernel build VastitasKernel.TypeAuditRegression
cargo test --locked --all-targets
lake -d lean build VastitasOracle
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_boundaries.py
```

`TypeAuditRegression` is an explicit build target: its executable checks forge
checked terms directly, bypassing elaboration. They exercise invalid operand
and result annotations, variables, nominal identities, substitutions,
packages, symbol reuse, and dependency cycles. They also verify that the code
generator rejects forged modules carrying only the legacy annotation
certificate. These tests complement the logical soundness theorems.

Rust integration tests exercise parsing and diagnostics, malformed raw IR,
semantic rejection codes, native execution, source libraries, implementation
limits, and preservation of existing output artifacts on failure. The compiler
CI jobs build and test on macOS and Linux from a checkout without `lean/` or
mathlib, including the checked-IR audit regressions. A separate job builds the
proof oracle and audits its axioms. Dependency-boundary checks prevent the
normal compiler path from acquiring a mathlib dependency.
