# Package resource functions (protocol 8)

Protocol 8 connects explicit resource functions to the ordinary `.vast` package
compiler. Names, imports, visibility, canonical module owners, indexed declarations,
finite dispatch and edit assemblies share the same namespace. The existing
`Indexed.AuthoritySource` checks every ordinary, applicable, nonwinning and
unapplied pure body. Resource bodies then pass independent ownership, layout,
initialization and actual-call checks. This is the initial **static resource
profile**, not completion of [Stage 1](stage1-completion.md).

The [complete example](../examples/packages/storage/app/src/main.vast) imports
resource functions from a separate directory-aligned package, receives an owned
buffer, borrows it for inspection, moves it through another function, drops it,
and computes `42` using ordinary finite dispatch and an independent lambda:

```sh
vastitas check --manifest-path examples/packages/storage/app/Vastitas.toml
vastitas build --manifest-path examples/packages/storage/app/Vastitas.toml -o /tmp/storage-example
/tmp/storage-example
```

## Explicit source contracts

Resource declarations use `resource fn`. The operations are statements; the final
`value { ... }` block uses ordinary pure expression syntax. A root resource `main`
has no resource inputs or owned outputs and returns `Int`. A package may instead
have an ordinary pure `main`, or no main when checking a library. Pure and resource
functions cannot declare the same name in one module.

```vast
pub resource fn make()
    returns (data: Owned<F64, 8> initialized [layout(8, 2, 2, 4, false)]) -> Unit {
    allocate data: F64[8];
    borrow output = write(data, layout(8, 2, 2, 4, false));
    fill(output, f64_bits(4613937818241073152));
    release(output);
    value { () }
}
```

`Owned<S, elements>` consumes an owner. An optional `initialized [layout(...), ...]`
contract requires those exact regions; capacity and padding alone imply no
initialization. `returns (name: Owned<...>, ...)` transfers the named body owners
in order. For example, `call buffers::make() -> (data);` receives its owner into a
fresh caller binding. A consumed binding remains unusable and cannot be shadowed.

Borrowed parameters use `Read<S, rows, columns>`, `Write<S, rows, columns>` or
`ReadWrite<S, rows, columns>`, optionally followed by `initializes`. They receive
scoped child loans of the actual caller view. Their scalar and logical shape must
match, but their real offset, padding and transpose are preserved. The caller's
loan resumes only after all children are returned. Two read arguments may alias;
parameter names never prove separation for a writer. Individual cell stores can
establish an entire initialized output, including a padded caller view, through
the bounded write-union check. Both branches must independently cover each
requested cell. No preliminary fill is required when the stores suffice; missing
cells, padding holes and exhausted coverage budgets remain unreadable.

| Statement | Meaning |
| --- | --- |
| `allocate data: F64[8];` | Allocate one initially uninitialized owner; `Complex<F64>` is also supported. |
| `move data -> next;` | Transfer an unborrowed owner; revoke `data`. |
| `borrow view = read(data, layout(...));` | Borrow from an owner or reborrow a loan; also `write` and `read_write`. |
| `release(view);` | Return a childless loan. |
| `drop(data);` | Free an unborrowed owned allocation. |
| `transpose(view);` | Swap the logical axes without copying or conjugating. |
| `fill(view, f64_bits(bits));` | Fill the writable logical rectangle. |
| `store(view, row, column, payload);` | Initialize one checked cell. |
| `expect(view, row, column, payload);` | Assert the exact bits of an initialized readable cell at runtime. |
| `copy(input, output);` | Copy between compatible checked views; reuse the destination. |
| `space v = linear(Profile, 3);` | Construct a fresh nominal linear space from an independently resolved profile. |
| `basis bv = basis(v);` | Introduce a distinct basis tied to that space. |
| `map a = view(input, bv, bw);` | Interpret a live loan as a map from `v` to `w` in those bases. |
| `map a = owned(buffer, layout(...), bv, bw);` | Move initialized coordinate storage into an owned map with exact bases and layout. |
| `borrow coordinates = read(a);` | Borrow an owned map using its actual stored layout; also `write` and `read_write`. |
| `map view = view(coordinates, a);` | Recover the owned map's exact interpretation for a matching live loan. |
| `gemm(a, b, c, overwrite, NativeFast);` | Check exact endpoints/bases and resources, then multiply into `c`; also `accumulate`. |
| `gemm(a, b, c, accumulate, NativeFast, alpha=coefficient(s), beta=f64_bits(bits));` | Read the checked 1x1 scalar loan at execution and apply explicit coefficients; complex maps require complex coefficient bits. |
| `call path(arguments) -> (owners);` | Invoke a resource function, transferring its ordered owned results. |
| `if true { ... } else { ... }` | Check both resource branches and join their states; current conditions are literal booleans. |

Public `gemm` is a numerical statement over typed map views. Lean resolves its
nominal endpoints/bases before composing the actual resource checks and exact
native lowering. Protocol 8 rejects a raw resource `action` containing `gemm`;
the internal action cannot bypass nominal checking. See
[numerical source and wire compatibility](numerical-values.md#source-and-wire-compatibility)
and [adapter responsibilities](numerical-adapter.md#responsibilities-along-the-implemented-path).

`layout(offset, rows, columns, leading, transposed)` uses a byte offset and an
element leading dimension. Bounds, LP64 dimensions, capacity, alignment and
initialization are checked independently in Lean. Native preflight checks physical
handles and arithmetic again. See [the layout contract](storage-ir.md).

`f64_bits` and `complex_bits(real, imaginary)` are explicit unsigned 64-bit IEEE
payload constructors. The example payload is binary64 `3.0`. They do not introduce
floating-point literals or scalar arithmetic into the existing Nat/Int dispatcher.
Allocation sizes and layout arguments are static metadata. An explicit
`coefficient(loan)` operand instead reads an initialized scalar at GEMM execution;
it does not introduce general scalar expression flow between resource statements.

## Pure values and executable boundaries

The terminal `value` block can call ordinary functions, finite generic families
and independent lambdas, and use indexed geometry under its existing declaration
contracts. It cannot read resource handles or perform resource operations. Its
bindings and lambdas cannot capture or shadow surrounding resource bindings.
Resource functions are not `Fn` values, dispatch keys or editable generic families.
Ordinary pure calls cannot invoke them.

The current `call` statement transfers owners and discards the callee's pure
result. There is no scalar result binding or scalar argument flow between resource
statements yet. The entry's pure `Int` result is evaluated after its resource
schedule succeeds. Discarded pure results need no native execution; their complete
bodies still pass the common all-body/type/independence checks. This limited flow
must not be presented as general interleaving of scalar computation and mutation.

Every resource definition is checked, including unused dependencies. Check-only
libraries use actual all-body probes without a fabricated main. Source owners,
local symbols and call IDs are reconstructed; the public input cannot provide
allocation IDs, checked Core, alias assertions or trusted initialization flags.
Versions 2–7 reject resource declarations rather than discarding them.

Generation rechecks the original resource schedule and native instructions, and
rechecks the actual pure Core module, entry target and dependency order. The same
resource main supplies both the schedule and its pure return block. Native IO uses
structured cleanup, including failure paths; a failed resource operation does not
publish the pure return value. Earlier completed writes are not rolled back.

The optional `lean-kernel/native` package is linked only for a resource entry.
A protocol-8 program with only an ordinary pure entry still builds without that
runtime. Neither route needs mathlib. A checked GEMM schedule additionally links
the optional numerical package with explicit pinned OpenBLAS configuration;
other entries remain BLAS-free. See [numerical source and build](numerical-values.md).
Native code performs no runtime
loan interpretation or implicit alias-repair copy; operation costs remain visible
in the checked schedule.

## Evidence and remaining work

`ResourceSource.Checked` retains the original decoder/source mapping, canonical
owners, independently re-resolved calls, actual authority acceptance, complete
resource probes, pure return compilation and exact executable plan. The oracle
imports those definitions: source identity and call provenance, all resource-body
coverage, the original authority trace, typed total evaluation of the returned
pure Core, and closed logical resources at successful entry exit are connected to
actual acceptance. These facts do not prove native heap behavior, full source
operational correspondence, numerical results or compiler refinement.

Regression coverage includes actual source check/build/run, runtime assertion
failure, re-exports/private access, moved owners, uninitialized storage, captures,
nonwinning and unapplied pure bodies, legacy-version rejection and forged wire
metadata. The existing forged native-plan, sanitizer, failure-cleanup and allocation
counter regressions remain required.

Numerical inputs now accept explicit static `Space`, dependent `Basis`, and
`ReadMap`/`WriteMap`/`ReadWriteMap` contracts; see [the input contract](numerical-values.md#dependent-numerical-inputs).
`OwnedMap<source_basis,target_basis>` inputs/results additionally transfer initialized
storage and input-dependent mathematical identities; see [owned results](numerical-values.md#owned-numerical-results).
Bounded generative owned-map packages, explicit rank-three packing/regrouping,
versioned scratch reuse and connected rank-two/three contraction trees are
implemented below. [Diagonal metrics](diagonal-metrics.md) add explicit declared
coefficient realization and scratch-backed pairing. Runtime dimensions/conditions,
scalar value flow throughout resource bodies, general resource packages, dense
metric realization, general owned-result joins and retained-evidence interfaces
remain open. Equivalent-C measurements exist for bounded paths; controlled-host
performance and total allocation acceptance remain unfinished. Escaping borrowed lifetimes and
broader lifetime interfaces retain their separate scope. Protocol 8's static
profile and native compilation alone do not establish **Fast like C**.

[Typed transforms](linear-transforms.md) now add explicit dual/conjugate spaces,
corresponding bases, canonical involutions, declared coordinate metrics and
read-only dual/conjugate/orthonormal-adjoint operations. Dependent parameter
contracts and actual reborrows preserve their evidence and conjugation through
nested calls. The public checker also audits the exact transform receipt origins.

[Vector evaluation](vector-evaluation.md) adds bilinear dual evaluation and explicit
orthonormal Hermitian pairing with scoped vector loans. [Finite two-map networks](finite-networks.md)
check occurrence identity, exact port usage, the bilinear edge and ordered boundaries.
Both features reach the same resource/native path and retain their public origin
audits through both branch arms; their broader metric and network contracts remain open.

[Owned-map packages](owned-map-packages.md) now add the bounded
`OwnedMapTo<source_basis,target_dimension>` profile: one hidden primal target and
direct basis, initialized affine storage, fresh consuming unpack and explicit
repack. The source basis remains an actual caller dependency. Pack/open/transfer
preserve the exact allocation/layout and emit no additional native instructions.
Dynamic dimensions, general resource packages/closures, borrowed results and
full source/native refinement remain pending.

`cache saved = pack3(source, scratch);` and
`contract3_cached(saved, packed, right, output, NativeFast);` expose the bounded
[packing dependency contract](cached-packing.md). Cache names are lexical metadata
with no parameter/result or escaping package form. All-body and both-branch checks
include their capture, consumer and cleanup schedules.

[Bounded contraction trees](contraction-trees.md) add explicit unresolved finite
graphs, ordered ports and caller-supplied regroup/GEMM plans. The full public
checker independently resolves their nominal axes and resource names, retains
actual producer/event receipts from both branches and audits their declaration
environment alongside package and packing-cache receipts.
