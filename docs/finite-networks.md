# Executable finite two-map networks

Protocol 8 supports a deliberately finite profile of [#69](https://github.com/MGYamada/Vastitas/issues/69):
two rank-two map occurrences, one bilinear evaluation edge, one input boundary,
one output boundary and one caller-provided overwrite destination. It is connected
to the independent Lean checker and the existing typed GEMM/storage/native path.
This does not complete #69 or the historical Stage 1 gate in #179.

## Public source

For already constructed maps `left : V → W`, `right : U → V` and
`destination : U → W`, with the same middle basis:

```vast
contract(destination, NativeFast) {
    occurrence a = left;
    occurrence b = right;
    edge(a.input, b.output);
    input(b.input);
    output(a.output);
}
```

`a.input` is the algebraic-dual factor of the source of `left`; `a.output`
is its target factor. Thus the edge means `V∨ ⊗ V → K`, with the dual port
written first. Boundaries retain the uncontracted input of `b` and output of
`a`. The destination must have exactly those source/target objects **and bases**.
In coordinates the requested result is `C[i,k] = Σ_j A[i,j]*B[j,k]`.
Multiplication is bilinear; contraction inserts no conjugation, metric, adjoint,
dual-space identification or basis transport.

Occurrence identifiers are local to this contraction. A repeated immutable map
value may appear under two different occurrence names, for example `a = same`
and `b = same` for an endomorphism squared. Their ports are different even though
they read the same allocation. They do not grant separate mutable-buffer
ownership. Output separation and all loan/access/initialization checks still
come from the existing resource checker. A port must occur exactly once across
the edge and boundaries. Duplicated occurrence names, duplicate port use,
unconnected/unknown ports and reversed boundary roles are rejected.

Explicitly transformed operands use the existing checked
[dual/conjugate/adjoint path](linear-transforms.md), including its exact nominal
origins, basis evidence and active child loans. A graph cannot supply raw native
flags or convert a conjugate space into an algebraic dual. Merely equal dimensions
do not identify spaces, and distinct bases of one space are not silently identified.

The [complete package](../examples/packages/finite_network/Vastitas.toml) computes
the rectangular real and complex products from the public GEMM example and checks
every output coordinate. The complex product has entries `1+2i, 3i; 2, 2`;
an inserted conjugation changes it.

```sh
cargo run --locked -- check --manifest-path examples/packages/finite_network/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/finite_network/Vastitas.toml \
  --openblas-prefix /path/to/openblas-0.3.34 -o /tmp/finite-network
/tmp/finite-network
```

On Linux add `--native-cc cc`, as for the existing numerical adapter. The program
prints `42` after its coordinate checks. Source checking needs no OpenBLAS.
The optional native runtime is linked only for executed GEMM; unused network
bodies remain independently checked on the ordinary no-BLAS path.

## Graph and independent acceptance

Rust serializes an unresolved resource statement with `kind: "network"`, `graph`,
`output`, `policy: "native_fast"` and `span`. The graph has:

| Field | Entries |
| --- | --- |
| `occurrences` | Two `{name, value}` objects; `value` is a local map name |
| `edges` | One `{dual, primal}` edge |
| `inputs` | One explicit input boundary port |
| `outputs` | One explicit output boundary port |

Each port is `{occurrence, role}`, where `role` is `input` or `output`. Types,
allocations, inferred conversions, certificates and schedules are not accepted
from the frontend. The decoder bounds these lists before traversing them and
rejects unknown fields at every level. Older protocols reject network statements;
older protocol-8 kernels fail closed on the unknown tag.

`ResourceSource.lowerStatements` independently resolves map names in the actual
function scope. `Storage.Functions.networkOperation` resolves the current call's
activation and passes the actual numerical environment, values and resource state
to `TensorNetwork.check`. It validates occurrence identity, exact port coverage,
edge variance, nominal edge type and ordered boundaries. It then calls the
existing `Storage.Numerical.checkProduct` for the actual three maps. Storage and
GEMM checking are shared with direct products, including stale views, initialization,
output aliases and exact scalar/layout checks. All-body probes remain separate from executable expansion. Both branch arms
are checked, and each arm's receipts are retained exactly once together with
receipts before and after the branch, including nested branches. A branch receipt
records its local schedule segment; it does not claim that both arms execute.

The sole edge determines the left and right operands. Declaration order does not
select a different schedule. Lowering emits exactly one overwrite GEMM with
default alpha one, beta zero and explicit `NativeFast`. There is no order search,
packing, intermediate allocation or copy inserted by the graph layer.
`NetworkReceipt` retains the exact accepted graph, pre-state, mathematical product,
emitted operation and actual accepted storage transition. The public checker audits
that every executable network receipt uses its same accepted declaration environment.

## Proof and validation boundaries

`VastitasOracle.TensorNetwork` imports the actual implementation and proves:

| Theorem | Guarantee |
| --- | --- |
| `ports_used_once` | Every declared occurrence port has exactly one use |
| `admitted_bilinear_edge` | Both edge ends have the same exact basis with dual/vector roles |
| `edge_product_basis` | The graph edge basis equals the actual GEMM inner basis |
| `output_boundary` | Ordered boundaries and destination bases agree |
| `no_implicit_conjugation` | Lowering preserves only the checked operand conjugation flags |
| `same_input_plan` | The same accepted input produces the same GEMM request |
| `actual_lowering` | Actual graph acceptance, emitted GEMM and storage acceptance agree |
| `public_network_origin` | Public acceptance ties the receipt to the exact declaration environment |

These are graph acceptance, nominal typing and exact lowering facts. They do not
prove floating-point arithmetic, a general tensor-category denotation theorem,
full source operational equivalence or native heap/toolchain refinement. They
reuse the existing product/storage proofs rather than reimplementing those models.

`NetworkRegression` checks actual internal expansion and mutated graphs/values/native
instructions. `tests/numerical_source.rs` checks public source, strict raw-wire
rejection, unused bodies, branches, declaration-order independence, alias rejection
and immutable reuse. Its optional native test executes real/complex rectangular
products, `(2+3i)^2 = -5+12i` through two occurrences of one map, and nested dependent
calls. Both numerical CI jobs run the optional source tests. The direct pair emits
six data allocations and two GEMMs, without copies; the reuse pair emits four data
allocations and two GEMMs. These are structural costs, not C-parity measurements.

## Remaining scope

This profile has exactly two rank-two maps and one contraction, uses a caller-owned
destination, and fixes overwrite with unit alpha. Network accumulation and scalar
coefficients, arbitrary rank or multiple edges, scalar covector/vector evaluation,
explicit Hermitian pairing nodes, trace/copy/diagonal/hyperedge nodes, general metric
realization, rewrites and contraction-order optimization are not implemented here.
The existing crossing-word `Graph` checker and its categorical obligations remain
separate. The broader #69 checklist stays open.

Stage 1 still requires the outstanding numerical/storage interfaces and evidence
listed in [stage1-completion.md](stage1-completion.md), including general dynamic
shape/scalar flow, scratch/dependency handling and equivalent-C runtime,
allocation/copy and peak-live-memory measurements. This increment supplies the
first executable occurrence/port connection, not the integrated completion record.
