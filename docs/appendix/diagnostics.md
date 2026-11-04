# Appendix B: Diagnostics reference

Every rejection starts with a code such as `E_TYPE`. This appendix lists the
codes by the component that reports them. [Chapter 11](../guide/diagnostics-and-cli.md)
explains how to read a diagnostic line.

The codes and messages below were collected from the sources at this revision.
Where the book specifies a code's meaning, the table links to that rule. Other
codes are listed with the checker that reports them; their messages carry the
detail. The book does not yet give each code its own entry.

## Output format

| Origin | Form | Exit status |
| --- | --- | --- |
| Source diagnostic | `FILE:LINE:COLUMN: CODE: message` | 1 |
| Manifest diagnostic | `MANIFEST: E_MANIFEST: message` | 1 |
| Driver error without a source position | `CODE: message` | 1 |
| Interrupted compilation | `E_INTERRUPTED: compilation interrupted` | 128 + signal number |
| Generated program, native runtime check | Standard error contains `E_NATIVE_*: message` | Unsuccessful |

Lines and columns are one-based; columns count Unicode scalars. A diagnostic
reported by the Lean kernel is mapped back to the original file and its local
position.

## Driver and frontend

The Rust driver reports these before or around kernel checking. Source position
codes come from the lexer, parser and lexical resolver.

| Code | Reported when |
| --- | --- |
| `E_USAGE` | The command line is invalid, for example numerical build options without numerical operations |
| `E_INPUT` | An input file or manifest path cannot be read or is not acceptable |
| `E_MANIFEST` | A `Vastitas.toml` is malformed or has unsupported fields |
| `E_LIBRARY` | A flat-mode `--lib` library declares `main`, which only the entry file may do |
| `E_OUTPUT` | The `-o` path is unusable, for example not a regular file or an alias of an input |
| `E_BACKEND` | The kernel cannot be located or started, or reports a build identity other than this compiler's (`incompatible kernel`) |
| `E_BUILD` | The native build cannot be prepared or fails, including a missing `--openblas-prefix` |
| `E_INTERRUPTED` | A signal cancelled the compilation |
| `E_LEX`, `E_PARSE`, `E_UNSUPPORTED` | The source cannot be tokenized or parsed, or uses unimplemented syntax |
| `E_RESOURCE_LITERAL` | A resource payload such as `f64(0.1)` is not an exact binary64 value ([rule](../storage/resource-programs.md#resource-source--explicit-source-contracts)) |
| `E_LEAN_AUDIT`, `E_LEAN_AUDIT_POLICY`, `E_LEAN_AUDIT_CHECKER` | `audit-lean` cannot read, recheck or accept a proof export; its policy is invalid; or the pinned Lean toolchain or its `nanoda_bin` is missing or mismatched ([CLI](../guide/cli.md)) |

The frontend also reports some kernel-family codes early, including `E_LIMIT`,
`E_NAME`, `E_DUPLICATE`, `E_RESERVED`, `E_SHADOW`, `E_CAPTURE`, `E_CYCLE`,
`E_RECURSION`, `E_MAIN`, `E_TYPE` and `E_PROTOCOL`. The kernel checks the same
rules again independently.

## Lean kernel

| Family | Codes | Checker and specification |
| --- | --- | --- |
| Core language | `E_TYPE`, `E_ARITY`, `E_NAME`, `E_DUPLICATE`, `E_RESERVED`, `E_SHADOW`, `E_RECURSION`, `E_MAIN`, `E_LITERAL`, `E_OPERATOR`, `E_SCOPE`, `E_CONTEXT`, `E_DEPENDENCY`, `E_STAGE`, `E_SCALAR_PROFILE` | Scalar, function and Core checking; [core language](../stage0.md) |
| Geometric identity | `E_ESCAPE`, `E_ENDPOINT`, `E_BASE`, `E_INDEX`, `E_RING` | Object, point and package checks; [geometric core](../stage0.md#geometric-core), [indexed source](../indexed-source.md) |
| Functions | `E_CAPTURE`, `E_STATIC_CALL` | [Static target rule](../stage1b.md#static-target-rule) |
| Dispatch | `E_DISPATCH_AMBIGUOUS`, `E_DISPATCH_ARITY`, `E_DISPATCH_CAPABILITY`, `E_DISPATCH_COVERAGE`, `E_DISPATCH_DOMAIN`, `E_DISPATCH_DUPLICATE`, `E_DISPATCH_DUPLICATE_ID`, `E_DISPATCH_HIERARCHY`, `E_DISPATCH_LIMIT`, `E_DISPATCH_SELECTOR`, `E_DISPATCH_UNREALIZABLE`, `E_CAPABILITY` | [Selection and whole-program checking](../stage1a.md#selection-and-whole-program-checking) |
| Abstract types and contracts | `E_HIERARCHY`, `E_CONTRACT_DOMAIN`, `E_CONTRACT_EMPTY`, `E_CONTRACT_RESULT` | [Abstract selectors and contracts](../stage1a.md#abstract-types) |
| Packages and authority | `E_VISIBILITY`, `E_OWNER`, `E_CYCLE`, `E_ASSEMBLY`, `E_BORROW`, `E_IMPACT`, `E_PROVENANCE` | [Packages](../packages.md), [edit borrowing](../packages.md#edit-borrowing) |
| Resource programs | `E_RESOURCE_ACCESS`, `E_RESOURCE_ALIAS`, `E_RESOURCE_ARITY`, `E_RESOURCE_BOUNDS`, `E_RESOURCE_CODEGEN`, `E_RESOURCE_COEFFICIENT`, `E_RESOURCE_DEPENDENCY`, `E_RESOURCE_DIAGONAL`, `E_RESOURCE_ESCAPE`, `E_RESOURCE_FUNCTION`, `E_RESOURCE_GEMM`, `E_RESOURCE_INIT`, `E_RESOURCE_JOIN`, `E_RESOURCE_LAYOUT`, `E_RESOURCE_LIMIT`, `E_RESOURCE_LOAN`, `E_RESOURCE_MOVE`, `E_RESOURCE_NAME`, `E_RESOURCE_OVERFLOW`, `E_RESOURCE_PACK`, `E_RESOURCE_PROVENANCE`, `E_RESOURCE_RECURSION`, `E_RESOURCE_REGION`, `E_RESOURCE_STATE`, `E_RESOURCE_TYPE`, `E_RESOURCE_VALUE` | [Checked storage](../storage/checked-storage.md), [resource diagnostics](../storage/resource-programs.md#resource-diagnostics) |
| Runtime shapes | `E_RUNTIME_BRANCH`, `E_RUNTIME_CALL`, `E_RUNTIME_CODEGEN`, `E_RUNTIME_COEFFICIENT`, `E_RUNTIME_ESCAPE`, `E_RUNTIME_EXTENT`, `E_RUNTIME_GUARD`, `E_RUNTIME_NUMERICAL`, `E_RUNTIME_RETURN`, `E_RUNTIME_SHAPE`, `E_RUNTIME_TYPE` | [Runtime extents](../storage/resource-programs.md#runtime-shapes) |
| Numerical values and tensors | `E_NUMERICAL_METRIC`, `E_NUMERICAL_ORIGIN`, `E_NUMERICAL_PACKAGE`, `E_NUMERICAL_TYPE`, `E_NETWORK`, `E_TENSOR`, `E_TENSOR_CACHE`, `E_TENSOR_TREE` | [Maps and GEMM](../linalg/maps-and-gemm.md), [networks and packing](../linalg/networks-and-packing.md) |
| Presented affine geometry (Stage 2) | `E_AFFINE_BASE`, `E_AFFINE_COORDINATE`, `E_AFFINE_RELATION` | `E_AFFINE_BASE`: a missing, cyclic or non-presented base, base-coordinate images, structure maps, fiber bases without a chosen isomorphism, projections, restrictions and Cartesian squares. `E_AFFINE_COORDINATE`: unknown, duplicate or foreign coordinates, zero denominators and coefficient selectors that are not a single monomial with coefficient one. `E_AFFINE_RELATION`: a map that violates the target's relations, an isomorphism or Cartesian inverse that does not compose to the identity, or a basis or certificate that fails verification. See [presented affine geometry](../affine-geometry.md#diagnostics) and the [algebra checker](../verification.md#exact-affine-algebra-checker-stage-2-571) |
| Smooth affine geometry | `E_SMOOTH` | <a id="e-smooth"></a>A declaration whose form does not match its implementation is an error (`E_SMOOTH`): `spec[…]`, `fiber(…)` or `localize(…)` under a smooth implementation, `Affine(n)[…]` under a presented or descriptor implementation, or `indexed global` under a smooth implementation. An `Affine(n)[…]` object whose dimension differs from its number of coordinates, or whose coordinates repeat, is an error (`E_SMOOTH`). A smooth map that does not name exactly two smooth objects, an `identity` map between different objects, or a smooth map defined other than by `pullback(…)` or `identity` is an error (`E_SMOOTH`). A `smooth_int_point` whose object or point object is not a smooth object, or whose point object is not 0-dimensional, is an error (`E_SMOOTH`). An unknown, missing or foreign coordinate in a smooth map is an error (`E_AFFINE_COORDINATE`). The frontend checks the dimension of `Affine(K, n)[…]` against its coordinates and reports a mismatch as `E_AFFINE_COORDINATE`. A dimension above the generator limit is an error (`E_LIMIT`). See [smooth forms](../protocol.md#protocol-9-smooth-forms) |
| Limits | `E_LIMIT` | [Appendix D](limits.md), including the work and term budgets of every check-time substitution in the affine profile |
| Wire and generation | `E_PROTOCOL`, `E_ARGUMENT`, `E_CODEGEN` | [Wire protocols](../protocol.md) |
| Internal audits | `E_INTERNAL_ASSEMBLY`, `E_INTERNAL_AUTHORITY`, `E_INTERNAL_DISPATCH`, `E_INTERNAL_FUNCTION`, `E_INTERNAL_GRAPH`, `E_INTERNAL_NAMESPACE`, `E_INTERNAL_TYPE` | Independent audits of the checker's own results; [verification](../verification.md) |

`E_PROTOCOL` also covers tampered or forged requests: the kernel rejects
identities, owners and certificates that the wire cannot supply.

## Native runtime

A built program checks physical conditions before it writes. On failure it
reports one of these messages from
[`lean-kernel/native/storage.c`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/native/storage.c):

| Code | Message |
| --- | --- |
| `E_NATIVE_ALLOCATION` | allocation or live-byte budget failed |
| `E_NATIVE_HANDLE` | allocation is absent, closed or already issued |
| `E_NATIVE_SCALAR` | scalar representation mismatch |
| `E_NATIVE_LAYOUT` | invalid layout, bounds, alignment or narrowing |
| `E_NATIVE_OVERFLOW` | native size or accounting overflow |
| `E_NATIVE_BOUNDS` | cell index is outside the view |
| `E_NATIVE_ALIAS` | accessed regions may overlap |
| `E_NATIVE_EXPECT` | stored bit pattern differs |
| `E_NATIVE_ABI` | unsupported numerical backend version, ABI or threading |
| `E_NATIVE_SHAPE` | numerical operand dimensions differ |
| `E_NATIVE_OPERATION` | unsupported numerical operation or layout |
| `E_NATIVE_STATUS` | unknown status |

A failed `expect` reports the cell and both payloads:
`E_NATIVE_EXPECT: stored bit pattern differs at cell (ROW, COLUMN): holds …; expected …`.
The runtime-shape profile also reports `E_RUNTIME_EXTENT` when a runtime extent
is negative or exceeds the signed native size range.

## Development references

Two independent reference models study diagnostics without being part of the
compiler: a [non-punitive diagnostic record](../reference/compiler-tools.md#diagnostic-reference)
and an [expected-rejection doctest contract](../reference/compiler-tools.md#doctest-result-reference).
