# Compiler protocols (versions 2 and 3)

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

Request: `{ "version": 2, "file": "input.vast", "functions": [...],
"generics": [...], "methods": [...] }`. All three declaration arrays are
present, including when empty. Protocol 3 uses the separate namespace request
below; package requests never fall back to protocol 2. Other versions are rejected.

Every function, generic, method, parameter, block, statement and expression has `span`:
`{ "start": 0, "end": 1, "line": 1, "column": 1 }` (UTF-8 byte offsets,
one-based Unicode-scalar columns). Types and indices have their containing
node's span. All arrays are ordered. With explicit `--lib` inputs, declarations
are merged after separately parsing each file. Byte offsets occupy disjoint
source ranges, while line and column remain local to the original file. The
Rust driver retains the range-to-path map and formats backend diagnostics;
`file` identifies the entry input. The backend does not read library files.

Function: `{ "name": "f", "params": [...], "return_type": Type,
"body": Block, "span": Span }`.
Parameter: `{ "name": "x", "ty": Type, "span": Span }`.
Block: `{ "statements": [Statement...], "result": Expr, "span": Span }`.

Generic: `{ "name": "add", "params": [{ "name": "left", "span": Span },
{ "name": "right", "span": Span }], "domain": [[Type, Type], ...],
"span": Span }`. An empty domain is `[]`; a domain containing the zero-argument
key is `[[]]`. Each tuple contains exactly the declared number of concrete
scalar types.

Method: `{ "name": "add", "params": [Parameter...], "return_type": Type,
"requires": ["HasOrder"], "body": Block, "span": Span }`. Parameter `ty`
fields may use the scalar selectors `Any` and `Number` as well as concrete
scalars; the result must be concrete. An absent source `requires` clause is
encoded as `[]`. Requirement names use their containing method's span.

Types use a `kind` tag:

- `named`: `name` is `Nat`, `Int`, `Bool`, `Unit`, `Scheme`, or `CInfScheme`.
- `pair`: `element` is the string `Nat` or `Int`, for example
  `{"kind":"pair","element":"Nat"}`. Lean independently rejects other elements.
  This is a closed homogeneous value family, not general parametric data.
- `point`: `target: Index`, `source: Index`.
- `morphism`: `source: Index`, `target: Index`.
- `pointed`: `setting` is `Scheme` or `CInfScheme`; `base` is `QQ` or `CInfReal`.
- `function`: `params: [Type...]`, `return_type: Type`. The recursive contract
  contains only Nat, Int, Bool, Unit and function types. An empty `params` is
  `Fn<(), R>`; a single Unit element is `Fn<Unit, R>`. `Fn` is a reserved source
  constructor, not a `named` IR type. Type nesting is bounded to 64 levels.

Index: `{ "kind": "name", "name": "X" }` or
`{ "kind": "base", "ring": "QQ" }`.

`Any` and `Number` are allowed only in method parameter selectors. Domain
tuples accept only `Nat`, `Int`, `Bool`, and `Unit`. Method results additionally
accept `Pair<Nat>` and `Pair<Int>`. The selected method's declared result is
preserved in its specialized signature; expected results do not select methods.
Geometric values and nominal object IDs cannot select a method. The backend
constructs the nominal hierarchy and capability facts itself; request metadata
cannot add subtype edges, assert capabilities, or provide a trusted winner.
It checks ambiguity on the complete concrete key space, coverage on the
declared domain, and every applicable monomorphized body, including nonwinners.
See [Stage 1a](stage1a.md) for the exact specialization order and limits.

Expressions use a `kind` tag and always include `span`:

`pair`, `pair_first`, and `pair_second` use ordinary `call` nodes. Both constructor
operands are inferred independently, with no expected-type conversion. Pair
values can occur in ordinary function contracts and data expressions, but not
in dispatch keys/selectors or recursive Fn contracts. These additions use the
existing protocol-2 and protocol-3 envelopes; older kernels reject the new tag.

- `integer`: decimal unsigned `value` string (unary minus is separate).
- `boolean`: boolean `value`.
- `unit`: no payload.
- `variable`: `name`.
- `call`: `callee` string, `args: [Expr...]`.
- `invoke`: `callee: Expr`, `args: [Expr...]`.
- `lambda`: `params: [Parameter...]`, `return_type: Type`, `body: Block`.
- `unary`: `op` (`-`, `!`), `operand: Expr`.
- `binary`: `op` (`+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`),
  `left: Expr`, `right: Expr`.
- `if`: `condition: Expr`, `then_branch: Block`, `else_branch: Block`.
- `block`: `body: Block`.
- `pack`: `scheme: Expr`, `point: Expr`.

An ordinary function name may occur as `variable`; a generic family may not.
A string `call` may refer to a local Fn binding. The `invoke` form supports
arbitrary callee expressions. Lambda IDs and static targets are assigned by
Lean; spans are diagnostic metadata and cannot establish target identity.
There is no public internal-reference constructor. Unknown expression tags
are rejected. All previously valid protocol-2 requests remain supported.

Statements use a `kind` tag and always include `span`:

- `let`: `name`, `annotation: Type | null`, `value: Expr`.
- `unpack`: `value: Expr`, `scheme` binding name, `point` binding name.

Builtins are `Affine(K, n)`, `Base(K)`, `origin(X)`, `id(X)`,
`compose(g, f)`, `apply(f, p)`, `dimension(X)`, and `int(n)` (Nat to Int).
Only the ring argument of `Affine`/`Base` accepts the reserved variable
`QQ` or `CInfReal`. Their use as ordinary values is invalid.

Success: `{ "version": 2, "ok": true, "lean_source": "..." }` (the source
is present for emit and may be absent for check).
Failure: `{ "version": 2, "ok": false, "diagnostics": [
{ "code": "E_TYPE", "message": "...", "span": Span,
  "notes": [{ "message": "...", "span": Span }] }] }`.
Notes carry related source locations, including object introduction sites. They
are diagnostic metadata, not trusted identity evidence. Current backends emit
an empty array when there are no notes; drivers also accept omitted notes.

Frontend and backend use the same codes for name violations: `E_SHADOW` for a
binding conflicting with a function/generic, `E_RESERVED` for a reserved name,
`E_NAME` for an invalid or unresolved name (including an undeclared generic),
and `E_DUPLICATE` for repeated declarations or local bindings. `E_ARITY` and
`E_TYPE` identify argument-count and type violations. `E_LIMIT` reports bounded
implementation resources; core checking and dispatch lowering share the
4096-unit per-function checking-budget diagnostic. Diagnostic wording does
not change the acceptance rule or its proof boundary.
`E_CAPTURE` rejects references to outer lambda bindings; `E_STATIC_CALL`
rejects function values with unresolved or differing runtime targets.
Higher-order specialization has a separate 4096-instance bound.

The checker rejects recursion (including mutual recursion), duplicate function
names, reserved names, unbound references, incompatible annotations, escaping
nominal identities, and a main signature other than `fn main() -> Int`.
Check accepts modules without main; emit requires main.
Source declaration order does not constrain function calls.
The `__vastitas_` prefix is reserved for hygienic specialization names and is
rejected in source binders and references, including forged wire requests.

`decodeSurfaceModule` in `SurfaceProtocol.lean` decodes the extended request and
`checkSurfaceProgram` checks it. Function syntax remains separate from core
syntax. Every lambda and function body is checked, including unused functions;
signature probes for abstract function parameters are confined to a separate
audit pass. Executable specialization memoizes definition/function-argument
IDs, erases function values and produces only direct calls. The unchanged
finite engine still checks all applicable method bodies. See [Stage 1b](stage1b.md).

The backend lowers the accepted program to the existing Stage 0 core input
representation and runs its independent checker. That internal representation
retains its original version tag; it is not an alternative wire protocol.
External clients must use version 2 even for programs containing only ordinary
functions. The wire request is decoded and checked before this internal adapter.

Runtime representation: generated Lean code uses only
`import VastitasKernel.Runtime`. Scalar types map to Lean `Nat`, `Int`, `Bool`,
`Unit`. Geometric values map to runtime `Object`, `Point`, `Morphism`, and
`Pointed`. Their nominal typing is established before erasure by the checker.
User symbols are always renamed to generated identifiers; source text is never
inserted as Lean syntax. Integers are validated decimal literals.


## Protocol 3: package namespaces

The namespace request is `{ "version": 3, "file": "entry manifest",
"root": "/canonical/app/Vastitas.toml", "packages": [Package...] }`.
The response has the same shape as version 2 and echoes version 3.

- Package: `source` (canonical manifest location), `name`, `version` (SemVer),
  `dependencies: [{ "alias": "math", "target": "/canonical/math/Vastitas.toml" }]`,
  `modules: [Module...]`. The three identity fields distinguish owners. A
  manifest location occurs once, regardless of how many dependency aliases use it.
- Module: `path: ["logical", "components"]`, `public: Bool`, `span`,
  `imports`, `functions`, `generics`, `methods`. The root has path `[]`.
  Each non-root path has a declared parent. Its visibility belongs to the
  module declaration in that parent. There is no source-file owner field.
- Import: `path: ["package", "math", "add"]`, `alias`, `public`, `span`.
- Functions and generics retain the v2 fields and add `public: Bool`.
  Methods retain the v2 fields; `name` is an unresolved reference path.
- Expressions retain the v2 shape. Global `variable.name` and `call.callee`
  preserve unresolved `::` paths. Locals and dependent indices remain lexical
  names. There are no frontend-supplied function IDs or edit-authority grants.

Lean validates package/module/declaration uniqueness, acyclic dependencies,
imports and reexports (including unused ones), visibility on every traversed
path, and exact-module generic method authority. Each resolution shares a
4096-member work budget across path components and aliases, as well as a
nesting bound; exhaustion returns `E_LIMIT` at the referring source span.
Completed dependency nodes are memoized, so duplicate aliases do not cause
repeated graph traversal. Unknown namespace metadata
fields, including claimed owners, are rejected. A public reexport preserves
its original target and requires a public declaration; private intermediates
must be accessible from the reexporting module. Private declarations are
visible from their declaring module and descendants only. Parent names are
not implicitly in scope. Dependency aliases are only initial path components.

`Namespace.lower` assigns symbols from package identity + logical module path
+ declaration name; it also renames local bindings hygienically, including
geometric type indices. Only an ordinary root-package root-module `main`
becomes the core entrypoint. It checks every dependency and body, then the
existing surface/dispatch checker independently checks all applicable method
specializations and the final core. Protocol 2 keeps its flat namespace.
The namespace audit re-resolves recorded references and checks exact method
owners before calling the existing surface acceptance path.

`E_VISIBILITY` identifies private access or a nonpublic reexport; `E_OWNER`
identifies unauthorized method extension, including ordinary functions.
`E_CYCLE` identifies package or import cycles. Existing duplicate, name,
shadowing, capture, static-call and checking-limit codes remain in use.

These checks validate the supplied namespace graph, not the authenticity of
filesystem contents. Changing a graph into a different *valid* program is not
an authentication failure: the wire protocol is not a signed artifact format.
Rust is responsible for canonical file loading and retaining all input files
for output collision protection. Manifest mode selects protocol 3 explicitly; see [packages](packages.md) for
source syntax, CLI, file loading and compatibility details.
