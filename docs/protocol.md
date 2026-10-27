# Compiler protocol (version 2)

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

Request: `{ "version": 2, "file": "input.vast", "functions": [...],
"generics": [...], "methods": [...] }`. All three declaration arrays are
present, including when empty. Requests and responses with another protocol
version are rejected.

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
- `point`: `target: Index`, `source: Index`.
- `morphism`: `source: Index`, `target: Index`.
- `pointed`: `setting` is `Scheme` or `CInfScheme`; `base` is `QQ` or `CInfReal`.

Index: `{ "kind": "name", "name": "X" }` or
`{ "kind": "base", "ring": "QQ" }`.

`Any` and `Number` are allowed only in method parameter selectors. Domain
tuples and method results accept only `Nat`, `Int`, `Bool`, and `Unit`.
Geometric values and nominal object IDs cannot select a method. The backend
constructs the nominal hierarchy and capability facts itself; request metadata
cannot add subtype edges, assert capabilities, or provide a trusted winner.
It checks ambiguity on the complete concrete key space, coverage on the
declared domain, and every applicable monomorphized body, including nonwinners.
See [Stage 1a](stage1a.md) for the exact specialization order and limits.

Expressions use a `kind` tag and always include `span`:

- `integer`: decimal unsigned `value` string (unary minus is separate).
- `boolean`: boolean `value`.
- `unit`: no payload.
- `variable`: `name`.
- `call`: `callee` string, `args: [Expr...]`.
- `unary`: `op` (`-`, `!`), `operand: Expr`.
- `binary`: `op` (`+`, `-`, `*`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `&&`, `||`),
  `left: Expr`, `right: Expr`.
- `if`: `condition: Expr`, `then_branch: Block`, `else_branch: Block`.
- `block`: `body: Block`.
- `pack`: `scheme: Expr`, `point: Expr`.

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

The checker rejects recursion (including mutual recursion), duplicate function
names, reserved names, unbound references, incompatible annotations, escaping
nominal identities, and a main signature other than `fn main() -> Int`.
Check accepts modules without main; emit requires main.
Source declaration order does not constrain function calls.
The `__vastitas_` prefix is reserved for hygienic specialization names and is
rejected in source binders and references, including forged wire requests.

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
