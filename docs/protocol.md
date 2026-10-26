# Stage 0 compiler protocol (version 1)

The Rust frontend sends one JSON object on stdin to `vastitas-kernel check`
or `vastitas-kernel emit`. The Lean backend writes one response on stdout;
tool logs belong on stderr. Neither the frontend's annotations nor names are
trusted. The backend allocates nominal identities while checking lexical
bindings; the wire format cannot supply a trusted object identity.

Request: `{ "version": 1, "file": "input.vast", "functions": [...] }`.
Every function, parameter, block, statement and expression has `span`:
`{ "start": 0, "end": 1, "line": 1, "column": 1 }` (UTF-8 byte offsets,
one-based Unicode-scalar columns). Types and indices have their containing
node's span. All arrays are ordered. With explicit `--lib` inputs, functions
are merged after separately parsing each file. Byte offsets occupy disjoint
source ranges, while line and column remain local to the original file. The
Rust driver retains the range-to-path map and formats backend diagnostics;
`file` identifies the entry input. The backend does not read library files.

Function: `{ "name": "f", "params": [...], "return_type": Type,
"body": Block, "span": Span }`.
Parameter: `{ "name": "x", "ty": Type, "span": Span }`.
Block: `{ "statements": [Statement...], "result": Expr, "span": Span }`.

Types use a `kind` tag:

- `named`: `name` is `Nat`, `Int`, `Bool`, `Unit`, `Scheme`, or `CInfScheme`.
- `point`: `target: Index`, `source: Index`.
- `morphism`: `source: Index`, `target: Index`.
- `pointed`: `setting` is `Scheme` or `CInfScheme`; `base` is `QQ` or `CInfReal`.

Index: `{ "kind": "name", "name": "X" }` or
`{ "kind": "base", "ring": "QQ" }`.

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

Success: `{ "version": 1, "ok": true, "lean_source": "..." }` (the source
is present for emit and may be absent for check).
Failure: `{ "version": 1, "ok": false, "diagnostics": [
{ "code": "E_TYPE", "message": "...", "span": Span,
  "notes": [{ "message": "...", "span": Span }] }] }`.
Notes carry related source locations, including object introduction sites. They
are diagnostic metadata, not trusted identity evidence. Current backends emit
an empty array when there are no notes; drivers also accept omitted notes.

The checker rejects recursion (including mutual recursion), duplicate function
names, reserved names, unbound references, incompatible annotations, escaping
nominal identities, and a main signature other than `fn main() -> Int`.
Check accepts modules without main; emit requires main.
Source declaration order does not constrain function calls.

Runtime representation: generated Lean code uses only
`import VastitasKernel.Runtime`. Scalar types map to Lean `Nat`, `Int`, `Bool`,
`Unit`. Geometric values map to runtime `Object`, `Point`, `Morphism`, and
`Pointed`. Their nominal typing is established before erasure by the checker.
User symbols are always renamed to generated identifiers; source text is never
inserted as Lean syntax. Integers are validated decimal literals.
