# Stage 0 language and implementation

Stage 0 compiles an entry file and explicitly selected source libraries, with a
deliberately finite geometric core.
It implements the original design's object/point/morphism skeleton and a
native compilation path. The original proposal is indexed in [design.md](design.md).

## Surface language

```text
fn make_origin(n: Nat) -> Pointed<Scheme, QQ> {
    let X = Affine(QQ, n);
    pack { scheme: X, point: origin(X) }
}

fn keep(X: Scheme, p: Point<X, Base(QQ)>) -> Point<X, Base(QQ)> {
    apply(id(X), p)
}

fn main() -> Int {
    let package = make_origin(3);
    unpack package as { scheme: X, point: p };
    let q: Point<X, Base(QQ)> = keep(X, p);
    if dimension(X) == 3 { 42 } else { 0 }
}
```

Functions require parameter and return types. Forward calls are permitted;
direct and mutual recursion are rejected. Arguments are explicit, and functions
cannot capture local variables. Function values and anonymous functions are not
part of this milestone.

Blocks contain `let` and `unpack` statements followed by a result expression
without a semicolon. An empty block returns `Unit`. A `let` annotation is
optional. A block, conditional, function call, or `pack` is an expression.
Both branches of `if` must have the same type; `else` is required.
Only named functions and builtins may be called. Bindings cannot shadow an
existing binding or a function name.

Identifiers are ASCII letters, digits, and underscores, with a non-digit first
character. Source files are UTF-8; whitespace and `//` comments can contain
Unicode. Diagnostics use byte offsets and one-based Unicode-scalar columns.
Trailing commas are accepted in argument lists and package fields.

## Scalars

| Type | Operations |
| --- | --- |
| `Nat` | Arbitrary-precision unsigned literals, `+`, `-`, `*`, comparisons |
| `Int` | Arbitrary-precision literals, unary `-`, `+`, `-`, `*`, comparisons |
| `Bool` | `true`, `false`, `!`, `&&`, `||`, equality |
| `Unit` | `()`, empty blocks, equality |

Comparisons are `==`, `!=`, `<`, `<=`, `>`, `>=`. Ordering is integer-only.
Comparisons cannot be chained without parentheses: write `a < b && b < c`,
or explicitly parenthesize a comparison whose Boolean result is compared again.
Precedence, from low to high, is `||`, `&&`, comparisons, `+`/`-`, `*`,
then unary operators. Parentheses override precedence. `Nat` subtraction
saturates at zero. There are no implicit conversions between `Nat` and `Int`.
An integer literal defaults to `Int` unless an expected `Nat` type determines
it, as in an annotation, argument, or the dimension of `Affine`.
Division, remainder, floating-point values, strings, I/O, loops, and mutable
variables are not available. The generated executable's small entrypoint
prints the pure `main` result; that is not a general source-language effect system.

## Geometric core

| Form | Meaning |
| --- | --- |
| `Affine(QQ, n)` | Ordinary affine descriptor over the rational base |
| `Affine(CInfReal, n)` | Smooth affine descriptor over the smooth real base |
| `Base(K)` | Geometric base object, distinct from the coefficient-ring marker |
| `origin(X)` | The admitted zero point with test object `Base(K)` |
| `id(X)` | Identity morphism on `X` |
| `compose(g, f)` | `g` after `f`, requiring the same middle endpoint |
| `apply(f, p)` | Apply a morphism whose source matches the point's target |
| `dimension(X)` | Descriptor's finite `Nat` dimension |

`Scheme` is the ordinary setting and `CInfScheme` the smooth setting. This
milestone supports only `QQ` and `CInfReal`, respectively; no implicit bridge
between them exists. `QQ` and `CInfReal` are reserved static markers, not
first-class ring values. The base object's dimension is zero.

`Point<X, S>` denotes an `S`-valued point; its indices are geometric objects.
`Morphism<X, Y>` carries source and target indices. Named object parameters can
be used in later parameter types and the result type. Calls substitute the
actual object identity, not just its dimension, into dependent types.

Every affine construction has a fresh abstract identity. Aliasing an existing
object preserves its identity. Equal settings, bases, dimensions, or runtime
descriptors never authorize identifying distinct endpoints. Geometry equality
is not exposed as a scalar operation. Plain object-returning function calls
have fresh result identities; no interprocedural alias inference is promised.

`Pointed<Scheme, QQ>` and `Pointed<CInfScheme, CInfReal>` hide an object with its
base-valued point. `pack` checks the point's exact target and geometric base.
Each `unpack` opens the package with a fresh scoped identity, even when the same
package is opened twice. Returning a local point or morphism without its
endpoint is rejected; repackaging an object with its point is supported.
An object itself can be passed or returned as an immutable value.

The runtime stores descriptors; the origin does not allocate a coordinate
array of size `n`. Nominal indices are erased only after checking. The core is
not a general implementation of coordinate rings, all generalized points,
arbitrary algebraic/smooth maps, or scheme isomorphism decision.

## Compiler behavior and limits

`vastitas check file.vast` performs Rust parsing/resolution and independent Lean
checking. It does not need a C compiler or an entrypoint. `vastitas build
file.vast -o output` additionally requires `fn main() -> Int`, emits Lean into a
temporary Lake project, and builds a host executable. User identifiers never
become raw Lean code. The output is installed atomically only after successful
native compilation; a failed compile preserves an existing output file.

The backend and its native runtime artifacts must already be built with
`lake -d lean-kernel build vastitas-kernel`. A missing backend, protocol mismatch,
semantic error, or failed native build is an error; there is no frontend-only
fallback. The frontend bounds recursive parsing at 64 levels and syntax trees
at 128 nodes of depth, including left-associated operator chains. The protocol
decoder allows up to 512 recursive decoding steps. The semantic checker starts
each function with 4096 units of fuel, consumed along recursive checking paths
by expression nesting, statements, and call arguments; this is not solely a
syntax nesting limit or an exact statement count.

Both `check` and `build` also enforce at most 4096 generated Lean `let` bindings
per function, including all branches and nested expressions. A source `let`
contributes one and `unpack` contributes three. Exceeding either checker budget
reports `E_LIMIT`. Generated Lean uses `maxRecDepth 32768` and
`maxHeartbeats 2000000`. These are tested defensive implementation limits, not
mathematical restrictions or a guarantee against environmental build failures.

When `VASTITAS_KERNEL` explicitly selects an executable, `check` needs no
kernel package directory. Native builds still require `VASTITAS_KERNEL_ROOT`
(or this checkout's default package), and copy that package's `lean-toolchain`
into the temporary Lake project.

Unimplemented syntax or operations are rejected. Modules/imports, generics
beyond the listed indexed types, dispatch, ownership of editable functions,
tensor operations, AD, numerical solvers, and physical evidence are later
milestones. There is no REPL, user-facing interpreter, LSP, package manager, or
cross-compilation target in Stage 0.

## Source libraries

The CLI accepts repeatable `--lib LIBRARY.vast` options for both `check` and
`build`. For example:

```sh
vastitas build app.vast --lib stdlib/src/arithmetic/int.vast -o app
```

Each source is parsed independently; declarations are then resolved and checked
as one compilation unit. Functions may call declarations in other included
files in either direction, subject to the existing recursion prohibition. All
functions currently share one namespace; duplicate function definitions and
duplicate input files are errors. A library cannot supply the `main` entrypoint.
Diagnostics identify the original file and its local line/column, including
errors reported by the Lean backend. Library paths are relative to the command's
working directory and must name `.vast` files; directories are not expanded.

`stdlib/src/arithmetic/int.vast` exposes `int_add`, `int_sub`, `int_mul`,
`int_neg`, `int_abs`, `int_min`, and `int_max`. The corresponding natural-number
file exposes `nat_add`, `nat_sub`, `nat_mul`, `nat_min`, and `nat_max`.
The prefixes distinguish types while overloading remains outside Stage 0.
The ordinary operator syntax and its scalar typing rules are unchanged; these
`.vast` functions build on the existing exact arithmetic primitives. Libraries
are never loaded implicitly, and there is no package resolver or import syntax.
