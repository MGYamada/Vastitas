# Declaration-driven indexed source (protocol 7)

Protocol 7 adds package-only indexed declarations and typed existential payloads.
Rust serializes unresolved references; Lean composes declaration validation,
actual edit-authority assembly, finite dispatch, independent Fn specialization
and both Core audits on that same input. See [the foundation](indexed-declarations.md)
for the internal contracts and [protocol](protocol.md) for the wire format.

The [geometry stdlib](../stdlib/src/geometry/README.md) exposes `std::geometry::scheme`
and `std::geometry::smooth` through `stdlib`, declaring the finite ordinary/smooth
affine profile through this path. An explicit checked `geometry_compat` library
export maps legacy syntax to those same declarations. This does not complete
#49/#58–63: legacy semantic correspondence and full migration acceptance remain pending. Protocols 2–6
and explicit `--lib` retain their existing geometry syntax and wire formats.
`Indexed.LegacySource` adapts their decoded source into this same common checker
with a separately validated closed compatibility declaration package. Storage ownership, numerical arrays
and performance evidence remain separate pending work.

## Legacy geometry syntax in packages

The geometry library manifest exports unresolved role paths under `geometry_compat`
(see [wire schema](protocol.md#protocol-7-indexed-declarations-and-rich-package-bodies)).
Lean resolves them in the provider’s root scope, checks the complete declaration
environment and validates each role. This is an explicit syntax facade, including
intentional access to the provider’s own declarations; it grants no edit authority.
The two settings require distinct markers, actual global base objects, compatible
finite affine implementations, exact origin/identity/dimension contracts, shared
Point/Morphism families with exactly the same-base constraint, and the matching
single-point existential cases. Names and equal dimensions grant no compatibility.

Exactly one export enables the original `Scheme`/`CInfScheme`, Point/Morphism/
Pointed annotations, old pack/unpack and unqualified geometry calls in the entire
closure. Explicit indexed syntax and old syntax then use the same canonical IDs.
A legacy `Base(QQ)` or `Base(CInfReal)` index is translated to the exported
base object; a bare coefficient marker is rejected as an object index. Local Fn bindings
and declared names are resolved first; only an unresolved unqualified builtin
spelling falls back, never a private-name rejection. Both forms emit the same
checked primitives. Legacy annotation references still participate in capture
checks, and both syntax forms retain independent unused-body and Core audits.

All exports are audited. With zero or multiple exports, qualified new syntax
continues to work and legacy syntax fails with the exact-one-export diagnostic.
This supports independent copies without collapsing nominal package identities.
Profile resolution has no generated runtime operation. Whole-term evaluation,
legacy semantic correspondence and C performance measurements remain separate
obligations. Protocols 2–6 use the source adapter described in
[indexed declarations](indexed-declarations.md#compatibility-adapter-for-protocols-26).

## Declarations and source example

Declarations start with contextual `indexed`, optionally preceded by `pub`, and
end in `;`. Declaration identity comes from the defining package/module/name;
names such as `Scheme` and `Point` do not grant capabilities by themselves.

```vast
pub indexed marker QQ;
pub indexed implementation Grid(QQ, affine_descriptor) capabilities(origin, dimension);
pub indexed classification Scheme { parents(); domain(Grid); };
pub indexed global Base(Grid);
pub indexed family Point(object(Scheme), object(Scheme)) = point constraints(same_base(0, 1));
pub indexed family Morphism(object(Scheme), object(Scheme)) = morphism constraints(same_base(0, 1));
pub indexed package Pointed {
    case(Scheme, QQ) { Point(witness, global(Base)); }
};
pub indexed primitive affine = descriptor(Grid);
pub indexed primitive origin = origin((Scheme, QQ), Point, Base);
pub indexed primitive dimension = dimension((Scheme, QQ));
```

A family parameter is `domain`, `marker`, `natural` or `object(Classification)`.
Constraints use zero-based parameter positions: `same_object(a,b)`,
`same_base(a,b)` and `over(object,marker)`. Natural indices are arbitrary-precision
unsigned literals; they do not become dispatch keys. Family representations are
the finite contracts `token`, `point` and `morphism`. These declarations are not
an arbitrary native representation escape hatch.

Package cases list the witness classification/marker and ordered field families.
Bound indices are `witness`, an unsigned literal, `global(path)`, `domain(path)`
or `marker(path)`. Every field must have the required nominal association with
the witness; matching dimensions cannot substitute for that association.

Primitive contracts are `descriptor(implementation)`, `global(declaration)`,
`origin((domain,marker),pointFamily,baseObject)`,
`identity((domain,marker),mapFamily)`, `dimension((domain,marker))`,
`compose(mapFamily)` and `apply(mapFamily,pointFamily)`. Declaration audits check
their actual representations, domains, arities, capabilities and family shapes.

Value annotations use `Object<domain,marker>` or `family<arguments...>`.
Use qualified forms such as `geo::Point<X,geo::Base>` for compatibility spellings
that the old parser also recognizes. An argument names a declaration or preceding
object binding, or supplies a natural literal, according to the family's contract.
Package annotations use `package<domain,marker>`.

```vast
fn make(n: Nat) -> geo::Pointed<geo::Scheme, geo::QQ> {
    let X = geo::affine(n);
    pack geo::Pointed<geo::Scheme, geo::QQ> { witness: X, fields: [geo::origin(X)] }
}
fn main() -> Int {
    let packed = make(42);
    unpack packed as { witness: Y, fields: [p] };
    int(geo::dimension(Y))
}
```

`unpack` introduces a fresh scoped witness and binds every field in order. A
result containing that opened witness must be repackaged before leaving scope.
An object freshly constructed with the same descriptor remains distinct.

The complete [example](../examples/packages/indexed/main.vast) additionally uses
an identity morphism and a static lambda:

```sh
cargo run --locked -- check --manifest-path examples/packages/indexed/Vastitas.toml
cargo run --locked -- build --manifest-path examples/packages/indexed/Vastitas.toml -o target/indexed-demo
./target/indexed-demo
# 42
```

## Composition and limits

The ordinary import/visibility/shadowing rules apply. A declaration does not grant
edit authority over another module's methods, memberships or contracts. Protocol 7
uses the full protocol-6 assembly checks, including omitted empty root assemblies,
unapplied contribution body checking, nested loans and permanent transfer.

Indexed values can occur in ordinary data signatures and method bodies. Finite
dispatch still uses only the existing scalar/abstract selectors and capabilities;
all applicable bodies, including nonwinners and out-of-domain keys, are checked.
Fn signatures still contain only scalar/recursive-Fn types. Independent lambdas
cannot capture values or object names appearing in indexed annotations.
Separate signature probes audit unused bodies and cannot enter executable targets.

No indexed array allocation, storage loan, linear-algebra operation, new affine
map construction or general recursive function is introduced here. Source and
type depth bounds, 4096 specialization/key limits, arbitrary-precision integers
and nominal identity checks remain in force.

## Acceptance and proof scope

`Indexed.Wire.CheckedInput` retains the exact decoded JSON and exact result of
`Indexed.AuthoritySource.checkProgram`. `VastitasOracle.IndexedWire` connects it
to both typed Core passes, dependency order, main validity, returned loans and
final winning footprints. Native code generation receives the actual executable
Core certificate and independently rechecks that Core at its boundary.

`IndexedProgramSafety` now proves typed total evaluation, including dependent
calls and unpack bodies, for an actual checked Core module. `IndexedWire` and
`LegacySource` expose that theorem for the exact audit/executable modules returned
from protocols 2–7, and prove finite Int-valued main evaluation. This does not
prove whole-source rewriting correspondence, equality with the retained legacy
evaluator or native code-generation correctness. None of these proofs establishes the [Fast like C](storage-ownership.md)
performance goal.
