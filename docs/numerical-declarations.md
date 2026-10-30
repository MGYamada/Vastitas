# Numerical declaration profiles (protocol 8)

**Implemented boundary:** package source can declare and independently check
ideal real/complex coefficient kinds, nominal geometric scalar bases and finite
linear representation profiles. These use the existing indexed declaration
namespace and the complete authority/Fn/dispatch checker. Declaration acceptance
alone does not authorize numerical operations; the separate
[numerical-value path](numerical-values.md) checks local spaces, bases, actual
map loans and typed GEMM in public resource functions.

The [mathematics-first charter](adr/0001-mathematics-first-stdlib.md) distinguishes
an ideal mathematical coefficient domain from its numerical realization. The
existing resource scalars `F64` and `ComplexF64` describe binary64 storage; neither
is an exact `Field` or a `C∞`-ring. `ComplexF64` is still a closed representation,
not a general public `Complex<T>` type constructor. No new scalar dispatch key,
pure floating arithmetic or recursive `Fn` scalar type is introduced here.

## Source contract

```vast
pub indexed marker RealCoefficients;
pub indexed marker ComplexCoefficients;
pub indexed implementation SmoothScalar(RealCoefficients, scalar_base(smooth, real)) capabilities();
pub indexed global SmoothBase(SmoothScalar);
pub indexed implementation RealSmooth(RealCoefficients, linear_descriptor(SmoothBase, real)) capabilities();
pub indexed implementation ComplexSmooth(ComplexCoefficients, linear_descriptor(SmoothBase, complex)) capabilities();
```

The marker is a nominal coefficient declaration. `SmoothBase` is a distinct
global geometric object, resolved through its package/module and visibility.
Passing the marker or the implementation declaration as the base is rejected.
Two globals of the same base implementation remain different base IDs. An alias
resolves to the original ID; identical spelling in another package does not.

`scalar_base(setting, coefficient)` admits `scheme` and `smooth` settings and
`real` and `complex` ideal coefficient kinds. A smooth scalar base must be real.
An ordinary scheme base may use either kind. `linear_descriptor(Base, kind)`
requires that exact global base to refer to a scalar-base implementation:

| Linear profile | Required base and coefficient relationship |
| --- | --- |
| Ordinary scheme, real or complex | Same ideal kind and exact coefficient marker as the base |
| Smooth, real | Real geometric base and the same coefficient marker |
| Smooth, complex | Real geometric base and a distinct complex coefficient marker |

Every numerical use of one nominal marker must agree on its ideal coefficient
kind throughout the complete environment, including unused declarations. Profile
validation is declaration-order independent. The complex smooth profile retains
complex coefficients over a real geometric base; the later object constructor
must retain the distinction between complex dimension `n` and real dimension
`2*n`. No dimensions are constructed by these declarations alone.

Both new representations require `capabilities()`. They cannot claim the old
affine `origin` or `dimension` capabilities. Old `descriptor` and `global`
primitive bindings and point/morphism representation families remain limited to
the affine descriptor backend. Numerical metadata therefore cannot turn an
existing geometry primitive into a numerical realization. Generic token families
retain their existing index mechanism. A declared linear profile does not attest
algebraic laws or convert arbitrary `Scheme`/`CInfScheme` values into linear maps.

## Wire and checker boundary

Rust selects protocol 8 when any package contains a numerical representation,
even without resource functions. Existing `"affine_descriptor"` JSON is unchanged.
New representations are single-key objects:

```json
{"scalar_base": {"setting": "smooth", "coefficient": "real"}}
{"linear_descriptor": {"base": {"path": ["SmoothBase"], "span": {"start": 0, "end": 0, "line": 1, "column": 1}}, "coefficient": "complex"}}
```

Unknown fields, multiple representation keys, machine scalar names in the ideal
coefficient field, and old wire versions are rejected. Lean resolves base paths
through the same namespace resolver and records their provenance. The actual
`Indexed.Source.checkDeclarations` certificate checks all new contracts;
`ResourceSource` still checks every ordinary and resource body. The exact returned
Core independently audits its complete declaration environment again before
generation. No frontend-selected checked IDs or profile certificates are accepted.

The example under `examples/packages/numerical-declarations` checks these
declarations while compiling an ordinary program that returns `42`. It requires
neither OpenBLAS nor the storage native runtime. Declaration acceptance is not
evidence of numerical execution or C-level performance.

## Validation and remaining connection

`tests/numerical_declarations.rs` exercises source check/build/execution, version
downgrades, unused invalid bodies/profiles, wrong coefficient/base relationships,
namespace visibility, old primitive rejection and forged wire metadata.
`IndexedNumericalRegression` additionally checks nominal base preservation,
declaration permutations, cycles and tampered returned-Core rejection.

The actual-checker theorems in `VastitasOracle.IndexedSource` establish the
implementation contract, required linear base profile, real base/distinct
coefficient for smooth complex profiles, coefficient-kind coherence and the old
constructor boundary. `ResourceSource.public_numerical_declaration` connects
that contract to the actual protocol-8 decoded and accepted input. These prove
structural declaration facts, not mathematical field/module laws, native
refinement or floating-point accuracy.

The [numerical-value compiler](numerical-values.md) now constructs
local nominal spaces/bases and loan-backed maps, checks their bilinear GEMM
composition and emits the exact independently rechecked storage schedule.
The public decoder and source grammar expose these operations inside resource
functions, with independently resolved profile paths and exact receipt provenance.

Dependent numerical interfaces, dual/conjugate/metric evidence and finite tensor networks remain
required by [the Stage 1 gate](stage1-completion.md). These declarations do not
close #66, #67, #91 or #92, or introduce a new mathematical `std` family by name.
