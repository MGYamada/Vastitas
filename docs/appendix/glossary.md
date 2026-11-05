# Appendix G: Glossary

This glossary defines the terms that the book uses with a specific meaning.
Each entry links to a chapter that explains the term.

## Abstract method

An `abstract method` declaration has no executable body: its braces hold only a
domain. It extends the callable domain of its generic and fixes the result type
that each concrete winning method must have. See
[Abstract method contracts](../guide/dispatch.md#abstract-method-contracts).

## Abstract type

A nominal selector declared with `abstract type`. A `subtype` declaration places
a concrete scalar type under it. An abstract type has no values and adds no
conversions.
See [Abstract types](../guide/dispatch.md#abstract-types).

## Assembly

The `assembly` block in the root module of the root package. It borrows grants
as edit loans, applies contributions, returns the loans and seals the edited
generics. See
[Edit authority](../guide/modules-and-authority.md#edit-authority).

## Assumption registry

The list of trusted components that claims rest on, in
`docs/spec/assumptions.toml`. A claim with status Assumed cites an entry, and a
Proved or Tested claim may name entries in `assumes`. See
[Assumptions](../spec/assumptions.md).

## Base object

The object `Base(K)` over the coefficient marker `K`. The zero point
`origin(X)` has test object `Base(K)`. A base object is distinct from its
marker and from a [basis](#basis). See
[Objects, points and morphisms](../guide/indexed-geometry.md#objects-points-and-morphisms).

## Basis

A basis of a linear space, introduced by a `basis` declaration in a resource
function. A basis is tied to one space. A map reads storage as coordinates in
named bases. See
[Spaces, bases and maps](../guide/numerical.md#spaces-bases-and-maps).

## Capability

The word has two meanings:

1. In dispatch, a capability is a static fact about argument types that a
   method may require with `requires`. `HasEq` holds for every scalar type, and
   `HasOrder` holds for `Nat` and `Int`.
   See [Selectors and capabilities](../guide/dispatch.md#selectors-and-capabilities).
2. In an `indexed implementation` declaration, a capability is a tag in the
   `capabilities(...)` list, from the closed set `origin` and `dimension`. The
   checker audits each primitive against the declared capabilities. See
   [Declarations and source example](../indexed-source.md#declarations-and-source-example).

## CInfScheme

See [Scheme](#scheme).

## Claim

A record of what establishes one part of a [property](#property), or why
nothing does, with exactly one [claim status](#claim-status) and the evidence
that the status requires. See
[Properties and claims](../specifications.md#properties-and-claims).

## Claim status

One of Proved (oracle), Proved (bridge), Tested, Assumed, Not claimed and
Planned. The specification checks infer no status and upgrade none. See
[Claim statuses](../specifications.md#claim-statuses).

## Classification

An `indexed classification` declaration, such as `Scheme`. It lists its parent
classifications and its domain, the complete finite list of implementations
that it classifies. A child's domain lies inside each parent's domain. See
[Identity and declarations](../indexed-source.md#identity-and-declarations).

## Contribution

A `contribution` declaration that names a generic and holds methods for it. An
assembly applies it with `apply`: a recipient's contribution through an edit
loan, and a contribution of the module that holds the generic's edit authority
without a loan. See
[Edit authority](../guide/modules-and-authority.md#edit-authority) and
[Source declarations](../packages.md#source-declarations).

## Core

The typed intermediate representation of pure functions that the Lean kernel
builds while it checks a program. Code generation for pure functions starts
from the checked Core and checks it again. Storage operations are not part of
Core. See
[Verification boundaries](../verification.md#current-public-checker-routes).

## Cotangent pullback

The pullback of a covector along a [smooth map](#smooth-map) at a point. For a
map `F` with Jacobian `J` at a point `x`, it sends a covector `η` at `F(x)` to
the covector `Jᵀη` at `x`. A covector at any other point gives the
[failure value](#failure-value). See
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Delegation

A `delegation` declaration by the recipient of a `delegable` grant or
delegation. It names a recipient module and a region inside the parent loan's
region. In an assembly, `reborrow` uses it to lend a nested edit loan, and the
parent loan stays suspended until the nested loan returns. See
[Explicit delegation](../packages.md#explicit-delegation).

## Dispatch

The static selection of one method of a generic from the argument types. The
compiler makes and checks every choice at compile time, and no method lookup
happens at run time. Expected results never influence the choice. See
[How a method is chosen](../guide/dispatch.md#how-a-method-is-chosen).

## Dispatch key

A tuple of argument types from `Nat`, `Int`, `Bool` and `Unit`, of the
generic's arity. The checker examines every key for ambiguity, including keys
outside the [domain](#domain). See
[Selection and whole-program checking](../stage1a.md#selection-and-whole-program-checking).

## Domain

The word has two meanings:

1. The domain of a generic is the set of argument-type tuples that callers may
   use. A `domain` clause declares it, and [abstract methods](#abstract-method)
   extend it. See
   [Generics and methods](../guide/dispatch.md#generics-and-methods).
2. The domain of an `indexed classification` is the complete finite list of
   implementations that it classifies. See
   [Declaring an indexed profile](../guide/indexed-geometry.md#declaring-an-indexed-profile).

## Edit authority

The right to add methods to a generic. The module that defines the generic
holds it first, and a [transfer](#transfer) moves it to another module.
Imports, `pub`, qualified names and child modules do not grant it. A
[grant](#grant) lets an assembly borrow it for a region as an edit loan, which
the recipient's contribution uses.
A transfer does not move authority over abstract-type membership or
abstract-method contracts. See
[Edit authority](../guide/modules-and-authority.md#edit-authority) and
[Permanent transfer](../packages.md#permanent-transfer).

## Edit loan

Temporary, exclusive edit authority over a region of a generic. An assembly
takes it from a grant with `borrow` and gives it back with `return`. A loan from
a `delegable` grant or delegation can be lent on as a nested loan through a
[delegation](#delegation). An edit loan grants no access to storage; compare
[storage loan](#storage-loan).
See [Scoped edit borrowing](../packages.md#edit-borrowing).

## Existential package

A value that hides a witness object together with fields whose types depend on
it, such as a point on the hidden object. `pack` creates one. Each `unpack`
opens it with a fresh scoped identity, even when the same package is opened
twice. An `indexed package` declaration declares a package type such as
`Pointed`. An existential package is unrelated to a [package](#package) of
source code. See
[Identity is nominal](../guide/indexed-geometry.md#identity-is-nominal) and
[Single-witness existential contracts](../indexed-source.md#single-witness-existential-contracts).

## Failure value

The value of a [tangent or cotangent fiber](#tangent-or-cotangent-fiber) family
that stands for no vector or covector. A cotangent pullback returns it for a
covector that is not at the image point, and every pullback of the failure
value is the failure value. It is at no point, and it equals no value, itself
included. Its components and its pairings read `(0, 0)`, which no rational
number reads. See [smooth forms](../protocol.md#protocol-9-smooth-forms).

## Family

A type former declared with `indexed family`. Its parameters are objects,
markers, domains or natural numbers. `Point` and `Morphism` are families. See
[Declaring an indexed profile](../guide/indexed-geometry.md#declaring-an-indexed-profile).

## Fiber product

The presented affine object `fiber(X, Y)` of two presented affine objects over
a common base. It is unrelated to a
[tangent or cotangent fiber](#tangent-or-cotangent-fiber). See
[Fiber products and base change](../affine-geometry.md#fiber-products-and-base-change).

## Flat mode

The compiler mode that takes one entry file and any number of `--lib`
libraries, without a manifest. Flat mode has no modules, imports, `pub` or
other package-only declarations. Compare [manifest mode](#manifest-mode). See
[Flat mode with `--lib`](../guide/stdlib.md#flat-mode-with---lib).

## Frontend

The Rust part of the compiler, in `src/`. It provides the command line, parses
source, resolves lexical scopes and sends a wire request to the kernel. The
kernel trusts none of its names or annotations. See
[Compiler architecture](../development/architecture.md).

## Function value

A value of a type `Fn<A, R>`: a named function or a [lambda](#lambda).
Function values are independent: they capture nothing from their
surroundings. Every call of a function value resolves to one static target,
and [specialization](#specialization) erases function values. See
[Independent functions and specialization](../guide/function-values.md).

## Generic

A function with several methods, declared with `generic` together with its
arity and domain. Dispatch selects one method for each call. A generic is not a
function value. See
[Generics and methods](../guide/dispatch.md#generics-and-methods).

## Grant

A `grant` declaration offers a [region](#region) of edit authority over a
generic to one recipient module. It becomes usable once its module has received
that authority. The grant names the recipient by its package's manifest
`[package] name` and its module path. A grant is a permission, not a loan: an
assembly borrows it to obtain an edit loan. See
[Scoped edit borrowing](../packages.md#edit-borrowing).

## Implementation

An `indexed implementation` declaration, such as `Grid`. It records a
coefficient marker, a finite backend representation and its
[capabilities](#capability). See
[Identity and declarations](../indexed-source.md#identity-and-declarations).

## Indexed declaration

A declaration that begins with `indexed`: a marker, implementation,
classification, global, family, package or primitive. Indexed declarations let
any package declare an indexed [profile](#profile), and the standard geometry
library uses them. See
[Declaring an indexed profile](../guide/indexed-geometry.md#declaring-an-indexed-profile).

## Kernel

The Lean program in `lean-kernel/` that checks every program independently of
the frontend. It resolves names, allocates identities, checks every body and
generates code from the checked result. It depends on the Lean
distribution only. See [Compiler architecture](../development/architecture.md).

## Lambda

A function expression such as `fn(x: Int) -> Int { x + 1 }`. A lambda states
every parameter type and its result type, and it captures nothing from its
surroundings. See
[No captures](../guide/function-values.md#no-captures).

## Layout

The view descriptor `layout(offset, rows, columns, leading, transposed)`. It
describes a column-major physical rectangle in an allocation: a byte offset,
the physical numbers of rows and columns, the leading dimension in elements and
a transpose flag. See [Resource functions](../guide/storage.md#resource-functions).

## Manifest

The file `Vastitas.toml` at the root of a package. It names the package and its
dependencies. See [A manifest](../guide/stdlib.md#a-manifest).

## Manifest mode

The compiler mode that takes one manifest with `--manifest-path`. Modules,
imports, resource functions, indexed declarations and edit-authority
declarations appear only in this mode. Compare [flat mode](#flat-mode). See
[The commands](../guide/diagnostics-and-cli.md#the-commands).

## Marker

A coefficient marker, such as `QQ`. A package declares a marker with
`indexed marker`, and the core geometry syntax spells the markers `QQ` and
`CInfReal`. An implementation records its marker. A marker is not an object:
`QQ` and the [base object](#base-object) `Base(QQ)` differ. See
[Declaring an indexed profile](../guide/indexed-geometry.md#declaring-an-indexed-profile).

## Mathematical bridge

The proof package in `lean-bridge/`. It proves with mathlib what the kernel's
definitions mean; the kernel, the oracle and the compiler do not depend on it.
A claim with status Proved (bridge) cites its theorems. See
[Independent mathematical bridge](../verification.md#independent-mathematical-bridge).

## Method

One body of a generic. A method gives each parameter a selector, declares a
result type and may require capabilities. See
[Generics and methods](../guide/dispatch.md#generics-and-methods).

## Metric form

A family with the `metric_form` representation, such as `MetricForm<X>`, over
a [smooth affine object](#smooth-affine-object) `X`. An `indexed metric`
declaration names a metric form and gives a constant symmetric Gram matrix in
the coordinates of `X`. No value has a metric form type. `flat` and `sharp`
name their metric explicitly, and no metric is ever selected by default. A
metric form is distinct from the diagonal Hermitian `Metric` of
[transforms and metrics](../linalg/transforms-and-metrics.md). See
[metric forms](../protocol.md#protocol-9-metric-forms).

## Module

A namespace inside a package. The root source file is the package's root
module. A child module is an inline `mod name { ... }` block or a file that
`mod name;` loads. Each module has a logical module path from the package root.
See [Modules](../guide/modules-and-authority.md#modules).

## Nominal identity

Identity that comes from a declaration or a construction, never from structure.
Every `Affine(...)` construction and every `space` declaration has a fresh
identity. Equal settings, base objects, dimensions or descriptors never
identify two objects. Abstract types and indexed declarations also have nominal
identity. See [Identity is nominal](../guide/indexed-geometry.md#identity-is-nominal).

## Nominal object

An object with [nominal identity](#nominal-identity), such as the result of
`Affine(QQ, 2)`. A point's type names the object that the point lies on. See
[Identity is nominal](../guide/indexed-geometry.md#identity-is-nominal).

## Nondegenerate evidence

An `indexed evidence` declaration `nondegenerate(g)` for a metric `g` with Gram
matrix `G`. The kernel computes an inverse `B` of `G`, and it checks again that
`G B` and `B G` are the identity. A singular Gram matrix has no nondegenerate
evidence. `sharp` requires nondegenerate evidence for its metric. See
[metric forms](../protocol.md#protocol-9-metric-forms).

## Oracle

The Lean proof package in `lean/`. It proves theorems about the kernel's
definitions. Compilation and generated programs never run it. See
[Verification boundaries](../verification.md).

## Owner

The word has three meanings. Qualify it where the context does not decide.

1. The **owner** of a function or other declaration is its defining package,
   logical module path and name. Aliases, reexports, file names and read order
   never change it. See
   [Visibility and ownership](../guide/modules-and-authority.md#visibility-and-ownership).
2. The **current owner** of a generic is the module that holds its edit
   authority. A [transfer](#transfer) changes it. See
   [Permanent transfer](../packages.md#permanent-transfer).
3. A **storage owner** is a binding that owns an allocation. `allocate`
   creates one, `move` and calls hand it on, and `drop` frees it. See
   [The statements](../guide/storage.md#the-statements).

## Package

A directory with a `Vastitas.toml` manifest, a root source file and modules.
Compare [existential package](#existential-package). See
[Packages and manifests](../guide/stdlib.md).

## Primitive

An `indexed primitive` declaration. It binds a name, such as `origin` or
`compose`, to one of a closed set of primitive contracts. The checker audits
each primitive's representation, domain, arity, capabilities and family shapes.
See
[Declarations and source example](../indexed-source.md#declarations-and-source-example).

## Profile

The word has three qualified uses:

1. A **finite profile** is an explicitly bounded part of a broader feature
   that the compiler supports. For example, the
   [two-map network profile](../linalg/networks-and-packing.md#finite-networks)
   admits two rank-two map occurrences joined by one evaluation edge.
2. An **indexed profile** is a set of indexed declarations that defines a
   geometric setting, such as the ordinary affine profile of
   `examples/packages/indexed/geo.vast`. See
   [Declaring an indexed profile](../guide/indexed-geometry.md#declaring-an-indexed-profile).
3. A **coefficient profile** declares what the coefficients of numerical maps
   mean mathematically. See
   [Coefficient profiles](../guide/numerical.md#coefficient-profiles).

## Property

One mathematical fact about a language construct or a standard-library module,
recorded in a [specification](#specification) with an example and one or more
[claims](#claim). See [Specifications](../specifications.md).

## Region

The word has two meanings:

1. The region of a [grant](#grant) or [delegation](#delegation) is a list of
   concrete scalar argument tuples. An edit loan covers that region. See
   [Source declarations](../packages.md#source-declarations).
2. A storage region is a set of byte intervals in one allocation. Storage loans
   and layouts cover regions. See
   [Regions, overlap and alias evidence](../storage-ownership.md#74-regions-overlap-and-alias-evidence).

## Resource function

A function declared with `resource fn`. Its body is a sequence of storage
statements followed by a pure `value { ... }` block. See
[Resource functions](../guide/storage.md#resource-functions).

## Riemannian evidence

An `indexed evidence` declaration `riemannian(g)` for a metric `g` with Gram
matrix `G`. The kernel computes a factorization `G = L D Lᵀ`, where `L` is unit
lower triangular and every entry of the diagonal `D` is positive. It also
computes an inverse of `L`, and it checks every identity again. Only a
positive-definite Gram matrix has Riemannian evidence. It is the wrong kind of
evidence for `sharp`, which requires
[nondegenerate evidence](#nondegenerate-evidence). See
[metric forms](../protocol.md#protocol-9-metric-forms).

## Scheme

`Scheme` classifies ordinary affine descriptor objects, and `CInfScheme`
classifies smooth descriptor objects. A descriptor object records only its
dimension. No implicit bridge connects the two settings. A `CInfScheme` object
is not a [smooth affine object](#smooth-affine-object). See
[Objects, points and morphisms](../guide/indexed-geometry.md#objects-points-and-morphisms).

## Seal

The `seal` step of an assembly. Sealing a generic checks its final method
table: no ambiguity, full domain coverage, and winning methods only inside each
grant's region. See
[Edit authority](../guide/modules-and-authority.md#edit-authority).

## Seed

The covector that a [cotangent pullback](#cotangent-pullback) or a reverse pass
starts from. A seed must lie over the image of the point; any other seed gives
the [failure value](#failure-value). See
[reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives).

## Selector

The type that a method gives a parameter for dispatch: a concrete scalar type,
`Number`, `Any` or an abstract type. See
[Selectors and capabilities](../guide/dispatch.md#selectors-and-capabilities).

## Signature probe

A typed placeholder result that an abstract function parameter supplies during
the signature-probe pass. That pass checks every definition, including unused
higher-order functions and lambdas. A separate pass specializes executable
calls, and signature probes never enter it or the generated code. See
[Checking and specialization](../stage1b.md#checking-and-specialization).

## Smooth affine object

An object declared as `Affine(n)[c₁, …, cₙ]` under an implementation with the
`smooth_affine` representation. It stands for the smooth real affine space
ℝⁿ with the named coordinates. Each declaration is one canonical object. A
smooth affine object is distinct from a descriptor object, such as a
`CInfScheme` object, and from a presented affine object. See
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Smooth map

A value of a family with the `smooth` representation, such as
`Smooth<X, Y>`, between two [smooth affine objects](#smooth-affine-object). It
is a polynomial map with exact rational coefficients. A declared smooth map
gives each target coordinate as a polynomial in the source coordinates.
`compose` builds a program from smooth maps and does not expand it. See
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Space

A linear space declared with `space` in a resource function. Each `space`
declaration makes a fresh nominal space, so two spaces of dimension 2 are
different spaces. See
[Spaces, bases and maps](../guide/numerical.md#spaces-bases-and-maps).

## Specialization

The compilation step that erases function values. Each definition, together
with the function values passed to it, becomes one checked instance. Lambda
instances and instances of higher-order functions count toward a limit that
[Appendix D](limits.md) gives. See
[Specialization](../guide/function-values.md#specialization) and
[Checking and specialization](../stage1b.md#checking-and-specialization).

## Specification

A TOML file under `docs/spec/`, other than the
[assumption registry](#assumption-registry), that records the properties of one
module or construct, apart from its code. Each file generates a chapter of the
book. See [Specifications](../specifications.md).

## Specification environment

The Lean environment in which a [statement pin](#statement-pin) resolves: the
oracle environment, for theorems under `VastitasOracle` and kernel definitions
under `VastitasKernel`, or the bridge environment, for theorems under
`VastitasBridge`. Proved (oracle) and Proved (bridge) name it. It is distinct
from the kernel's checked declaration environment. See
[Claim statuses](../specifications.md#claim-statuses).

## Specification resolver

The check `scripts/spec_resolve.lean`. It imports the modules that a statement
pins file lists and checks each pinned name's module, kind, axioms and
statement hash. See [What the checks verify](../specifications.md#what-the-checks-verify).

## Stage

A numbered milestone of the development roadmap. Stage 1 is the finite
compiler, and Stage 2 is finite affine geometry over QQ. See
[Historical Stages 2–7](../guide/historical-roadmap.md).

## Statement pin

The recorded defining module and kind of a theorem or kernel definition that a
[claim](#claim) cites and, for a theorem, the hash of its statement. A changed
statement fails the [specification resolver](#specification-resolver) until
someone reviews the change and regenerates the pin. See
[Statement pins](../specifications.md#statement-pins).

## Status words

Implemented, Tested, Proved and Planned: the four kinds of statement that the
book keeps apart. The [Introduction](../index.md#what-exists-today) defines
them. A [claim](#claim) has one of the six
[claim statuses](../specifications.md#claim-statuses) instead.

## Storage loan

Temporary access to a [region](#region) of storage that a storage
[owner](#owner) holds.
`borrow` takes a `read`, `write` or `read_write` loan on a layout, and
`release` returns it. Read loans are shared, and a write loan is
exclusive. A storage loan grants no edit authority; compare
[edit loan](#edit-loan). See
[Affine ownership and explicit transitions](../storage-ownership.md#75-affine-ownership-and-explicit-transitions).

## Tangent or cotangent fiber

A value of a family with the `tangent` or `cotangent` representation, such as
`Tangent<X>` or `Cotangent<X>`. It is a vector or covector at a rational point
of the [smooth affine object](#smooth-affine-object) `X`. Its components are
given in the coordinate frame or coframe. It may also be the
[failure value](#failure-value). It is unrelated to a
[fiber product](#fiber-product). See
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Tape

A value of a family with the `tape` representation, such as `Tape<X, Y>`: the
forward values that one evaluation of a [smooth map](#smooth-map) saves at a
point. Only `linearize` builds a tape; a tape has no source or wire form.
`cotangent_backward` runs the reverse pass over a tape. It returns the
[failure value](#failure-value) for a covector that is not at the tape's
output point. See [smooth forms](../protocol.md#protocol-9-smooth-forms).

## Transfer

A `transfer` declaration names an operation that permanently moves edit
authority over a generic to a recipient module. An assembly performs the
transfer, and the generic keeps its identity. See
[Permanent transfer](../packages.md#permanent-transfer).

## View

The binding that a storage loan creates, such as `output` in
`borrow output = write(data, layout(...));`. A view reads or writes the cells
that its [layout](#layout) describes. See
[Resource functions](../guide/storage.md#resource-functions).

## Wire protocol

The versioned JSON request that the frontend sends to the kernel, and the
kernel's response. Each request carries a protocol version. See
[Compiler protocols](../protocol.md).

## Witness

The object that an [existential package](#existential-package) hides. See
[Single-witness existential contracts](../indexed-source.md#single-witness-existential-contracts).
