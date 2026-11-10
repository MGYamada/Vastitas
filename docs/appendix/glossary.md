# Appendix G: Glossary

This glossary defines the terms that the book uses with a specific meaning.
Each entry links to a chapter that explains the term.

## Abstract method

An `abstract method` declaration has no executable body: its braces hold only a
domain. It extends the callable domain of its generic and fixes the result type
that each concrete winning method must have. See
[Abstract methods](../stage1a.md#abstract-methods) and the
[guide](../guide/abstract-types.md#abstract-methods).

## Abstract type

A nominal selector declared with `abstract type`. A `subtype` declaration places
a concrete scalar type under it. An abstract type has no values and adds no
conversions.
See [Abstract types](../stage1a.md#abstract-types) and the
[guide](../guide/abstract-types.md).

## Accept

The compiler accepts a program when `vastitas check` reports no
[diagnostic](#diagnostic) for it. Acceptance says that the program
breaks no rule that the checker enforces; it is not
[native refinement](#native-refinement). See
[What acceptance means](../language/guarantees.md#what-acceptance-means).

## Allocation

A buffer of [cells](#cell) that one storage [owner](#owner) owns. `allocate`
creates it, and `drop` frees it. See
[Storage types](../storage/resource-programs.md#storage-types).

## Applicable method

A method that **applies** at a [key](#dispatch-key): each type of the key
belongs to the matching selector of the method and has the capabilities that
the method requires. See [Selection](../stage1a.md#selection).

## Arm

One of the two lists of statements of a branch in a resource function. See
[Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls).

## Assembly

The `assembly` block in the root module of the root package. Its
[events](#event) borrow grants as edit loans, apply contributions, return the
loans and seal the edited generics. See
[Assemblies](../language/edit-authority.md#assemblies) and the
[guide](../guide/edit-authority.md#the-assembly).

## Assumption registry

The list of trusted components that claims rest on, in
`docs/spec/assumptions.toml`. A claim with status Assumed cites an entry, and a
Proved or Tested claim may name entries in `assumes`. See
[Assumptions](../spec/assumptions.md).

## Backward Core

The generated function of a [reverse site](#reverse-site) in
[compiled reverse Core](#compiled-reverse-core). It takes the map values of
the site's [opaque steps](#opaque-step), the points and the
[seed](#seed), and it pulls the seed back along the maps of the site, last map
first. It pulls a declared map back by its [Jacobian table](#jacobian-table)
and an opaque step by the [runtime reverse pass](#runtime-reverse-pass).
Compare [forward Core](#forward-core). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Bare name

A name without `::`. It resolves among the bindings in scope, the declarations
and imports of the current module, and the built-in functions. See
[Resolution](../language/names-and-paths.md#resolution).

## Base chain

The [presented affine object](#presented-affine-object) itself, its **base**,
the base of that base, and so on. The base of an object is the object that
its declaration names after `over`. A morphism over a base names an object
on the base chains of its source and of its target. See
[Presented affine objects](../affine-geometry.md#presented-affine-objects)
and the [guide](../guide/affine-geometry.md#objects-over-a-base).

## Base isomorphism

The two maps `via(…) inverse(…)` in the declaration of a
[fiber product](#fiber-product) whose factors lie over two separately
declared bases. The compiler checks that the maps are inverse to each other.
See [Fiber products](../affine-geometry.md#fiber-products).

## Base object

The object `Base(K)` over the coefficient marker `K`. The zero point
`origin(X)` has test object `Base(K)`. A base object is distinct from its
marker and from a [basis](#basis). See
[Settings and markers](../language/geometric-types.md#settings-and-markers)
and the [guide](../guide/indexed-geometry.md#objects-points-and-morphisms).

## Basis

A basis of a linear space, introduced by a `basis` declaration in a resource
function. A basis is tied to one space. A map reads storage as coordinates in
named bases. See
[Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) and the
[guide](../guide/numerical.md#spaces-bases-and-maps).

## Binding

A name that a `let` or `unpack` statement or a parameter list introduces. In a
[resource function](#resource-function), owners, loans and the results of
calls are bindings too. A binding is immutable, and no binding reuses a name
that is visible where it is introduced. See
[Scopes of bindings](../language/statements.md#scopes-of-bindings) and
[Resource statements](../storage/resource-programs.md#resource-statements).

## Bound index

An argument of a field of an `indexed package` declaration: `witness`,
`global(G)`, `domain(C)`, `marker(K)` or an integer literal. `witness` stands
for the object that the existential package hides. See
[Existential packages](../indexed-source.md#existential-packages).

## Boundary

The ports of a [network](#network) or of a contraction tree that no edge
contracts. They are the axes of the result. See
[Two-map networks](../linalg/networks-and-packing.md#two-map-networks) and
[Contraction trees](../linalg/networks-and-packing.md#contraction-trees).

## Built-in function

A function that the language defines: `int`, `pair`, `pair_first`,
`pair_second` and the geometric operations such as `origin`. Its name is
reserved, and it is not a function value. See
[Built-in functions](../language/expressions.md#built-in-functions).

## Cache

A record, at compile time, that the cells of one [tensor](#tensor) hold the
packing of the cells of another. `cache` declares one. It is valid until a
statement writes either allocation, until one of them is dropped, and until
the end of a branch. See [Caches](../linalg/networks-and-packing.md#caches).

## Callable domain

The keys at which callers may call a generic: the keys of its domain together
with the keys of its abstract methods. Every key of the callable domain needs a
winner. See [Abstract methods](../stage1a.md#abstract-methods).

## Capability

The word has two meanings:

1. In dispatch, a capability is a static fact about argument types that a
   method may require with `requires`. `HasEq` holds for every scalar type, and
   `HasOrder` holds for `Nat` and `Int`.
   See [Method declarations](../stage1a.md#method-declarations) and the
   [guide](../guide/dispatch.md#selectors-and-capabilities).
2. In an `indexed implementation` declaration, a capability is a tag in the
   `capabilities(...)` list, from the closed set `origin` and `dimension`. The
   checker audits each primitive against the declared capabilities. See
   [Implementations](../indexed-source.md#implementations).

## Cartesian square

An `indexed cartesian` declaration: the checked statement that the common
source of two declared morphisms is a given [fiber product](#fiber-product).
It names the inverse of the morphism into the fiber product. See
[Cartesian squares](../affine-geometry.md#cartesian-squares) and the
[guide](../guide/affine-geometry.md#the-fiber-over-a-point).

## Case

One alternative of an `indexed package` declaration, `case(D, K) { … }`. It
declares the type `P<D, K>` of the [existential packages](#existential-package)
whose [witness type](#witness-type) is `Object<D, K>`, and it lists their
[fields](#field). See
[Existential packages](../indexed-source.md#existential-packages).

## Cell

One element of an [allocation](#allocation): a binary64 number for `F64`, or
two for `Complex<F64>`. See
[Storage types](../storage/resource-programs.md#storage-types).

## Checker

The part of the compiler that decides whether a program breaks a rule of the
Reference: the [kernel](#kernel). The [frontend](#frontend) reports the errors
of source text, files and manifests, and some errors of names, which the
kernel checks again. See
[What acceptance means](../language/guarantees.md#what-acceptance-means).

## Child

The word has two meanings:

1. A child module is a module that a `mod` declaration of its parent module
   declares. See [Module declarations](../language/modules.md#module-declarations).
2. A child loan is a [storage loan](#storage-loan) borrowed from another loan,
   its parent. See
   [Resource statements](../storage/resource-programs.md#resource-statements).

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
[Classifications](../indexed-source.md#classifications).

## Code

The name of the kind of error that a [diagnostic](#diagnostic) reports, such
as `E_TYPE`. The Reference specifies the code of each error that a rule
states, and not the text of its message. See [Codes](../language/diagnostics.md#codes) and
[Appendix B](diagnostics.md).

## Compiled reverse Core

The [Core](#core) that the kernel generates for the
[reverse sites](#reverse-site) of a checked module: the
[forward Core](#forward-core) at each site and one
[backward Core](#backward-core) function per site. The kernel checks the
generated module again with the Core audit, and it validates the module by
compiling the source module again. Code generation receives the compiled
module. See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Component

In the plan of a contraction tree, a set of occurrences that the plan has
contracted, with the [tensor](#tensor) that holds their product. See
[Contraction trees](../linalg/networks-and-packing.md#contraction-trees).

## Contribution

A `contribution` declaration that names a generic and holds methods for it. An
assembly applies it with `apply`: a recipient's contribution through an edit
loan, and a contribution of the module that holds the generic's edit authority
without a loan. See
[Edit authority across packages](../guide/edit-authority.md#the-contribution) and
[Contributions](../language/edit-authority.md#contributions).

## Coordinate ring

The ring of a [presented affine object](#presented-affine-object): the
polynomials in its **coordinates** with rational coefficients, modulo its
**relations**. See
[Presented affine objects](../affine-geometry.md#presented-affine-objects).

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
[Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Current module

The module in which a path occurs. The first segment of the path resolves in
it. See [Resolution](../language/names-and-paths.md#resolution).

## Delegation

A `delegation` declaration by the recipient of a `delegable` grant or
delegation. It names a recipient module and a region inside the parent loan's
region. In an assembly, `reborrow` uses it to lend a nested edit loan, and the
parent loan stays suspended until the nested loan returns. See
[Grants and delegations](../language/edit-authority.md#grants-and-delegations).

## Dependency alias

The name under which a manifest declares a dependency. As the first segment
of a path it names the root module of that package. See
[Manifests](../packages.md#manifests).

## Derivative rule

The field `reverse` of a [registry entry](#registry-entry). It says what a
call of the binding contributes when the kernel compiles a reverse pass into
[compiled reverse Core](#compiled-reverse-core). A declared smooth map is one
step pulled back by its [Jacobian table](#jacobian-table). `compose` chains
the maps of two operands. `linearize` builds a tape whose map and point a
reverse pass of the tape reads. A pullback, a differential or the reverse pass
of a tape is a reverse pass, and its call is a
[reverse site](#reverse-site). The other bindings have the rule `none`. See [Add an indexed primitive](../development/primitives.md).

## Derived basis

A basis that `derived(b, s)` declares for the basis `b` in the
[derived space](#derived-space) `s`: the dual basis in a dual space, and the
conjugate basis in a conjugate space. See
[Dual and conjugate spaces](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces).

## Derived space

The dual space or a conjugate space of a [space](#space), declared with
`dual` or `conjugate`. It is a different space from every other space. See
[Dual and conjugate spaces](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces).

## Descriptor object

An object of an implementation with the representation `affine_descriptor`,
such as an object of type `Scheme` or `CInfScheme`, which `Affine(QQ, n)` or
`Affine(CInfReal, n)` builds. It records only its dimension. See
[Implementations](../indexed-source.md#implementations) and
[Geometric types](../language/geometric-types.md).

## Diagnostic

The report that the compiler writes for a program that it rejects, or for a
command that it cannot carry out. It has a [code](#code) and a message, and it
may have a [place](#place) and [notes](#note). See
[Diagnostics](../language/diagnostics.md) and the
[guide](../guide/diagnostics-and-cli.md#reading-a-diagnostic).

## Dispatch

The static selection of one method of a generic from the argument types. The
compiler makes and checks every choice at compile time, and no method lookup
happens at run time. Expected results never influence the choice. See
[Selection](../stage1a.md#selection) and the
[guide](../guide/dispatch.md#how-a-method-is-chosen).

## Dispatch key

A tuple of argument types from `Nat`, `Int`, `Bool` and `Unit`, one per
parameter of a generic. It is also called a **key**. The checker examines
every key for ambiguity, including keys outside the
[callable domain](#callable-domain). See
[Generic declarations](../stage1a.md#generic-declarations) and
[Selection](../stage1a.md#selection).

## Domain

The word has two meanings:

1. The domain of a generic is the list of [keys](#dispatch-key) in its
   `domain` clause. Callers may call the generic at these keys and at the keys
   of its abstract methods; compare [callable domain](#callable-domain). See
   [Generic declarations](../stage1a.md#generic-declarations) and the
   [guide](../guide/dispatch.md#generics-and-methods).
2. The domain of an `indexed classification` is the complete finite list of
   implementations that it classifies. The domain of an implementation is
   that implementation alone. See
   [Classifications](../indexed-source.md#classifications) and the
   [guide](../guide/indexed-profile.md#a-classification).

## Edit authority

The right to add methods to a generic. The module that defines the generic
holds it first, and a [transfer](#transfer) moves it to another module.
Imports, `pub`, qualified names and child modules do not grant it. A
[grant](#grant) lets an assembly borrow it for a region as an edit loan, which
the recipient's contribution uses.
A transfer does not move authority over abstract-type membership or
abstract-method contracts. See
[Edit authority](../guide/modules-and-authority.md#edit-authority) and
[Transfers](../language/edit-authority.md#transfers).

## Edit loan

Temporary, exclusive edit authority over a region of a generic. An assembly
takes it from a grant with `borrow` and gives it back with `return`. A loan from
a `delegable` grant or delegation can be lent on as a nested loan through a
[delegation](#delegation). An edit loan grants no access to storage; compare
[storage loan](#storage-loan).
See [Assemblies](../language/edit-authority.md#assemblies).

## Entry point

The function `main` of a program, with the signature `fn main() -> Int`, or a
`resource fn main() -> Int` in manifest mode. `vastitas build` requires one,
and the executable prints the integer that it returns. See
[The entry point](../language/programs.md#the-entry-point).

## Erased evaluator

The evaluator of a [registry entry](#registry-entry) that computes a
[primitive](#primitive) call on the runtime structures that generated
programs link. It applies operations of `IndexedRuntime`, `AlgebraRuntime`
or `SmoothRuntime`. Compare [logical evaluator](#logical-evaluator) and
[erasure](#erasure). See
[Add an indexed primitive](../development/primitives.md#terms).

## Erasure

The word has two qualified uses:

1. The **erasure of a primitive value** maps a value of the Core semantics to
   the runtime structure that generated programs link, such as a smooth
   program or a fiber. The oracle proves for every
   [registry entry](#registry-entry) that a successful logical evaluation
   erases to the entry's [erased evaluator](#erased-evaluator) on the erased
   operands. See
   [Add an indexed primitive](../development/primitives.md#terms).
2. Elsewhere, erasure removes what only the checker needs before native
   execution, such as nominal tags and the function values that
   [specialization](#specialization) erases. See
   [Compiler protocols](../protocol.md).

## Event

One step of an [assembly](#assembly): `borrow`, `reborrow`, `apply`,
`return`, `transfer` or `seal`. The compiler replays the events in order. See
[Assemblies](../language/edit-authority.md#assemblies).

## Existential package

A value that hides a witness object together with fields whose types depend on
it, such as a point on the hidden object. `pack` creates one. Each `unpack`
opens it with a fresh scoped identity, even when the same package is opened
twice. An `indexed package` declaration declares a package type such as
`Pointed`. An existential package is unrelated to a [package](#package) of
source code. See
[Existential packages](../language/geometric-types.md#existential-packages),
the [guide](../guide/indexed-geometry.md#existential-packages) and
[Existential packages](../indexed-source.md#existential-packages) of indexed
declarations.

## Expected type

The type that the position of an expression requires, such as the annotation
of a `let` statement or the type of a parameter for an argument. An integer
literal has type `Nat` where its expected type is `Nat`, and `Int` otherwise.
See [Literal expressions](../language/expressions.md#literal-expressions).

## Export

The `[geometry_compat]` table of a manifest. It maps the syntax of the
geometric core, such as `Point<X, Base(QQ)>` and `origin(X)`, to indexed
declarations for a program in manifest mode. See
[Geometry compatibility exports](../packages.md#geometry-compatibility-exports)
and [Core geometry syntax](../indexed-source.md#core-geometry-syntax).

## Extent

A size in a `runtime_` statement or type: a literal, or a `Nat` or `Int`
binding that the program computes. See
[Runtime extents](../storage/resource-programs.md#runtime-extents).

## Failure value

The value of a [tangent or cotangent fiber](#tangent-or-cotangent-fiber) family
that stands for no vector or covector. A cotangent pullback returns it for a
covector that is not at the image point, and every pullback of the failure
value is the failure value. It is at no point, and it equals no value, itself
included. Its components and its pairings read `(0, 0)`, which no rational
number reads. See [Fiber primitives](../language/smooth-declarations.md#fiber-primitives) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Family

A type former declared with `indexed family`. Its parameters are objects,
markers, domains or natural numbers. `Point` and `Morphism` are families. See
[Families](../indexed-source.md#families) and the
[guide](../guide/indexed-profile.md#families-of-types).

## Fiber product

The presented affine object `fiber(X, Y)` of two presented affine objects over
a common base. It is unrelated to a
[tangent or cotangent fiber](#tangent-or-cotangent-fiber). See
[Fiber products](../affine-geometry.md#fiber-products).

## Field

A value that an [existential package](#existential-package) of indexed
declarations holds beside its witness. A [case](#case) of an `indexed package`
declaration lists the fields, each as a family with its
[bound indices](#bound-index). The word is unrelated to an exact field of
coefficients. See
[Existential packages](../indexed-source.md#existential-packages).

## Flat mode

The compiler mode that takes one entry file and any number of `--lib`
libraries, without a manifest. Flat mode has no modules, imports, `pub` or
other package-only declarations. Compare [manifest mode](#manifest-mode). See
[Flat mode](../language/programs.md#flat-mode).

## Floating-point literal

A token such as `1.5`, `125e-3` or `0x1.8p1`. It is valid only as a number
of a [payload](#payload). See
[Other literals](../language/lexical-structure.md#other-literals).

## Forward Core

The `let`s of [compiled reverse Core](#compiled-reverse-core) that bind the
input point of a [reverse site](#reverse-site) and its image along each map of
the site, in application order, as ordinary Core values. The images are
evaluated points; the input point is the point operand as the source gives
it. They stand at a saved site, and inside the
[backward Core](#backward-core) of a recomputing site, which binds only the
images that its steps read. The last image is the primal value, and the other
points are the [residuals](#residual). Compare [backward Core](#backward-core). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

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
[Function values](../stage1b.md) and the
[guide](../guide/function-values.md).

## Generic

A function with several methods, declared with `generic` together with its
arity and domain. Dispatch selects one method for each call. A generic is not a
function value. See
[Generic declarations](../stage1a.md#generic-declarations) and the
[guide](../guide/dispatch.md#generics-and-methods).

## Global object

The one object that an `indexed global` declaration declares. Types name it by
its path, and a primitive with the binding `global(G)` gives it as a value.
Two global objects are different objects. See
[Global objects](../indexed-source.md#global-objects).

## Grant

A `grant` declaration offers a [region](#region) of edit authority over a
generic to one recipient module. It becomes usable once its module has received
that authority. The grant names the recipient by its package's manifest
`[package] name` and its module path. A grant is a permission, not a loan: an
assembly borrows it to obtain an edit loan. See
[Grants and delegations](../language/edit-authority.md#grants-and-delegations).

## Grouping

The part `axes(…), s` of a [tensor](#tensor) declaration. It says which axes
index the rows and which the columns of the matrix that stores the cells. See
[Tensors](../linalg/networks-and-packing.md#tensors).

## Guarantee

A property that every program that the compiler [accepts](#accept) has, or
that every run of the compiler has. A guarantee reaches as far as its
evidence. See [Guarantees](../language/guarantees.md).

## Higher-order function

A function with a function parameter or a function result. See
[Specialization](../stage1b.md#specialization).

## Identity Gram data

The Gram data of a [metric](#metric) that is `orthonormal`, a
`scaled_identity` with the entry 1 or a `diagonal` whose entries are all 1.
`adjoint` and `hermitian` need it. Over a space of dimension 0 every metric
has it. See [Metrics](../linalg/transforms-and-metrics.md#metrics).

## Implementation

An `indexed implementation` declaration, such as `Grid`. It records a
coefficient marker, a [representation](#representation) and its
[capabilities](#capability). See
[Implementations](../indexed-source.md#implementations).

## Indexed declaration

A declaration that begins with `indexed`. Its kinds are `marker`,
`implementation`, `classification`, `global`, `family`, `package`,
`primitive`, `affine`, `morphism`, `metric`, `evidence`, `iso` and
`cartesian`. Indexed declarations let any package declare an indexed
[profile](#profile), and the standard geometry library uses them. See
[Indexed declarations](../indexed-source.md),
[Smooth affine declarations](../language/smooth-declarations.md) and the
[guide](../guide/indexed-profile.md).

## Indexed type

A type that applies a family of an `indexed` declaration to its arguments, such
as `geo::Point<X, geo::Base>`, or the type `Object<D, M>` of an object. See
[Indexed types](../language/types.md#indexed-types).

## Involution

The scalar involution of a linear implementation: the identity for real
coefficients and complex conjugation for complex ones. `involution` declares
a binding of it. See
[Dual and conjugate spaces](../linalg/transforms-and-metrics.md#dual-and-conjugate-spaces).

## Isomorphism

An `indexed iso` declaration: the checked statement that two declared
[morphisms over a base](#morphism-over-a-base) are inverse to each other. See
[Isomorphisms](../affine-geometry.md#isomorphisms).

## Issuer

The module that declares a grant or a delegation. See
[Grants and delegations](../language/edit-authority.md#grants-and-delegations).

## Item

A declaration at the top level of a source file or of a module, such as a
function, a generic or a module. Statements and expressions occur only inside
items. See [Items](../language/items.md).

## Jacobian step

The step of [backward Core](#backward-core) along a declared
[smooth map](#smooth-map). It applies the transpose of the map's
[Jacobian table](#jacobian-table), evaluated at the saved input point, to the
seed. It gives the [failure value](#failure-value) unless the seed lies over
the saved output point. Compare [opaque step](#opaque-step). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Jacobian table

The matrix of partial derivatives of a declared [smooth map](#smooth-map), as
polynomials with rational coefficients. The kernel computes it from the map
when it generates the program, and the generated code declares each distinct
table once as a [shared literal](#shared-literal).
A step of [backward Core](#backward-core) along the map evaluates the table at
the saved input point and applies its transpose to the seed. That step is a
[Jacobian step](#jacobian-step). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Kernel

The Lean program in `lean-kernel/` that checks every program independently of
the frontend. It resolves names, allocates identities, checks every body and
generates code from the checked result. It depends on the Lean
distribution only. See [Compiler architecture](../development/architecture.md).

## Key

See [dispatch key](#dispatch-key).

## Lambda

A function expression such as `fn(x: Int) -> Int { x + 1 }`. A lambda states
every parameter type and its result type, and it captures nothing from its
surroundings. See
[Lambda expressions](../language/expressions.md#lambda-expressions) and the
[guide](../guide/function-values.md#no-captures).

## Layout

The descriptor `layout(offset, rows, columns, leading, transposed)` of a
[view](#view). It describes a column-major rectangle in an allocation: a byte
offset, the numbers of stored rows and columns, the leading dimension in
cells and a transposition flag. See
[Storage types](../storage/resource-programs.md#storage-types) and the
[guide](../guide/storage.md#resource-functions).

## Limit

A fixed bound of the compiler on the size of a program or on the work of
checking it. A program beyond a limit is an error. See
[Limits](../language/limits.md) and [Appendix D](limits.md).

## Line separator

A character that ends a line in another convention than LF or CR LF, such as
a form feed or U+2028. A source file contains none. See
[Source text](../language/lexical-structure.md#source-text).

## Linear implementation

An `indexed implementation` with a `linear_descriptor` representation. It
says over which base object and with which coefficients, real or complex, its
[spaces](#space) are. See
[Linear implementations](../linalg/maps-and-gemm.md#linear-implementations).

## Logical evaluator

The evaluator of a [registry entry](#registry-entry) that computes the value
of a [primitive](#primitive) call on the values of the Core semantics. Compare
[erased evaluator](#erased-evaluator). See
[Add an indexed primitive](../development/primitives.md#terms).

## Logical path

The names of the modules from the root module of a package down to a module,
such as `math::exact`. The file of a file module depends only on its logical
path. See [Module declarations](../language/modules.md#module-declarations).

## Lowering

The text or the smaller form that a compiler pass produces for a checked
construct. The lowering of a [primitive](#primitive) call is the Lean text
that code generation writes for it from the texts of its operands. The
`render` field of the binding's [registry entry](#registry-entry) produces
it. Other passes lower checked source to [Core](#core), and their checked
records keep the lowering equation. See
[Add an indexed primitive](../development/primitives.md#terms).

## Manifest

The file `Vastitas.toml` at the root of a package. It names the package and its
dependencies. See [Manifests](../packages.md#manifests) and the
[guide](../guide/stdlib.md#a-manifest).

## Manifest diagnostic

A [diagnostic](#diagnostic) for an error in the text of a manifest. It names
the manifest and has the code `E_MANIFEST`. See
[Diagnostic lines](../language/diagnostics.md#diagnostic-lines).

## Manifest mode

The compiler mode that takes one manifest with `--manifest-path`. Modules,
imports, resource functions, indexed declarations and edit-authority
declarations appear only in this mode. Compare [flat mode](#flat-mode). See
[Manifest mode](../language/programs.md#manifest-mode).

## Marker

A coefficient marker, such as `QQ`. A package declares a marker with
`indexed marker`, and the core geometry syntax spells the markers `QQ` and
`CInfReal`. An implementation records its marker. A marker is not an object:
`QQ` and the [base object](#base-object) `Base(QQ)` differ. See
[Markers](../indexed-source.md#markers) and the
[guide](../guide/indexed-profile.md#a-marker-and-an-implementation).

## Mathematical bridge

The proof package in `lean-bridge/`. It proves with mathlib what the kernel's
definitions mean; the kernel, the oracle and the compiler do not depend on it.
A claim with status Proved (bridge) cites its theorems. See
[Independent mathematical bridge](../verification.md#independent-mathematical-bridge).

## Matrix bound

A number that bounds the size of the Gram matrix of a
[metric form](#metric-form) as a whole: the product of the Euclidean norms of
its rows, each cleared of its denominators, and of the largest least common
denominator of a row. It limits the size of the certificates of
[nondegenerate evidence](#nondegenerate-evidence) and
[Riemannian evidence](#riemannian-evidence), which the bound on one entry
does not. See [Metrics](../language/smooth-declarations.md#metrics) and
[Smooth metrics](limits.md#smooth-metrics).

## Method

One body of a generic. A method gives each parameter a selector, declares a
result type and may require capabilities. See
[Method declarations](../stage1a.md#method-declarations) and the
[guide](../guide/dispatch.md#generics-and-methods).

## Metric

A Hermitian form on a numerical [space](#space), declared with `metric` by
its diagonal Gram matrix in a basis. A program names a metric wherever an
adjoint or a Hermitian pairing needs one. Compare
[metric form](#metric-form). See [Metrics](../linalg/transforms-and-metrics.md#metrics).

## Metric form

A family with the `metric_form` representation, such as `MetricForm<X>`, over
a [smooth affine object](#smooth-affine-object) `X`. An `indexed metric`
declaration names a metric form and gives a constant symmetric Gram matrix in
the coordinates of `X`. No value has a metric form type. `flat` and `sharp`
name their metric explicitly, and no metric is ever selected by default. A
metric form is distinct from the diagonal Hermitian `Metric` of
[transforms and metrics](../linalg/transforms-and-metrics.md). See
[Metrics](../language/smooth-declarations.md#metrics) and the wire
[metric forms](../protocol.md#protocol-9-metric-forms).

## Module

A namespace inside a package. The root source file is the **root module** of
the package. A child module is an **inline module**, a `mod name { ... }`
block, or a **file module**, a file that `mod name;` loads. Each module has a
[logical path](#logical-path) from the root module. See
[Modules](../language/modules.md).

## More specific

Method `a` is more specific than method `b` when its selectors are no
broader, its requirements are no weaker, and one of these comparisons is
strict. See [Selection](../stage1a.md#selection).

## Morphism over a base

A value of a [relative family](#relative-family), such as `Over<X, Y, S>`: a
morphism from the [presented affine object](#presented-affine-object) `X` to
`Y` that commutes with their [structure maps](#structure-map) to `S`. A
declared morphism gives each coordinate of the target as a polynomial in the
coordinates of the source. See
[Morphisms over a base](../affine-geometry.md#morphisms-over-a-base) and the
[guide](../guide/affine-geometry.md#morphisms-are-written-as-pullbacks).

## Native refinement

The statement that the executable of a program computes the value of the
program that the checker accepted. It is not proved: it rests on the Lean
compiler and the C compiler, and tests exercise it. See
[What acceptance means](../language/guarantees.md#what-acceptance-means).

## Network

A graph of [occurrences](#occurrence) of numerical maps whose
[ports](#port) an edge contracts. A `contract` block declares a network of
two maps. See [Two-map networks](../linalg/networks-and-packing.md#two-map-networks).

## Nominal identity

Identity that comes from a declaration or a construction, never from structure.
Every `Affine(...)` construction and every `space` declaration has a fresh
identity. Equal settings, base objects, dimensions or descriptors never
identify two objects. Abstract types and indexed declarations also have nominal
identity. See [Object identity](../language/geometric-types.md#object-identity) and the
[guide](../guide/indexed-geometry.md#identity-is-nominal).

## Nominal object

An object with [nominal identity](#nominal-identity), such as the result of
`Affine(QQ, 2)`. A point's type names the object that the point lies on. See
[Object identity](../language/geometric-types.md#object-identity) and the
[guide](../guide/indexed-geometry.md#identity-is-nominal).

## Nondegenerate evidence

An `indexed evidence` declaration `nondegenerate(g)` for a metric `g` with Gram
matrix `G`. The kernel computes an inverse `B` of `G`, and it checks again that
`G B` and `B G` are the identity. A singular Gram matrix has no nondegenerate
evidence. `sharp` requires nondegenerate evidence for its metric. See
[Metric evidence](../language/smooth-declarations.md#metric-evidence) and the wire
[metric forms](../protocol.md#protocol-9-metric-forms).

## Normal form

The canonical representative of a polynomial in the
[coordinate ring](#coordinate-ring) of a presented affine object: its
remainder on division by the reduced Gröbner basis of the relations. Two
polynomials are equal in the coordinate ring exactly when their normal forms
are equal. See
[Presented affine objects](../affine-geometry.md#presented-affine-objects).

## Note

A line of a [diagnostic](#diagnostic) that points to a related
[place](#place), such as the construction that introduced an identity. See
[Diagnostic lines](../language/diagnostics.md#diagnostic-lines).

## Numerical map

A [view](#view) of storage presented as the matrix of a linear map between
two [spaces](#space), in a named [basis](#basis) of each. A `map` statement
declares one, and `gemm` multiplies two. Also called a **map**. See
[Maps](../linalg/maps-and-gemm.md#maps).

## Object type

A type `Object<D, K>`, where `D` names a classification or an implementation
and `K` a marker. Its implementations are the implementations in the
[domain](#domain) of `D` whose marker is `K`. One object type lies within
another when both name the same marker and every implementation of the first
is an implementation of the second. See
[Object types](../indexed-source.md#object-types).

## Occurrence

A node of a [network](#network) or of a contraction tree. It stands for one
use of a map or of a [tensor](#tensor). See
[Two-map networks](../linalg/networks-and-packing.md#two-map-networks) and
[Contraction trees](../linalg/networks-and-packing.md#contraction-trees).

## Opaque step

A map of a [reverse site](#reverse-site) whose structure the compilation does
not open. Function parameters, values of branches and calls and
`composite(…)` are opaque steps, and so are maps that the `reverseLeaves`
[limit](limits.md#checker-limits) does not reach: a `let`-bound map beyond
the remaining budget, or a whole map operand whose `compose` calls exceed it.
[Backward Core](#backward-core) pulls the seed back along an opaque step with
the [runtime reverse pass](#runtime-reverse-pass) in the site's residual
policy. Compare [Jacobian table](#jacobian-table). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Oracle

The Lean proof package in `lean/`. It proves theorems about the kernel's
definitions. Compilation and generated programs never run it. See
[Verification boundaries](../verification.md).

## Owned map

A storage [owner](#owner) whose allocation holds the initialized matrix of a
map between two bases. `owned` makes one, and `OwnedMap<bs, bt>` is its type
as a parameter or result. See
[Owned maps](../linalg/maps-and-gemm.md#owned-maps).

## Owned result

An owner that a resource function hands to its caller. The function declares
it after `returns`. See
[Resource functions](../storage/resource-programs.md#resource-functions).

## Owned-map package

An owner that `pack` makes from an [owned map](#owned-map) and that hides
the target space and its basis. `OwnedMapTo<bs, n>` is its type. It is not
usable as an owned map until `unpack` opens it with a fresh space and basis. It is not a [package](#package) of source files. See
[Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages).

## Owner

The word has three meanings. Qualify it where the context does not decide.

1. The **owner** of a function or other declaration is its defining package,
   [logical path](#logical-path) and name. Aliases, reexports, file names and read order
   never change it. See [Owners](../language/edit-authority.md#owners).
2. The **current owner** of a generic is the module that holds its edit
   authority: its defining module, until a [transfer](#transfer) changes it.
   See [Owners](../language/edit-authority.md#owners) and
   [Transfers](../language/edit-authority.md#transfers).
3. A **storage owner** is a binding that owns an
   [allocation](#allocation). `allocate` creates one, `move` and calls hand
   it on, and `drop` frees it. See
   [Storage types](../storage/resource-programs.md#storage-types) and the
   [guide](../guide/storage.md#the-statements).

## Package

A directory with a `Vastitas.toml` manifest, a root source file and modules.
Compare [existential package](#existential-package). See
[Packages](../packages.md) and the [guide](../guide/stdlib.md).

## Package graph

The packages that a root manifest reaches through its dependencies. The
compiler checks every package of the graph. See
[The package graph](../packages.md#the-package-graph).

## Path

A sequence of names separated by `::` that names a declaration, such as
`std::arithmetic::generic::add`. Its first segment may be `package`, `self`,
`super` or a dependency alias. See [Names and paths](../language/names-and-paths.md).

## Payload

The value of one cell of storage in a resource statement, written `f64(…)`,
`complex(…)`, `f64_bits(…)` or `complex_bits(…)`. A payload is one exact
binary64 value, or two for a complex cell; the compiler never rounds one. See
[Payloads](../storage/resource-programs.md#payloads).

## Place

The position that a [diagnostic](#diagnostic) or a [note](#note) names: a
file, a line and a column. See [Places](../language/diagnostics.md#places).

## Port

An end of an [occurrence](#occurrence) that an edge may contract: the input
or the output of a map in a network, or one axis of a tensor in a contraction
tree. See [Two-map networks](../linalg/networks-and-packing.md#two-map-networks) and
[Contraction trees](../linalg/networks-and-packing.md#contraction-trees).

## Presented affine object

An object declared by `indexed affine` under an implementation with the
`presented_affine` representation: `spec[…]` with coordinates and polynomial
relations, a [fiber product](#fiber-product) or a
[principal open](#principal-open). It stands for the affine scheme of its
[coordinate ring](#coordinate-ring). Each declaration is one object. A
presented affine object is distinct from a descriptor object and from a
[smooth affine object](#smooth-affine-object). See
[Presented affine objects](../affine-geometry.md#presented-affine-objects)
and the [guide](../guide/affine-geometry.md#objects-given-by-equations).

## Primitive

An `indexed primitive` declaration. It binds a name, such as `origin` or
`compose`, to one of a closed set of primitive bindings. The checker audits
each primitive's representation, domain, arity, capabilities and family shapes.
See [Primitives](../indexed-source.md#primitives).

## Primitive association

The condition that a [primitive shape](#primitive-shape) places on the
operand list and the result of one call: the operands match the shape, every
relation of the shape holds and the result is the shape's result template,
instantiated at the operands. The checker decides it for every call. See
[Add an indexed primitive](../development/primitives.md#terms).

## Primitive binding

In source, the binding of an `indexed primitive` declaration is the part after
`=`, such as `compose(Morphism)`. It fixes the operands and the result of the
primitive. See [Primitives](../indexed-source.md#primitives). In the kernel, a
primitive binding is a constructor of `PrimitiveBinding` with its data: family,
base and object IDs and the embedded maps, matrices or coordinates. It is the
Core-level identity of a [primitive](#primitive) call and has one
[registry entry](#registry-entry). Displayed names and certificate strings
are not part of it. See
[Add an indexed primitive](../development/primitives.md#terms).

## Primitive family

The entry of one wire `op` in the family table of
`IndexedPrimitiveFamilies.lean`: the operation's fields with their kinds in
wire order, whether only protocol 9 admits it, and how the resolved fields
build a [primitive](#primitive) binding. The wire decoder, the resolver and
the frontend's generated table read it. A primitive family is not a
[family](#family) declaration. See
[Add an indexed primitive](../development/primitives.md#3-the-primitive-family).

## Primitive registry

The closed, finite set of [primitive](#primitive) bindings that the checker
accepts. Each binding has one [registry entry](#registry-entry). The checker
derives a binding's validity contract, operand association, result type and
operand count from its registry entry, and code generation the text of a
call. No source spelling or native symbol adds a binding. See
[Closed primitive binding inventory](../internals/indexed-checker.md#closed-primitive-binding-inventory).

## Primitive shape

The part of a [primitive](#primitive) binding's registry entry that lists
its operands, the relations between them and its result. A call of the
binding allocates when the result is a fresh object. The argument hints and the
[role table](#role-table) of the binding come from its shape. See
[Closed primitive binding inventory](../internals/indexed-checker.md#closed-primitive-binding-inventory).

## Principal open

The presented affine object `localize(X, f) inverse u`: the open subset of
`X` on which the polynomial `f` has the inverse `u`. See
[Principal opens](../affine-geometry.md#principal-opens) and the
[guide](../guide/affine-geometry.md#open-subsets).

## Private

Declared without `pub`: visible in the declaring module and in its
descendants only. See [Visibility](../language/names-and-paths.md#visibility).

## Profile

The word has three qualified uses:

1. A **finite profile** is an explicitly bounded part of a broader feature
   that the compiler supports. For example, the
   [two-map network profile](../linalg/networks-and-packing.md#two-map-networks)
   admits two rank-two map occurrences joined by one evaluation edge.
2. An **indexed profile** is a set of indexed declarations that defines a
   geometric setting, such as the ordinary affine profile of
   `examples/packages/indexed/geo.vast`. See
   [Defining an indexed profile](../guide/indexed-profile.md).
3. A **coefficient profile** declares what the coefficients of numerical maps
   mean mathematically. See
   [Coefficient profiles](../guide/numerical.md#coefficient-profiles).

## Program

The set of source files that the compiler checks together: an entry file and
its `--lib` libraries in [flat mode](#flat-mode), or the packages that a
manifest reaches in [manifest mode](#manifest-mode). See
[Programs](../language/programs.md).

## Property

One mathematical fact about a language construct or a standard-library module,
recorded in a [specification](#specification) with an example and one or more
[claims](#claim). See [Specifications](../specifications.md).

## Public

Declared with `pub`: nameable from every module that can reach the declaring
module. See [Visibility](../language/names-and-paths.md#visibility).

## Recipient

The module that a grant, delegation or transfer names after `to`: the manifest
name of its package followed by its logical path. See
[Grants and delegations](../language/edit-authority.md#grants-and-delegations).

## Reexport

A `pub use` declaration, which makes a public declaration of another module
nameable through the current module. The declaration keeps its [owner](#owner), and
the reexport grants no edit authority. See [`use` declarations](../language/modules.md#use-declarations).

## Region

The word has two meanings:

1. The region of a [grant](#grant) or [delegation](#delegation) is a list of
   [keys](#dispatch-key). An edit loan covers that region. See
   [Grants and delegations](../language/edit-authority.md#grants-and-delegations).
2. A storage region is a set of byte intervals in one allocation. Storage loans
   and layouts cover regions. See
   [Regions, overlap and alias evidence](../storage-ownership.md#regions-overlap-and-alias-evidence).

## Registry entry

The `PrimitiveDescriptor` value of one [primitive binding](#primitive-binding)
in the [primitive registry](#primitive-registry). It holds the binding's
[primitive shape](#primitive-shape), its validity contract as a `Prop` and as
a `Bool` with the proof that they agree, its
[logical](#logical-evaluator) and [erased evaluators](#erased-evaluator),
its [lowering](#lowering), its [shared literals](#shared-literal) and its
[derivative rule](#derivative-rule). See
[Add an indexed primitive](../development/primitives.md).

## Relative family

A [family](#family) with the `relative` representation, such as `Over`. Its
application `Over<X, Y, S>` is the type of the
[morphisms over a base](#morphism-over-a-base) from `X` to `Y` over `S`. See
[The presented profile](../affine-geometry.md#the-presented-profile).

## Representation

The word after the marker in an `indexed implementation` declaration, such as
`affine_descriptor`: it says what an object of the implementation holds. The
word after `=` in an `indexed family` declaration, such as `point`, is the
representation of the family: it says which values the types of the family
have. See [Implementations](../indexed-source.md#implementations) and
[Families](../indexed-source.md#families).

## Reserved name

An identifier that no declaration or binding may use, such as a built-in type
name, a built-in function name or a name that begins with `__vastitas_`. An
`indexed` declaration may use the names of the geometric core, such as `Point`.
Compare [strict keyword](#strict-keyword). See
[Reserved names](../language/lexical-structure.md#reserved-names).

## Residual

Saved data that a later pullback reads. In
[compiled reverse Core](#compiled-reverse-core), the residuals of a
[reverse site](#reverse-site) are its input point and its images before the
last map. The [forward Core](#forward-core) binds them as immutable Core
values. A saved site passes them, and the primal value, to its
[backward Core](#backward-core). A recomputing site passes the input point,
and the backward Core evaluates again the points that it reads. See
[Reverse residual retention and mutation](../storage-ownership.md#residual-retention).

## Resource function

A function declared with `resource fn`. Its body is a sequence of resource
statements followed by a pure `value { ... }` block. See
[Resource functions](../storage/resource-programs.md#resource-functions) and
the [guide](../guide/storage.md#resource-functions).

## Result

The expression at the end of a block, without a semicolon. The value of the
block is the value of its result. See
[Block expressions](../language/expressions.md#block-expressions).

## Reverse site

A call whose [derivative rule](#derivative-rule) is a reverse pass: a
[cotangent pullback](#cotangent-pullback) in either mode, a differential, or
the reverse pass of a [tape](#tape) that `linearize` builds. The kernel
replaces each reverse site whose maps it can read by
[compiled reverse Core](#compiled-reverse-core). Any other site stays a call
of the [runtime reverse pass](#runtime-reverse-pass). See
[Compiled reverse Core](../verification.md#compiled-reverse-core).

## Riemannian evidence

An `indexed evidence` declaration `riemannian(g)` for a metric `g` with Gram
matrix `G`. The kernel computes a factorization `G = L D Lᵀ`, where `L` is unit
lower triangular and every entry of the diagonal `D` is positive. It also
computes an inverse of `L`, and it checks every identity again. Only a
positive-definite Gram matrix has Riemannian evidence. It is the wrong kind of
evidence for `sharp`, which requires
[nondegenerate evidence](#nondegenerate-evidence). See
[Metric evidence](../language/smooth-declarations.md#metric-evidence) and the wire
[metric forms](../protocol.md#protocol-9-metric-forms).

## Role table

The requirements that a [primitive shape](#primitive-shape) places on the
operand types of one call, in a fixed order: the operands' families, then their
fixed indices, then the shape's relations. The table lists them once the
operands have the shape's index pattern; `relative_coefficient` and
`relative_pair` list the families as soon as each operand is of the expected
kind. Every requirement is part of the binding's contract. When a call of a
valid binding fails a listed requirement, the diagnostic names the first one;
otherwise it lists the operand types. See
[Closed primitive binding inventory](../internals/indexed-checker.md#closed-primitive-binding-inventory).

## Root manifest

The manifest that a command names with `--manifest-path`. See
[The package graph](../packages.md#the-package-graph).

## Root package

The package of the [root manifest](#root-manifest). Its root module holds the
entry point and the assembly of the program. See
[Manifest mode](../language/programs.md#manifest-mode).

## Run-time check

A check that an executable makes on values that the compiler does not know,
and whose failure stops the executable. Examples are an `expect` statement
and a condition on [extents](#extent). See
[Run-time checks](../language/guarantees.md#run-time-checks).

## Run-time diagnostic

The line that an executable writes to standard error when a
[run-time check](#run-time-check) fails. See
[Run-time diagnostics](../language/diagnostics.md#run-time-diagnostics).

## Runtime reverse pass

The verified routine of the smooth runtime that runs a reverse pass over a
program value: `SmoothRuntime.pullback`, `backward`, `differential` and
`linearize`. [Backward Core](#backward-core) calls it for an
[opaque step](#opaque-step), and a [reverse site](#reverse-site) that the
compilation cannot read stays a call of it. See
[reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives).

## Scalar base

An `indexed implementation` with a `scalar_base` representation: the base of
a geometric setting with real or complex coefficients. A
[linear implementation](#linear-implementation) names a global of one. See
[Linear implementations](../linalg/maps-and-gemm.md#linear-implementations).

## Scalar type

One of the types `Nat`, `Int`, `Bool` and `Unit`. Dispatch uses only scalar
types. See [Scalar types](../language/types.md#scalar-types).

## Scheme

`Scheme` classifies ordinary affine descriptor objects, and `CInfScheme`
classifies smooth descriptor objects. A descriptor object records only its
dimension. No implicit bridge connects the two settings. A `CInfScheme` object
is not a [smooth affine object](#smooth-affine-object). See
[Geometric types](../language/geometric-types.md) and the
[guide](../guide/indexed-geometry.md#objects-points-and-morphisms).

## Seal

The `seal` [event](#event) of an assembly. Sealing a generic checks its final
set of methods: no ambiguity, a winner at every key of the callable domain,
and wins of contributed methods only inside the region of each grant. See
[Sealing](../language/edit-authority.md#sealing) and the
[guide](../guide/edit-authority.md#regions-and-the-seal).

## Seed

The covector that a [cotangent pullback](#cotangent-pullback) or a reverse pass
starts from. A seed must lie over the image of the point; any other seed gives
the [failure value](#failure-value). See
[reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives).

## Selector

The type that a method gives a parameter for dispatch: a concrete scalar type,
`Number`, `Any` or an abstract type. See
[Method declarations](../stage1a.md#method-declarations) and the
[guide](../guide/dispatch.md#selectors-and-capabilities).

## Setting

The kind of a core geometric object: `Scheme` for ordinary objects and
`CInfScheme` for smooth ones. Each setting has one coefficient
[marker](#marker). See [Scheme](#scheme) and
[Settings and markers](../language/geometric-types.md#settings-and-markers).

## Shared literal

A basis, a matrix, a map or a [Jacobian table](#jacobian-table) that a
generated module declares once and that the [lowering](#lowering) of every
call that uses it names. A basis is declared as `basis_k`, the Gram matrix of
a metric or its inverse as `matrix_k`, the map of a relative or smooth
constant as `map_k`, and a Jacobian table as `jacobian_k`. The `literals`
field of a [registry entry](#registry-entry) lists the shared literals of the
binding's calls. See
[Add an indexed primitive](../development/primitives.md#2-the-registry-entry).

## Signature probe

A typed placeholder result that an abstract function parameter supplies during
the signature-probe pass. That pass checks every definition, including unused
higher-order functions and lambdas. A separate pass specializes executable
calls, and signature probes never enter it or the generated code. See
[Function specialization](../internals/checking-pipeline.md#function-specialization).

## Smooth affine object

An object declared as `Affine(n)[c₁, …, cₙ]` under an implementation with the
`smooth_affine` representation. It stands for the smooth real affine space
ℝⁿ with the named coordinates. Each declaration is one canonical object. A
smooth affine object is distinct from a descriptor object, such as a
`CInfScheme` object, and from a presented affine object. See
[Smooth affine objects](../language/smooth-declarations.md#smooth-affine-objects) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Smooth map

A value of a family with the `smooth` representation, such as
`Smooth<X, Y>`, between two [smooth affine objects](#smooth-affine-object). It
is a polynomial map with exact rational coefficients. A declared smooth map
gives each target coordinate as a polynomial in the source coordinates.
`compose` builds a program from smooth maps and does not expand it. See
[Smooth maps](../language/smooth-declarations.md#smooth-maps) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Source

The object `X` of a morphism type `Morphism<X, Y>`. Compare
[target](#target). See [Geometric types](../language/geometric-types.md).

## Source limit

A [limit](#limit) on the text and the files of a program, such as the nesting
of expressions. The other limits bound the program that the checker builds.
See [Source limits and limits of the checked program](../language/limits.md#source-limits-and-limits-of-the-checked-program).

## Space

A linear space declared with `space` in a resource function. Each `space`
declaration makes a fresh nominal space, so two spaces of dimension 2 are
different spaces. See
[Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) and the
[guide](../guide/numerical.md#spaces-bases-and-maps).

## Specialization

The compilation step that erases function values. The compiler checks each
lambda and each [higher-order function](#higher-order-function) on its own
and for the function values that the program passes to it. Each check is a
[specialized instance](#specialized-instance), and their number has a limit
that [Appendix D](limits.md) gives. See
[Specialization](../stage1b.md#specialization), the
[guide](../guide/function-values.md#specialization) and
[Function specialization](../internals/checking-pipeline.md#function-specialization).

## Specialized instance

One check of a lambda or of a
[higher-order function](#higher-order-function): one on its own, and one for
each combination of function values that the program passes to it. See
[Specialization](../stage1b.md#specialization).

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

## Static target

The one function definition that a call of a function value resolves to after
the compiler substitutes the function arguments. See
[Static targets](../stage1b.md#static-targets).

## Status words

Implemented, Tested, Proved and Planned: the four kinds of statement that the
book keeps apart. The [Introduction](../index.md#what-exists-today) defines
them. A [claim](#claim) has one of the six
[claim statuses](../specifications.md#claim-statuses) instead.

## Storage loan

Temporary access to one [view](#view) of the allocation of a storage
[owner](#owner). `borrow` creates a `read`, `write` or `read_write` loan, and
`release` ends it. Loans whose views may overlap must all be read loans,
apart from a loan and its [children](#child). A
storage loan grants no edit authority; compare [edit loan](#edit-loan). See
[Storage types](../storage/resource-programs.md#storage-types) and
[Ownership and explicit transitions](../storage-ownership.md#ownership-and-explicit-transitions).

## Strict keyword

A word with a fixed meaning that is never an identifier, such as `fn`, `let`
or `if`. Other words, such as `pub`, act as keywords only where a construct
spells them. See [Keywords](../language/lexical-structure.md#keywords).

## String literal

Text between double quotes. It is a token, but no construct accepts one. See
[Other literals](../language/lexical-structure.md#other-literals).

## Structure map

The morphism from a [presented affine object](#presented-affine-object) to
its base. `by(…)` in the declaration gives the image of each coordinate of
the base. See
[Presented affine objects](../affine-geometry.md#presented-affine-objects)
and the [guide](../guide/affine-geometry.md#objects-over-a-base).

## Tangent or cotangent fiber

A value of a family with the `tangent` or `cotangent` representation, such as
`Tangent<X>` or `Cotangent<X>`. It is a vector or covector at a rational point
of the [smooth affine object](#smooth-affine-object) `X`. Its components are
given in the coordinate frame or coframe. It may also be the
[failure value](#failure-value). It is unrelated to a
[fiber product](#fiber-product). See
[Fiber primitives](../language/smooth-declarations.md#fiber-primitives) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Tape

A value of a family with the `tape` representation, such as `Tape<X, Y>`: the
forward values that one evaluation of a [smooth map](#smooth-map) saves at a
point. Only `linearize` builds a tape; a tape has no source or wire form.
`cotangent_backward` runs the reverse pass over a tape. It returns the
[failure value](#failure-value) for a covector that is not at the tape's
output point. See [Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives) and the wire
[smooth forms](../protocol.md#protocol-9-smooth-forms).

## Target

The object `X` of a point type `Point<X, S>`, which the point lies on, or the
object `Y` of a morphism type `Morphism<X, Y>`, whose source is `X`. Compare
[test object](#test-object). See [Geometric types](../language/geometric-types.md).

## Tensor

A [view](#view) of storage presented as an array with two or three ordered
axes, each indexed by a [basis](#basis). `tensor` declares one. See
[Tensors](../linalg/networks-and-packing.md#tensors).

## Test object

The second index `S` of a point type `Point<X, S>`: the point is a point of
its target `X` with values in `S`. The test object of `origin(X)` is the
[base object](#base-object). See
[Geometric types](../language/geometric-types.md).

## Totality lemma

The oracle lemma of one [primitive binding](#primitive-binding) that proves
that an accepted call on typed operand values evaluates to a value of the
checked result type. The binding's soundness instance builds on it. See
[Add an indexed primitive](../development/primitives.md#5-the-local-proofs).

## Transfer

A `transfer` declaration names an operation that permanently moves edit
authority over a generic to a recipient module. An assembly performs the
transfer. The generic keeps its [owner](#owner); only its current owner
changes. See
[Transfers](../language/edit-authority.md#transfers).

## Transformed map

The dual, the conjugate or the adjoint of a
[numerical map](#numerical-map), declared with `map`. It reads the cells of
that map transposed or conjugated and copies nothing. See
[Transformed maps](../linalg/transforms-and-metrics.md#transformed-maps).

## Vector

A [view](#view) of storage presented as the column of coordinates of a
vector of a [space](#space) in a [basis](#basis). `vector` declares one. See
[Vectors](../linalg/transforms-and-metrics.md#vectors).

## View

A rectangle of [cells](#cell) of an allocation, which a [layout](#layout)
describes. A [storage loan](#storage-loan) gives access to one view, such as
`output` in `borrow output = write(data, layout(...));`. See
[Storage types](../storage/resource-programs.md#storage-types) and the
[guide](../guide/storage.md#resource-functions). A view of a
[morphism over a base](#morphism-over-a-base) is a different thing: the same
morphism over an object further along the base chain. See
[Morphism primitives](../affine-geometry.md#morphism-primitives).

## Whitespace

A character with the Unicode `White_Space` property that is not a
[line separator](#line-separator). Whitespace separates tokens and has no
other meaning. See [Source text](../language/lexical-structure.md#source-text).

## Winner

The method that dispatch selects at a key: the one applicable method that no
other applicable method is more specific than. See
[Selection](../stage1a.md#selection).

## Wire form

The JSON record that stands for one declaration or form in a request of the
[wire protocol](#wire-protocol). The wire form of a [primitive](#primitive)
is an `op` and the named fields of its [primitive family](#primitive-family),
in wire order. See
[Add an indexed primitive](../development/primitives.md#one-family-derived-wire-form).

## Wire protocol

The versioned JSON request that the frontend sends to the kernel, and the
kernel's response. Each request carries a protocol version. See
[Compiler protocols](../protocol.md).

## Witness

The object that an [existential package](#existential-package) hides. See
[Existential packages](../indexed-source.md#existential-packages).

## Witness type

The object type `Object<D, K>` of a [case](#case) `case(D, K)` of an
`indexed package` declaration. The witness of an existential package of that
case has an object type that lies within it, and the witness that `unpack`
binds has the witness type. See
[Existential packages](../indexed-source.md#existential-packages).

## Work budget

A [limit](#limit) on the units of work of one check. It counts units that the
checker defines, not time. See
[Kinds of limits](../language/limits.md#kinds-of-limits).
