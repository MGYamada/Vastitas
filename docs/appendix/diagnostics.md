# Appendix B: Diagnostics reference

This appendix lists every [code](glossary.md#code) of a
[diagnostic](glossary.md#diagnostic) that the compiler or an executable can
report. It groups the codes by the component that reports them, says what
each code reports, and links the rules of the Reference that give the code.
[Diagnostics](../language/diagnostics.md) gives the form of a diagnostic, its
place, the number and the order of the diagnostics of a run, and the exit
status. [Classes of codes](../language/diagnostics.md#classes-of-codes)
groups the codes by construct, and
[Chapter 12](../guide/diagnostics-and-cli.md) shows how to read a diagnostic.

## Components

| Component | What it reports | Section |
| --- | --- | --- |
| The [frontend](glossary.md#frontend) | The errors of the command line, of the files and of the native build, and the errors of source text and syntax. It also reports some errors of names and of sizes before the kernel runs | [Frontend](#frontend) |
| The [kernel](glossary.md#kernel) | Every error of names, types, dispatch, authority, declarations and resources. It is the [checker](glossary.md#checker) | [Kernel](#kernel) |
| The native runtime | The [run-time diagnostics](../language/diagnostics.md#run-time-diagnostics) of an executable | [Native runtime](#native-runtime) |

A code can stand in two sections. The kernel checks again every rule of
names, types and sizes that the frontend reports first, so that it accepts no
program on the word of the frontend.

In the tables, the column "Reports" names the kinds of errors that have the
code, and the column "Rules" links the sections of the Reference that state
them. The message of a diagnostic gives the particular error. The Reference
does not specify the text of a message, as
[Codes](../language/diagnostics.md#codes) says.

<a id="driver-and-frontend"></a>

## Frontend

### Commands, files and builds

These codes report the command and its environment. Only the frontend reports
them, apart from `E_PROTOCOL`, which the kernel reports for a request, as
[Requests and audits](#requests-and-audits) says. Their diagnostics have no
place, apart from `E_LIBRARY` and from an `E_INPUT` for the file of a module,
which has the place of the `mod` declaration. An `E_MANIFEST` names its
manifest.

| Code | Reports | Rules |
| --- | --- | --- |
| `E_USAGE` | A command line that is not valid, and a numerical option for a program that needs none | [Options](../guide/cli.md#options) · [Building a numerical program](../linalg/maps-and-gemm.md#building-a-numerical-program) |
| `E_INPUT` | An input that the compiler cannot use as a file: a file that it cannot read, a file that is not a regular file or not UTF-8, a file with another name than the mode requires, a file supplied twice, and a module without one file of its name inside its package | [Inputs](../guide/cli.md#inputs) · [Flat mode](../language/programs.md#flat-mode) · [Manifests](../packages.md#manifests) · [Module declarations](../language/modules.md#module-declarations) · [Source text](../language/lexical-structure.md#source-text) |
| `E_MANIFEST` | A manifest whose text is not valid: an error of TOML, an unknown or a missing key, an empty name, an invalid version or an invalid dependency alias | [Manifests](../packages.md#manifests) |
| `E_LIBRARY` | A library of flat mode that defines the only function `main` of the program | [Flat mode](../language/programs.md#flat-mode) |
| `E_OUTPUT` | An output path that `build` cannot use | [The output of `build`](../guide/cli.md#the-output-of-build) |
| `E_BACKEND` | A kernel that is missing or that does not start, an answer that neither accepts nor rejects the program, a kernel that fails after it accepts the program, a kernel with another build identity than the compiler expects, and an answer of the kernel beyond the largest size | [The kernel and its build identity](../guide/cli.md#the-kernel-and-its-build-identity) · [Output of the tools](../guide/cli.md#output-of-the-tools) |
| `E_BUILD` | A native build that cannot start or that fails: a missing or another Lean toolchain, a kernel root whose files differ from those of the compiler, a numerical program without `--openblas-prefix`, a package that the compiler cannot lock, and a failure of `lake` | [What `check` and `build` start](../guide/cli.md#what-check-and-build-start) · [Checks on the kernel root](../guide/cli.md#checks-on-the-kernel-root) · [Numerical builds](../guide/cli.md#numerical-builds) |
| `E_INTERRUPTED` | A signal that interrupts `check` or `build` | [Signals](../guide/cli.md#signals) · [Exit status](../language/diagnostics.md#exit-status) |
| `E_PROTOCOL` | An answer of the kernel that the frontend cannot read or use: text that is not an answer, a kernel that writes no answer, an answer of another version of the wire protocol that does not reject the program, a rejection without a diagnostic, and a generated program that imports another module than a runtime module | [The kernel and its build identity](../guide/cli.md#the-kernel-and-its-build-identity) · [Checks on the kernel root](../guide/cli.md#checks-on-the-kernel-root) |

### Source text and syntax

The frontend reports these codes when it reads a source file. The kernel
never sees the text of a file.

| Code | Reports | Rules |
| --- | --- | --- |
| `E_LEX` | Text that forms no token: a byte order mark, a line separator that the language excludes, a character outside ASCII in code, a character that begins no token, and a control or invisible character in a comment | [Source text](../language/lexical-structure.md#source-text) · [Comments](../language/lexical-structure.md#comments) · [Integer literals](../language/lexical-structure.md#integer-literals) |
| `E_PARSE` | Tokens that do not form the construct that a Syntax block gives | The Syntax block of the construct, in the [grammar summary](grammar.md), and the rules that name the code, such as [Source files](../language/programs.md#source-files) and [Kinds of items](../language/items.md#kinds-of-items) |
| `E_UNSUPPORTED` | Syntax that the language does not have, such as a block comment, a string literal or a mutable binding, and an item that the mode of the command does not have, such as a module in flat mode | [Keywords](../language/lexical-structure.md#keywords) · [Other literals](../language/lexical-structure.md#other-literals) · [Kinds of items](../language/items.md#kinds-of-items) · [`let` statements](../language/statements.md#let-statements) · [Types](../language/types.md) |
| `E_RESOURCE_LITERAL` | A payload that is not a binary64 value as written, such as `f64(0.1)` | [Payloads](../storage/resource-programs.md#payloads) |

### Errors that the frontend reports before the kernel

The frontend reports these errors itself, with the code that the kernel has
for the same rule. In flat mode it resolves the names of the whole program
and reports every error of names that it finds, as
[Number and order](../language/diagnostics.md#number-and-order) says. In both
modes it decides the limits on the source and the forms that the parser
reads.

| Code | What the frontend reports |
| --- | --- |
| `E_NAME`, `E_DUPLICATE`, `E_RESERVED`, `E_SHADOW`, `E_CAPTURE`, `E_RECURSION` | In flat mode, the errors of the names and scopes of the program, and one cycle of calls. In both modes, a reserved name where the parser reads a name, and a second assembly in a module |
| `E_MAIN` | In flat mode, a generic named `main` |
| `E_RING` | In flat mode, a coefficient marker such as `QQ` that stands as a value |
| `E_CYCLE` | A cycle of package dependencies, and a module file that loads itself |
| `E_LIMIT` | A program beyond a limit of [Source text](limits.md#source-text) or of [Inputs](limits.md#inputs). Also an assembly, a `diagonal` metric, a polynomial expression, an `Affine` dimension and a position in a constraint beyond their limits |
| `E_TYPE` | A word that the parser does not accept in a type or in an `indexed` declaration, such as an unknown representation of a family, a mode of `cotangent_pullback` other than `saved` or `recomputed`, or an element type of a pair other than `Nat` and `Int` |
| `E_AFFINE_COORDINATE` | `Affine(K, n)[…]` with another number of coordinates than `n` |
| `E_RESOURCE_LIMIT`, `E_RESOURCE_TYPE`, `E_RESOURCE_VALUE` | An integer of a resource function beyond 64 bits, a resource function or a program beyond the limits on statements and `value` blocks, an access mode or a condition that the parser does not accept, and a scalar binding of another type than `Nat`, `Int`, `Bool` and `Unit` |
| `E_NUMERICAL_TYPE`, `E_NETWORK`, `E_TENSOR`, `E_TENSOR_TREE` | A numerical statement whose form the parser does not accept: a mode of `gemm` other than `overwrite` and `accumulate`, a network or a contraction tree with other declarations or more declarations than its form admits, and a grouping or a port that names an axis beyond the third |

### `audit-lean`

Only the command `vastitas audit-lean` reports these codes.
[`audit-lean`](../guide/cli.md#audit-lean) gives its rules.

| Code | Reports |
| --- | --- |
| `E_LEAN_AUDIT` | An export that the command cannot read, that the checker rejects or that holds no declaration, a checker that fails, and a signal that interrupts the audit |
| `E_LEAN_AUDIT_CHECKER` | A pinned Lean toolchain or a checker `nanoda_bin` that is missing or has another version |
| `E_LEAN_AUDIT_POLICY` | A policy of the audit that the command cannot use. The policy is part of the compiler, so this code reports a defect of the compiler |

<a id="lean-kernel"></a>

## Kernel

The kernel reports one diagnostic for a program that it rejects, with the
notes of that diagnostic. The tables of this section follow the constructs of
the Reference. The frontend shows a diagnostic of the kernel at its place in
the source.

### Names, items and the entry point

| Code | Reports | Rules |
| --- | --- | --- |
| `E_NAME` | A name that no declaration or binding of its scope defines: a variable, a function, a type, a module, a component of a path, the generic of a method or an object in a type | [Resolution](../language/names-and-paths.md#resolution) · [Path expressions](../language/expressions.md#path-expressions) · [Calls](../language/functions.md#calls) · [Method declarations](../stage1a.md#method-declarations) |
| `E_DUPLICATE` | A name that one scope declares twice, and a declaration that repeats another: two items of one name, a binding with the name of a binding of its block or of an enclosing block, a method with the signature of another, a key twice in a domain, a second assembly, a grant with a repeated key | [Names of items](../language/items.md#names-of-items) · [Scopes of bindings](../language/statements.md#scopes-of-bindings) · [Method declarations](../stage1a.md#method-declarations) · [Manifests](../packages.md#manifests) |
| `E_RESERVED` | A reserved name as the name of a declaration or of a binding | [Reserved names](../language/lexical-structure.md#reserved-names) · [Keywords](../language/lexical-structure.md#keywords) |
| `E_SHADOW` | A binding with a name of the namespace of its module, such as the name of a function, and a parameter or a binding of a lambda with a name that is visible outside the lambda | [Scopes of bindings](../language/statements.md#scopes-of-bindings) · [Lambdas and their names](../stage1b.md#lambdas-and-their-names) |
| `E_VISIBILITY` | A private declaration that another module names, and a `pub use` that reexports a private declaration | [Visibility](../language/names-and-paths.md#visibility) · [`use` declarations](../language/modules.md#use-declarations) |
| `E_CYCLE` | A cycle of modules or of imports | [`use` declarations](../language/modules.md#use-declarations) · [The package graph](../packages.md#the-package-graph) |
| `E_MAIN` | An entry point with another signature than `fn main() -> Int`, a generic named `main`, a resource function `main` with another result type, and a `build` of a program without an entry point | [The entry point](../language/programs.md#the-entry-point) · [Resource functions](../storage/resource-programs.md#resource-functions) |

### Types, functions and expressions

| Code | Reports | Rules |
| --- | --- | --- |
| `E_TYPE` | A value of another type than its place requires, and a declaration or a type that its rules do not admit. The code serves every construct, including `indexed` declarations and resource functions | [Types](../language/types.md) · [Expressions](../language/expressions.md) · [Indexed declarations](../indexed-source.md) · the chapter of the construct |
| `E_ARITY` | A call, an `unpack` or a declaration with another number of arguments, operands, fields or parameters than its rule fixes | [Calls](../language/functions.md#calls) · [Call expressions](../language/expressions.md#call-expressions) · [Built-in functions](../language/expressions.md#built-in-functions) · [Calls of primitives](../indexed-source.md#calls-of-primitives) |
| `E_OPERATOR` | An operator whose operands have types that it does not accept, including `==` on geometric values | [Operator expressions](../language/expressions.md#operator-expressions) · [Object identity](../language/geometric-types.md#object-identity) |
| `E_RECURSION` | A cycle of calls between functions, methods or specialized instances | [Calls](../language/functions.md#calls) · [Selection](../stage1a.md#selection) · [Specialization](../stage1b.md#specialization) |
| `E_CAPTURE` | A lambda that uses a binding from outside, and a `value` block or a parameter with the name of a resource binding | [Lambdas and their names](../stage1b.md#lambdas-and-their-names) · [Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls) |
| `E_STATIC_CALL` | A function value without one target that the compiler knows, such as an `if` whose branches name different functions | [Static targets](../stage1b.md#static-targets) |

### Geometric types

| Code | Reports | Rules |
| --- | --- | --- |
| `E_ENDPOINT` | An operand whose objects, or whose family, differ from those that the operation requires | [Operations](../language/geometric-types.md#operations) · [Calls of primitives](../indexed-source.md#calls-of-primitives) · [Operand checks](../affine-geometry.md#operand-checks) of presented affine declarations · [Operand checks](../language/smooth-declarations.md#operand-checks) of smooth declarations |
| `E_ESCAPE` | A value whose type names a local object and that leaves the scope of the object | [Existential packages](../language/geometric-types.md#existential-packages) |
| `E_BASE` | A setting and a coefficient base that do not belong together | [Settings and markers](../language/geometric-types.md#settings-and-markers) |
| `E_RING` | `Affine` or `Base` without a coefficient marker, or with another first argument than `QQ` and `CInfReal` | [Settings and markers](../language/geometric-types.md#settings-and-markers) |

### Generics, abstract types and edit authority

| Code | Reports | Rules |
| --- | --- | --- |
| `E_DISPATCH_DOMAIN` | A domain that is not valid, and a call at a key outside the domain | [Generic declarations](../stage1a.md#generic-declarations) · [Selection](../stage1a.md#selection) |
| `E_DISPATCH_COVERAGE` | A key of the domain at which no method applies | [Selection](../stage1a.md#selection) |
| `E_DISPATCH_AMBIGUOUS` | A key at which no method is more specific than every other method that applies | [Selection](../stage1a.md#selection) |
| `E_CAPABILITY` | A capability that the language does not have, and a method that applies to no key | [Method declarations](../stage1a.md#method-declarations) |
| `E_HIERARCHY` | An abstract type or a `subtype` that its rules do not admit, such as a cycle of parents | [Abstract types](../stage1a.md#abstract-types) |
| `E_CONTRACT_DOMAIN`, `E_CONTRACT_EMPTY`, `E_CONTRACT_RESULT` | An abstract method with a key that does not satisfy its selectors and requirements, with a key that stands for no key of scalar types, or with a key at which the selected method has another result type | [Abstract methods](../stage1a.md#abstract-methods) |
| `E_OWNER` | A declaration that only the owner of a generic or of an abstract type may make, in another module: a method, a grant, a transfer or a `subtype` | [Owners](../language/edit-authority.md#owners) · [Grants and delegations](../language/edit-authority.md#grants-and-delegations) · [Abstract types](../stage1a.md#abstract-types) |
| `E_BORROW` | An event of an assembly that uses a loan against its rules: a second loan of a generic, a loan that is not active, or a loan that the assembly does not return | [Assemblies](../language/edit-authority.md#assemblies) · [Transfers](../language/edit-authority.md#transfers) |
| `E_ASSEMBLY` | An assembly in another module than the root module of the root package, an empty contribution, an event on a sealed generic, and a generic that the assembly edits or transfers without sealing it | [Assemblies](../language/edit-authority.md#assemblies) · [Contributions](../language/edit-authority.md#contributions) |
| `E_IMPACT` | A method of a contribution that wins at a key outside the region of its grant | [Sealing](../language/edit-authority.md#sealing) |
| `E_PROVENANCE` | A contribution that the assembly applies twice with different provenance | [Assemblies](../language/edit-authority.md#assemblies) |

### Indexed, presented affine and smooth declarations

The errors of an `indexed` declaration that concern its type have the code
`E_TYPE`. These codes report the other errors of the geometric declarations.

| Code | Reports | Rules |
| --- | --- | --- |
| `E_AFFINE_BASE` | A base, a structure map or a declaration over a base that its rules do not admit: a missing or cyclic base, a base that is no presented object, images of the base coordinates that are missing or repeated, and a projection, a restriction or a Cartesian square that does not fit its objects | [Presented affine objects](../affine-geometry.md#presented-affine-objects) · [Morphisms over a base](../affine-geometry.md#morphisms-over-a-base) · [Fiber products](../affine-geometry.md#fiber-products) · [Cartesian squares](../affine-geometry.md#cartesian-squares) · [Principal opens](../affine-geometry.md#principal-opens) |
| `E_AFFINE_COORDINATE` | A coordinate that an object does not have, a coordinate that repeats, a fraction with the denominator 0, and an image that is missing or repeated | [Presented affine objects](../affine-geometry.md#presented-affine-objects) · [Polynomial expressions](../language/smooth-declarations.md#polynomial-expressions) · [Smooth maps](../language/smooth-declarations.md#smooth-maps) · [Fiber primitives](../language/smooth-declarations.md#fiber-primitives) |
| `E_AFFINE_RELATION` | A morphism that does not respect the relations of its target, and an isomorphism or a Cartesian square whose composites are not the identity | [Morphisms over a base](../affine-geometry.md#morphisms-over-a-base) · [Isomorphisms](../affine-geometry.md#isomorphisms) · [Cartesian squares](../affine-geometry.md#cartesian-squares) |
| <a id="e-smooth"></a>`E_SMOOTH` in declarations | A declaration whose form does not fit its implementation, such as `spec[…]` under a `smooth_affine` implementation or `Affine(n)[…]` under another one. An `Affine(n)[…]` with another number of coordinates than `n` or with a repeated coordinate. A smooth map that does not name two smooth affine objects, or that is no `pullback(…)` and no `identity` of one object | [Smooth affine objects](../language/smooth-declarations.md#smooth-affine-objects) · [Smooth maps](../language/smooth-declarations.md#smooth-maps) · [Smooth map primitives](../language/smooth-declarations.md#smooth-map-primitives) |
| <a id="e-smooth-fibers"></a>`E_SMOOTH` in primitives on tangent or cotangent fibers and tapes | A binding that names a family of the wrong variance, such as a tangent family where `cotangent_pullback` requires a cotangent family, and an object of a binding that is no smooth affine object of the required dimension. An operand of the wrong shape, family or object has the code `E_TYPE` or `E_ENDPOINT` | [Fiber primitives](../language/smooth-declarations.md#fiber-primitives) · [Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives) · [Flat and sharp](../language/smooth-declarations.md#flat-and-sharp) · [Operand checks](../language/smooth-declarations.md#operand-checks) |
| <a id="e-metric"></a>`E_METRIC` | A metric that its rules do not admit: another family than a metric form, an object that is no smooth affine object, a Gram matrix of another size, an entry that is not constant, or a matrix that is not symmetric. Evidence that does not hold, such as `riemannian(g)` for a matrix that is not positive definite. A `flat` or a `sharp` that names no metric, or evidence for another metric | [Metrics](../language/smooth-declarations.md#metrics) · [Metric evidence](../language/smooth-declarations.md#metric-evidence) · [Flat and sharp](../language/smooth-declarations.md#flat-and-sharp) |

The sections of the last column give every rule with its code, including the
rules of these declarations that have the codes `E_TYPE`, `E_PARSE`,
`E_ENDPOINT`, `E_DUPLICATE` and `E_LIMIT`.
[Wire protocols](../protocol.md#protocol-9-smooth-forms) gives the errors of
a request that holds such a declaration (`E_PROTOCOL`).

### Resource functions

[Resource programs](../storage/resource-programs.md) gives the rules of
these codes, and
[Diagnostics of resource programs](../storage/resource-programs.md#diagnostics)
their places and notes. The numerical chapters use the same codes for the
loans and owners of their statements.

| Code | Reports | Rules |
| --- | --- | --- |
| `E_RESOURCE_NAME` | A resource binding that the function does not have at that place, a name that a body uses twice, and an owned result that names no binding | [Resource functions](../storage/resource-programs.md#resource-functions) · [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_TYPE` | An argument, a result, a payload or a view whose element type, size or shape differs from the type that its place requires, and a contract of a parameter that is not valid | [Storage types](../storage/resource-programs.md#storage-types) · [Resource functions](../storage/resource-programs.md#resource-functions) · [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_LAYOUT` | A layout that does not lie inside its allocation, or whose numbers break the rules of layouts | [Storage types](../storage/resource-programs.md#storage-types) |
| `E_RESOURCE_OVERFLOW` | An allocation beyond the largest number of bytes | [Storage types](../storage/resource-programs.md#storage-types) |
| `E_RESOURCE_LOAN` | A statement on a loan that is not live, on a loan with live children, or on an owner with live loans, and a borrowed parameter that the body releases | [Resource statements](../storage/resource-programs.md#resource-statements) · [Resource functions](../storage/resource-programs.md#resource-functions) |
| `E_RESOURCE_ACCESS` | A read through a loan that permits no reading, or a write through a loan that permits no writing | [Resource statements](../storage/resource-programs.md#resource-statements) · [Storage types](../storage/resource-programs.md#storage-types) |
| `E_RESOURCE_ALIAS` | Two live loans whose views may overlap and of which one writes, and an operation whose input and output may overlap | [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_REGION` | A reborrowed view that does not lie inside the view of its parent | [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_BOUNDS` | A cell index outside its view | [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_INIT` | A read of cells that no statement on every path wrote, and a parameter with `initializes` that the body leaves partly unwritten | [Resource statements](../storage/resource-programs.md#resource-statements) · [Storage types](../storage/resource-programs.md#storage-types) |
| `E_RESOURCE_MOVE` | A use of an owner that the body dropped, moved or handed to a call | [Resource statements](../storage/resource-programs.md#resource-statements) |
| `E_RESOURCE_ESCAPE` | An owner or a loan that is live at the end of a body without being an owned result, and an entry point with parameters or owned results | [Resource functions](../storage/resource-programs.md#resource-functions) |
| `E_RESOURCE_JOIN` | Two arms of an `if` that leave different owners or loans live, and an owner that an arm allocates and does not end | [Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls) |
| `E_RESOURCE_VALUE` | A scalar binding, a scalar argument, a result of a call or a condition of a branch whose type does not fit its use | [Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls) |
| `E_RESOURCE_ARITY` | A `call` with another number of arguments or of result bindings than the function has | [Scalar values and calls](../storage/resource-programs.md#scalar-values-and-calls) |
| `E_RESOURCE_RECURSION` | A resource function that calls itself, directly or through other resource functions | [Resource functions](../storage/resource-programs.md#resource-functions) |
| `E_RESOURCE_LIMIT` | A program beyond a limit of resource functions | [Limits](../language/limits.md#kinds-of-limits) · [Appendix D](limits.md#resource-functions) |

### Runtime extents

These codes report rules on runtime extents that the compiler decides.
`E_RUNTIME_EXTENT` and `E_RUNTIME_GUARD` are also codes of
[run-time diagnostics](#native-runtime).

| Code | Reports | Rules |
| --- | --- | --- |
| `E_RUNTIME_EXTENT` | An extent that is no literal and no binding of type `Nat` or `Int` | [Runtime extents](../storage/resource-programs.md#runtime-extents) |
| `E_RUNTIME_GUARD` | A condition on extents in which every extent is a literal and that is false | [Runtime extents](../storage/resource-programs.md#runtime-extents) |
| `E_RUNTIME_TYPE` | A `runtime_` statement that names a static binding or a binding of another role, and a `RuntimeBasis` that names no space | [Runtime extents](../storage/resource-programs.md#runtime-extents) · [Runtime maps](../storage/resource-programs.md#runtime-maps) |
| `E_RUNTIME_SHAPE` | A statement on runtime owners, loans or maps that breaks a rule on owners, loans, access or initialization, and a coefficient of `runtime_gemm` that does not fit | [Runtime extents](../storage/resource-programs.md#runtime-extents) · [Runtime maps](../storage/resource-programs.md#runtime-maps) |
| `E_RUNTIME_BRANCH` | A statement on runtime extents inside an arm of an `if` | [Runtime extents](../storage/resource-programs.md#runtime-extents) |
| `E_RUNTIME_CALL` | A call whose spaces, bases or maps are not those that its parameters relate, a `RuntimeMap` parameter with `initializes` that the body does not write, and a runtime owner that is live at the end of a function | [Runtime extents](../storage/resource-programs.md#runtime-extents) · [Runtime maps](../storage/resource-programs.md#runtime-maps) |
| `E_RUNTIME_COEFFICIENT` | A `coefficient(…)` in `runtime_gemm` | [Runtime maps](../storage/resource-programs.md#runtime-maps) |

### Numerical statements

| Code | Reports | Rules |
| --- | --- | --- |
| `E_NUMERICAL_TYPE` | A space, a basis, a map, a vector or a metric of another kind, scalar or basis than its statement requires | [Numerical maps](../linalg/maps-and-gemm.md) · [Transforms, evaluation and metrics](../linalg/transforms-and-metrics.md) |
| `E_NUMERICAL_PACKAGE` | An owned-map package that its rules do not admit | [Owned-map packages](../linalg/maps-and-gemm.md#owned-map-packages) |
| `E_NUMERICAL_METRIC` | A metric that does not fit the statement that names it: another basis, entries beyond the largest value, or Gram data that the statement does not accept | [Adjoints for diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) · [Pairings](../linalg/transforms-and-metrics.md#pairings) |
| `E_RESOURCE_GEMM` | A matrix product whose views the checker does not admit as inputs and output | [Matrix products](../linalg/maps-and-gemm.md#matrix-products) |
| `E_RESOURCE_COEFFICIENT` | A coefficient of a matrix product that does not fit its mode or its scalar | [Matrix products](../linalg/maps-and-gemm.md#matrix-products) |
| `E_RESOURCE_DIAGONAL` | An operation with a diagonal metric whose views or scratch do not fit | [Pairings](../linalg/transforms-and-metrics.md#pairings) · [Adjoints for diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) |
| `E_NETWORK` | A two-map network whose declarations or ports do not fit its maps | [Two-map networks](../linalg/networks-and-packing.md#two-map-networks) |
| `E_TENSOR` | A tensor, a grouping or a contraction whose axes do not fit its loan or its operands, and a `contract3_cached` with a cache that is no longer valid | [Tensors](../linalg/networks-and-packing.md#tensors) · [Packing and contraction](../linalg/networks-and-packing.md#packing-and-contraction) |
| `E_TENSOR_CACHE` | A first operand of `contract3_cached` that is no cache | [Caches](../linalg/networks-and-packing.md#caches) |
| `E_TENSOR_TREE` | A contraction tree whose graph or plan its rules do not admit, including a tree beyond its limits | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |

### Limits

| Code | Reports | Rules |
| --- | --- | --- |
| `E_LIMIT` | A program beyond a limit of the compiler | [Limits](../language/limits.md) · [Appendix D](limits.md) |

`E_RESOURCE_LIMIT`, `E_RESOURCE_OVERFLOW` and `E_TENSOR_TREE` report the
limits of their constructs, as
[Kinds of limits](../language/limits.md#kinds-of-limits) says.

### Requests and audits

These codes report a request of the
[wire protocol](glossary.md#wire-protocol) that breaks a rule of the
protocol, or a result of the kernel that fails a check that the kernel
repeats. The Reference gives one rule with a code of this section:
[Function types](../language/types.md#function-types) gives `E_PROTOCOL` for
an invalid function type in some programs. No other rule of the Reference
gives one of these codes, as
[Classes of codes](../language/diagnostics.md#classes-of-codes) says.

The tests of the repository reach none of the other codes of this section
from a source program. They reach `E_LITERAL` with a request that they
change, and the regressions of the kernel reach some of the codes with
requests and plans that they build. A diagnostic with a code of the third
table for a source program reports a defect of the compiler.

Codes of a request:

| Code | Reports |
| --- | --- |
| `E_PROTOCOL` | A request that is no request of a version that the kernel speaks: text that is not JSON, a request beyond the bounds of [Wire protocols](../protocol.md), an unknown version, an unknown or a missing field, a form that the version of the request does not have, and an identity, an owner or a certificate that only the kernel may compute |
| `E_ARGUMENT` | A kernel executable that is started with other arguments than `check` or `emit`. The command `vastitas` starts it with one of the two |
| `E_LITERAL` | An integer literal of a request that is no sequence of decimal digits |
| `E_CONTEXT` | A type of a request whose bindings, names or modules are not those of its context |
| `E_SCOPE` | A type or a lambda of a request that names an object or a binding outside its scope |
| `E_STAGE` | A request that joins forms of two versions of the protocol that do not belong together, such as a body of an older form with an `indexed` body |
| `E_RESOURCE_FUNCTION` | A plan of resource functions with a repeated function, without its entry or with a call of a function that it does not hold |

Codes of the storage checker on a plan of storage operations, which the
kernel builds from the resource functions:

| Code | Reports |
| --- | --- |
| `E_RESOURCE_PROVENANCE` | A loan or an argument whose allocation the plan does not hold as live |
| `E_RESOURCE_DEPENDENCY` | A cached value whose loan, allocation or version the plan does not hold as it was |
| `E_RESOURCE_PACK` | A packing or a regrouping whose views do not fit its three axes |
| `E_RUNTIME_ESCAPE` | An entry point whose runtime owners or loans are live at its end |

Codes of a check that the kernel repeats on its own result:

| Code | Reports |
| --- | --- |
| `E_INTERNAL_ASSEMBLY`, `E_INTERNAL_AUTHORITY` | An assembly whose states or steps fail the audit of edit authority |
| `E_INTERNAL_DISPATCH` | A dispatch table or a selection that differs from the methods of the program |
| `E_INTERNAL_FUNCTION` | A specialized instance, a lifted lambda or a static target that fails its audit |
| `E_INTERNAL_GRAPH` | An order of the functions that is no order of their calls |
| `E_INTERNAL_NAMESPACE` | Names or references that fail the audit of name resolution |
| `E_INTERNAL_REVERSE` | A compiled reverse pass that fails the audit of [Core](glossary.md#core) |
| `E_INTERNAL_TYPE` | A Core module that fails the second check of its types |
| `E_DEPENDENCY` | A Core module whose functions do not stand after the functions that they call |
| `E_CODEGEN` | A Core module that the generator of pure code rejects |
| `E_RESOURCE_CODEGEN`, `E_RUNTIME_CODEGEN` | A storage plan that the generator of storage code rejects |
| `E_RESOURCE_STATE` | A state of the storage checker that fails its audit, and a call whose expansion differs from its second run |
| `E_NUMERICAL_ORIGIN` | Numerical instructions that differ from the statements that they come from |
| `E_RUNTIME_NUMERICAL`, `E_RUNTIME_RETURN` | A statement on runtime extents whose record differs from the checked plan |
| `E_DISPATCH_HIERARCHY` | A hierarchy of nominal types that the dispatch engine does not accept. The kernel rejects such a hierarchy first (`E_HIERARCHY`) |

[Verification boundaries](../verification.md) describes the checks that the
kernel repeats, and [Wire protocols](../protocol.md) the rules of a request.

> **Implementation note.** The dispatch engine of the kernel names its errors
> with codes of its own, which no diagnostic shows. The kernel reports
> `E_DISPATCH_ARITY` as `E_ARITY`, `E_DISPATCH_SELECTOR` as `E_TYPE`,
> `E_DISPATCH_CAPABILITY` and `E_DISPATCH_UNREALIZABLE` as `E_CAPABILITY`,
> `E_DISPATCH_DUPLICATE` and `E_DISPATCH_DUPLICATE_ID` as `E_DUPLICATE`, and
> `E_DISPATCH_LIMIT` as `E_LIMIT`.
>
> The sources of the kernel name two further codes that no command
> reports. `E_SCALAR_PROFILE` stands in a module that only the proofs
> import, and `E_INDEX` in a checker of scalar programs that no route of
> the kernel executable calls.

## Native runtime

An executable checks conditions on its allocations, views and sizes before it
writes, as [Run-time checks](../language/guarantees.md#run-time-checks) says.
A check that fails stops the executable with a run-time diagnostic.
[Running a resource program](../storage/resource-programs.md#running-a-resource-program)
gives the rules, and
[Run-time diagnostics](../language/diagnostics.md#run-time-diagnostics) the
form of the line.

The storage runtime, in
[`lean-kernel/native/storage.c`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/native/storage.c),
reports these codes with these messages. The numerical runtime reports its
errors with the same codes.

| Code | Message | Reports |
| --- | --- | --- |
| `E_NATIVE_ALLOCATION` | allocation or live-byte budget failed | The system gives no memory for an allocation, or the live bytes of the executable exceed the largest number |
| `E_NATIVE_HANDLE` | allocation is absent, closed or already issued | An operation names an allocation that the executable does not hold |
| `E_NATIVE_SCALAR` | scalar representation mismatch | The element type of an operation differs from that of its allocation |
| `E_NATIVE_LAYOUT` | invalid layout, bounds, alignment or narrowing | A view does not lie inside its allocation, or its numbers do not fit the native sizes |
| `E_NATIVE_OVERFLOW` | native size or accounting overflow | A size does not fit the native integers |
| `E_NATIVE_BOUNDS` | cell index is outside the view | A cell index lies outside its view |
| `E_NATIVE_ALIAS` | accessed regions may overlap | The input and the output of an operation may overlap |
| `E_NATIVE_EXPECT` | stored bit pattern differs | A cell does not hold the payload of an `expect` or `runtime_expect` statement |
| `E_NATIVE_ABI` | unsupported numerical backend version, ABI or threading | The OpenBLAS library is no sequential LP64 build of the pinned version |
| `E_NATIVE_SHAPE` | numerical operand dimensions differ | The views of a matrix product or of a pairing do not fit each other |
| `E_NATIVE_OPERATION` | unsupported numerical operation or layout | A numerical operation has a view or a mode that the runtime does not support |
| `E_NATIVE_STATUS` | unknown status | The runtime returns a status that it does not define |

The message of a failed `expect` continues with the cell and both payloads:
`E_NATIVE_EXPECT: stored bit pattern differs at cell (ROW, COLUMN): holds …; expected …`.

A generated program reports two further codes for runtime extents:

| Code | Message | Reports |
| --- | --- | --- |
| `E_RUNTIME_EXTENT` | extent is negative | An extent that the program computes is a negative `Int` |
| `E_RUNTIME_EXTENT` | extent exceeds signed native size range | An extent is greater than 2⁶³ − 1 |
| `E_RUNTIME_GUARD` | extent, layout or shape preflight failed | A condition on runtime extents, layouts, cells or shapes that the compiler could not decide is false |

The checker rejects a program whose checks it can decide, so an executable of
an accepted program reports a code of the first table only for a condition
that depends on the machine or on the values of the run. Examples are a
failed allocation, a failed `expect` and an OpenBLAS library of another
build. [Resource checking](../internals/resource-checking.md#runtime-extent-proof-boundary)
states what is Proved about the conditions on runtime extents. No theorem
covers the C code of the runtime.

## Reference models

Two [reference models](reference-models.md) study diagnostics outside the
compiler: a
[diagnostic record](../reference/compiler-tools.md#diagnostic-reference) with
related places and corrections, and a
[contract for doctests](../reference/compiler-tools.md#doctest-result-reference)
that expect a rejection. They define no code of this appendix.

## Moved sections

These anchors keep older links working.

- <a id="output-format"></a>Output format: [Diagnostic lines](../language/diagnostics.md#diagnostic-lines), [Places](../language/diagnostics.md#places), [Names and text in diagnostics](../language/diagnostics.md#names-and-text-in-diagnostics), [Exit status](../language/diagnostics.md#exit-status) and [Run-time diagnostics](../language/diagnostics.md#run-time-diagnostics).
- <a id="development-references"></a>Development references: [Reference models](#reference-models).
