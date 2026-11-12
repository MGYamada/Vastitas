# Appendix D: Compiler limits

This appendix lists the [limits](glossary.md#limit) of the compiler with their
values. [Limits](../language/limits.md) gives the rules that hold for every
limit and names the kinds of limits. The chapter of a construct gives the
rules of the construct, and it states a limit that a program meets in
ordinary use.

## How to read the tables

Each table has these columns:

| Column | Content |
| --- | --- |
| Limit | The name of the limit. A name in code font is a key of the file that [Sources of the values](#sources-of-the-values) names |
| Value | The largest value that the compiler accepts. A program with 4096 of the things that a limit of 4096 counts is within the limit, and a program with 4097 is beyond it |
| Counts | What the limit counts |
| Holds for | The part of a program that has one count, such as a program, a generic or a function |
| Code | The code of the error for a program beyond the limit |

A limit that holds for a program counts the packages, modules and functions
of the program together. A table without the column "Code" has one code,
which the text above the table gives. Where a section gives a boundary in a
sentence, such as "a body of 2048 such statements is within the limit", the
compiler accepts a program at that boundary and rejects the next one.

### Sources of the values

> **Implementation note.** The values with a key come from the file
> [`lean-kernel/compiler-limits.json`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/compiler-limits.json).
> The frontend and the kernel read it when they are built. The file belongs
> to the build identity of the kernel, so the compiler rejects a kernel that
> was built with other values, as
> [Appendix A](../guide/cli.md#the-kernel-and-its-build-identity) describes.
> Two limits with equal values stay two limits. The values without a key are
> constants of the frontend, in `src/`, or of the kernel, in
> `lean-kernel/VastitasKernel/`.

## Source text

The frontend decides these limits when it parses a file.
[Expressions](../language/expressions.md) gives the syntax that they measure.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `parseNesting` | 64 | The levels of nested expressions and types on one path through the source. An expression or a type is one level, and each pair of parentheses, block, argument or type argument around it adds a level. The arms of the branches of a resource function share the count | An expression or a type | `E_LIMIT` |
| Conditions of an `if` chain | 62 | The conditions of a chain of `if` and `else if` that is the whole body of a function and whose conditions are single comparisons. Each condition takes one level of `parseNesting`, and the condition and the result of each arm take further levels. A chain inside another expression admits fewer conditions | An expression | `E_LIMIT` |
| `astDepth` | 128 | The depth of the syntax tree of an expression. In a chain of one left-associated operator, each operand adds a level | An expression | `E_LIMIT` |

An expression inside 63 pairs of parentheses is within `parseNesting`, and
`1 + 1 + … + 1` with 128 operands is within `astDepth`.
[Exact affine algebra](#exact-affine-algebra) gives the limit on the levels of
a polynomial expression.

## Inputs

The frontend decides these limits while it reads the files of a program.
A diagnostic for one of the first four has no
[place](../language/diagnostics.md#diagnostics-without-a-place-of-their-own).

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| One input file | 16 MiB | The bytes of one manifest or source file | A file | `E_LIMIT` |
| All inputs | 64 MiB | The bytes of all manifests and source files that the compiler reads. A file that serves several modules counts once for each | A program | `E_LIMIT` |
| Loaded files | 8192 | The manifests and source files that the compiler reads. A file that serves several modules counts once for each | A program | `E_LIMIT` |
| Modules | 4096 | The modules of all packages of a program in [manifest mode](../language/programs.md#manifest-mode): each root module, each module with a file of its own and each inline module | A program | `E_LIMIT` |
| `moduleNesting` | 64 | The modules around a module, below the root module of its package. It is the number of components of the path of the module in its package | A module | `E_LIMIT` |
| `packageNesting` | 64 | The packages on one chain of dependencies, with the root package | A program | `E_LIMIT` |

A mebibyte, MiB, is 1,048,576 bytes. A root module with 4095 further modules
is within the limit on modules. A package that two packages depend on is read
once. [Modules](../language/modules.md) and
[The package graph](../packages.md#the-package-graph) give the rules of
modules and of dependencies.

## Functions

The kernel decides these limits when it checks the bodies of functions,
methods and lambdas. [Specialization](../stage1b.md#specialization) defines
the specialized instances.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `bodyChecking` | 4096 | The units of one path of the checker through a body. Each level of a nested expression takes a unit. So does each statement that stands before a statement in its block, and each argument that stands before an argument in a call of a function. The operands of an operator, the branches of an `if` and the fields of a `pack` are separate paths, and each starts with the units that remain | The body of a function, of a method or of a lambda, in each specialized instance | `E_LIMIT` |
| `generatedLets` | 4096 | The bindings that the compiler generates for a body, in all its branches and nested expressions together | The body of a function, of a method or of a lambda, in each specialized instance | `E_LIMIT` |
| `specializations` | 4096 | The specialized instances. Each lambda is one. Each higher-order function is one for its check on its own and one more for each combination of function values that the program passes to it. Lambdas and instances of higher-order functions count together | A program | `E_LIMIT` |
| `elaborationWork` | 1,000,000 | The units of the bodies that the checker elaborates: one for each function and for each of its parameters, and one for each block, statement and expression of its body. A method counts at each key at which it applies, and a lambda or a higher-order function for each specialized instance. A `value` block of a resource function counts with the scalar bindings that it sees as its parameters | A program | `E_LIMIT` |

The compiler generates these bindings for a body:

- one for each `let` statement;
- two for each `unpack` statement and one more for each of its fields, so
  three for `unpack p as { scheme: X, point: x };`;
- one for each argument of a call of a function, of a generic or of a
  function value;
- one more for a call whose callee is an expression other than a name, such
  as a lambda that the program calls where it stands.

A call of a built-in function such as `int` or `pair`, or of a primitive,
generates no binding for its arguments. A `let` statement whose value is a
call with one argument therefore counts two. A body of 2048 such statements
is within `generatedLets`, and a body of 2049 is beyond it. A body of 1364
`unpack` statements of the three-binding form and four `let` statements
whose values generate no binding is at the limit: 1364 × 3 + 4 = 4096.

The path of `bodyChecking` through a body that is a list of statements grows
with each statement. A body of 4093 `let` statements with literal values and
a result is within the limit, and one more statement is beyond it.

`check` and `build` apply the same limits. The compilation of reverse passes
also measures `generatedLets`, without rejecting a program, as
[Bounds that reject nothing](#bounds-that-reject-nothing) describes.
[Function specialization](../internals/checking-pipeline.md#function-specialization)
describes how the checker counts instances and units of work.

## Generics and abstract types

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `dispatchArity` | 6 | The parameters of a generic | A generic | `E_LIMIT` |
| `dispatchKeys` | 4096 | The keys of a generic: 4ⁿ keys for `n` parameters. Six parameters give 4096 keys, so the two limits agree | A generic | `E_LIMIT` |
| `dispatchWork` | 16,000,000 | The units of work of building the dispatch table of a generic. The checker computes the work from the keys and the methods before it builds the table | A generic | `E_LIMIT` |
| `nominalTypes` | 64 | The nominal types of a program: its abstract types and the six built-in types `Nat`, `Int`, `Bool`, `Unit`, `Number` and `Any`. A program has at most 58 abstract types | A program | `E_LIMIT` |

[Generic declarations](../stage1a.md#generic-declarations),
[Selection](../stage1a.md#selection) and
[Abstract types](../stage1a.md#abstract-types) state the rules.

## Names

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `namespaceResolution` | 4096 | The steps of resolving one path through modules, imports and reexports | A path | `E_LIMIT` |
| `namespaceImportWork` | 1,000,000 | The members that the checker visits when it checks the `use` declarations | A program | `E_LIMIT` |
| `namespaceProgramWork` | 4,000,000 | The units of work of the names of the whole program: the size of the request that the frontend writes, and the lookups of names in all bodies | A program | `E_LIMIT` |

The diagnostic for `namespaceProgramWork` has the place `FILE:1:1`.
[Resolution](../language/names-and-paths.md#resolution) states the rule.

## Edit authority

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `assemblyEvents` | 4096 | The events of the assembly | A program | `E_LIMIT` |
| `contributionMethods` | 4096 | The methods of all contributions of the package graph | A program | `E_LIMIT` |
| `dispatchKeys` | 4096 | The keys that the `domain` of a grant lists. A generic has at most this many keys, so only a list with a repeated key is longer | A grant | `E_LIMIT` |
| `authorityTraceWork` | 200,000,000 | The units of work of the audit of the assembly. The checker computes the units of each event from the live loans, the applied contributions and the declarations before it audits the event. All events share the budget | A program | `E_LIMIT` |

[Assemblies](../language/edit-authority.md#assemblies) states the rules.

## Indexed declarations

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| Indexed declarations | 4096 | The `indexed` declarations of all packages | A program | `E_LIMIT` |
| Implementations of a classification | 64 | The implementations in the `domain` of a classification | A classification | `E_TYPE` |
| Parameters of a family | 16 | The parameters of an `indexed family` | A family | `E_TYPE` |
| Cases of a package declaration | 64 | The cases of an `indexed package` | A package declaration | `E_TYPE` |
| Fields of a case | 64 | The fields of one case of an `indexed package` | A case | `E_TYPE` |
| Position in a constraint | 2³² − 1 | The integer that names a parameter in a constraint of a family, such as the `1` of `same_base(0, 1)` | A constraint | `E_LIMIT` |

The diagnostic for the number of indexed declarations has the place
`FILE:1:1`. A position in a constraint must also name a parameter of the
family, which [Families](../indexed-source.md#families) requires; the limit
bounds the integer that the frontend reads.
[Indexed declarations](../indexed-source.md) states the rules.

<a id="exact-affine-algebra-stage-2"></a>

## Exact affine algebra

The kernel checks [presented affine declarations](../affine-geometry.md) by
arithmetic of polynomials with rational coefficients. It bounds a polynomial
expression of the source before it expands the expression. Every substitution
of a check runs within `algebraWork` and `algebraTerms`: a structure map, a
pullback, a base chain, a base isomorphism and the composites of an
isomorphism or of a Cartesian square. A declaration beyond a limit of this
section is an error (`E_LIMIT`).
[Limits](../affine-geometry.md#limits) of that chapter states the rules.

| Limit | Value | Counts | Holds for |
| --- | --- | --- | --- |
| `algebraGenerators` | 16 | The coordinates of a presented affine object. A fiber product counts the coordinates of both factors | An object |
| `algebraRelations` | 32 | The relations of a presented affine object | An object |
| `algebraChain` | 16 | The objects of a base chain, with the object that declares the chain | An object |
| `algebraDegree` | 16 | The degree of a polynomial expression and each of its exponents | A polynomial expression |
| `algebraCoefficientDigits` | 64 | The decimal digits of a literal of a polynomial expression | A literal |
| `algebraNesting` | 64 | The levels of a polynomial expression, as [Polynomial expressions](../language/smooth-declarations.md#polynomial-expressions) counts them. Parentheses and unary `-` signs nest at most 63 deep | A polynomial expression |
| `algebraTerms` | 512 | The terms of each polynomial that a check produces, including each intermediate product | A polynomial |
| `algebraBasis` | 64 | The elements of the basis that the kernel computes for the relations of an object | An object |
| `algebraWork` | 8,000,000 | The units of work of one run of the arithmetic: the computation and the verification of a basis, or one substitution | A run |

### Smooth objects and maps

[Smooth affine declarations](../language/smooth-declarations.md) have the
limits of exact affine algebra. The kernel elaborates each image of a smooth
map within one run of `algebraWork`. A declaration beyond a limit is an error
(`E_LIMIT`).

| Limit | Value | Counts | Holds for |
| --- | --- | --- | --- |
| `algebraGenerators` | 16 | The coordinates of a smooth affine object, and so the dimension of every smooth map, tangent or cotangent fiber, tape and Gram matrix | An object |
| `algebraCoefficientDigits` | 64 | The digits of the dimension in `Affine(n)`, and of a literal in an image or in a Gram entry | A literal |
| `algebraDegree` | 16 | The degree and the exponents of an image or of a Gram entry | A polynomial expression |
| `algebraNesting` | 64 | The levels of an image or of a Gram entry | A polynomial expression |
| `algebraTerms` | 512 | The terms of each expanded image or Gram entry | A polynomial |
| `algebraWork` | 8,000,000 | The units of work of elaborating one image, or all Gram entries of one metric | A run |

These limits hold when the compiler checks a program. In an executable,
`same` and `composite` expand a composite map without a budget, and the
reverse pass has no bound on its work. The length of a chain of `compose`
nodes has no bound, and neither have the exponents and the number of terms of
a composite. The runtime runs all three in loops, so they use time and
memory and no native stack
([#630](https://github.com/MGYamada/Vastitas/issues/630)).
[Stack-safe runtime code](../verification.md#stack-safe-runtime-code) gives
the evidence.

## Smooth metrics

The kernel evaluates all Gram entries of one metric within one run of
`algebraWork`. It then bounds the size of each entry and the size of the
whole matrix. A larger entry or matrix is an error (`E_LIMIT`). The kernel
checks both bounds when it elaborates the metric, before it computes a
certificate for any
[metric evidence](../language/smooth-declarations.md#metric-evidence), and
even when no evidence names the metric.
[Metrics](../language/smooth-declarations.md#metrics) states the rule.

| Limit | Value | Counts | Holds for |
| --- | --- | --- | --- |
| `metricEntryBits` | 512 | The bits of the numerator and of the denominator of one elaborated Gram entry | A Gram entry |
| `metricMatrixBits` | 16,384 | The bits of the [matrix bound](glossary.md#matrix-bound) ‖A₁‖ ⋯ ‖Aₙ‖ · max Dᵢ of one Gram matrix | A metric |

In the matrix bound, Dᵢ is the least common denominator of row i of the Gram
matrix, and Aᵢ is row i times Dᵢ, a row of integers. ‖Aᵢ‖ is its Euclidean
norm, and a zero row counts as 1.

The entry bound does not limit the work of the inverse, of the `L D Lᵀ`
factorization or of their checks. The entries of the inverse grow with the
least common denominators of the rows: a 16 × 16 matrix whose entries have
pairwise distinct 400-bit denominators has an inverse with entries of about
100,000 bits. The matrix bound limits that work. By Hadamard's inequality,
the numerator and the denominator of every entry of the inverse, and of every
entry of L, D and L⁻¹, have at most `metricMatrixBits` bits. With at most
`algebraGenerators` coordinates, this bounds the work of a certificate and of
its check. Every Gram matrix with integer entries and every diagonal Gram
matrix within the entry bound is within the matrix bound.

## Resource functions

[Resource programs](../storage/resource-programs.md) gives the rules of
resource functions. Most limits of this section have the code
`E_RESOURCE_LIMIT`, and four have another code.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `value` blocks | 4096 | The `value` blocks of all resource functions: each `value` statement and the block that ends each function. Each resource function ends with one, so a program has at most 4096 resource functions | A program | `E_RESOURCE_LIMIT` |
| Statements | 4096 | The statements of all resource functions, with the statements of both arms of each `if` and the steps of each plan of a contraction tree. The `value` block that ends a function is no statement | A program | `E_RESOURCE_LIMIT` |
| Steps of one function | 4096 | The steps of the body of one resource function before the checker expands its calls: one for the function, one for each statement, and one more for each `allocate`, `borrow`, `release`, `drop` and `fill` statement and for each of their `runtime_` forms | A resource function | `E_RESOURCE_LIMIT` |
| Parameters and owned results | 64 each | The parameters of a resource function, and its owned results | A resource function | `E_RESOURCE_LIMIT` |
| Arguments and results of a call | 64 each | The arguments of a `call` statement, and the bindings that take its owned results | A call | `E_RESOURCE_LIMIT` |
| Views of a contract | 64 | The layouts of one `initialized […]` contract | An owned parameter or result | `E_RESOURCE_TYPE` |
| Expansion of calls | 4096 | The units of work of one expansion. The checker expands the calls of each resource function once for the check of the function on its own, and those of the entry point once more. Each function that a call enters takes a unit, and each statement that the expansion reaches takes at least one | An expansion | `E_RESOURCE_LIMIT` |
| Depth of calls | 4096 | The units of one chain of calls. A call takes two units, and each statement that stands before the call in its function takes one | A chain of calls | `E_RESOURCE_LIMIT` |
| `resourceWork` | 32,000,000 | The weighted units of work of checking all resource functions: the check of each function on its own and the check of the entry point | A program | `E_LIMIT` |
| Storage plan | 4096 | The operations of the entry point after the expansion of its calls, with both arms of each branch, and the length of one path of the checker through them | A program | `E_RESOURCE_LIMIT` |
| Initialization records | 4096 | The records that the checker keeps of the writes to one allocation, at a join of two arms | An allocation | `E_RESOURCE_LIMIT` |
| Integers | 2⁶⁴ − 1 | An integer of a storage type, of a layout, of an allocation size, of a cell index or of `f64_bits` | An integer | `E_RESOURCE_LIMIT` |
| Bytes of an allocation | 2⁶³ − 1 | The cells of an allocation times the size of a cell, 8 bytes for `F64` and 16 for `Complex<F64>` | An allocation | `E_RESOURCE_OVERFLOW` |
| Rows, columns and leading of a layout | 2³¹ − 1 | The three numbers of a `layout` | A layout | `E_RESOURCE_LAYOUT` |

A resource function with 2046 `allocate` and `drop` statements has 4093
steps and is within the limit on the steps of one function. A chain of
resource functions in which each function only calls the next holds at most
2048 functions, and a chain of 2049 is beyond the depth of calls. Where the
functions of a chain hold other statements, the chain is shorter, and the
expansion of calls can reach its limit first.

The checker also bounds its search of the records of one allocation when it
decides whether the cells of a view are initialized. A view whose cells the
search does not find initialized is an error (`E_RESOURCE_INIT`), as
[Resource statements](../storage/resource-programs.md#resource-statements)
says. [Checked storage](../storage/checked-storage.md#storage-ir) describes
the storage plan and these records, and
[Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work)
the units of `resourceWork`.

## Numerical statements

The numerical chapters state these limits with their rules.

| Limit | Value | Counts | Holds for | Code | Rule |
| --- | --- | --- | --- | --- | --- |
| Dimension of a static space | 2⁶⁴ − 1 | The integer literal of `linear(P, n)` | A space | `E_RESOURCE_LIMIT` | [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) |
| Bytes of a static space | 2⁶³ − 1 | The dimension times the size of a cell | A space | `E_NUMERICAL_TYPE` | [Spaces and bases](../linalg/maps-and-gemm.md#spaces-and-bases) |
| Dimension of an axis of a tensor | 2³¹ − 1 | The dimension of the space of one axis | A tensor | `E_TENSOR` | [Tensors](../linalg/networks-and-packing.md#tensors) |
| Entries of a `diagonal` metric | 4096 | The entries that `diagonal` lists | A metric | `E_LIMIT` | [Metrics](../linalg/transforms-and-metrics.md#metrics) |
| Absolute value of a metric entry | 2⁵³ | Each entry of a metric that `adjoint_into` or `hermitian_diagonal` uses | A metric | `E_NUMERICAL_METRIC` | [Adjoints for diagonal metrics](../linalg/transforms-and-metrics.md#adjoints-for-diagonal-metrics) · [Pairings](../linalg/transforms-and-metrics.md#pairings) |
| Occurrences of a contraction tree | 64 | The `occurrence` declarations of one graph | A contraction tree | `E_TENSOR_TREE` | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |
| Declarations of a contraction tree | 128 | The declarations of one graph before `plan` | A contraction tree | `E_TENSOR_TREE` | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |
| Steps of a plan | 1024 | The steps of the `plan` of one contraction tree | A contraction tree | `E_TENSOR_TREE` | [Contraction trees](../linalg/networks-and-packing.md#contraction-trees) |

A view has at most 2³¹ − 1 rows and columns, by the limit on layouts of
[Resource functions](#resource-functions). The steps of a plan also count
against the statements of the resource functions.

## Limits that a source program does not reach

The kernel checks a request of the
[wire protocol](glossary.md#wire-protocol) without trusting the frontend, so
it has limits of its own on the request. The limits of
[Source text](#source-text), of [Inputs](#inputs) and of
[Resource functions](#resource-functions) bound a source program first: the
frontend reports one of them, and no source program is known to reach a limit
of this table. A request beyond one is an error with the code of the last
column.

| Limit | Value | Counts | Code |
| --- | --- | --- | --- |
| `typeNesting` | 64 | The nesting of a function type. The parser reads a type of 63 levels and reports `parseNesting` for the next | `E_LIMIT`, or `E_PROTOCOL` in the decoder of the request |
| Size of a request | 1024 MiB, 16,384 levels, 64 digits | The bytes of a request, the nesting of its arrays and objects, and the digits of one of its numbers, as [Wire protocols](../protocol.md#protocol-selection) says | `E_PROTOCOL` |
| `sourceNesting` | 512 | The steps of the recursion that decodes a body of the request and prepares it for checking | `E_LIMIT`, or `E_PROTOCOL` in the decoder of the request |
| `namespaceNesting` | 1024 | The recursion of the checker of names through a body | `E_LIMIT` |
| `dependencyGraph` | 4096 | The units of walking the graph of package dependencies | `E_LIMIT` |
| Resource functions | 4096 | The resource functions of a request. The limit on `value` blocks bounds a source program | `E_RESOURCE_LIMIT` |
| Requests of the specialization worklist | 2,000,001 | The requests for instances that one pass of the function checker handles, or a bound from the number of functions when that is smaller. `specializations` and `elaborationWork` bound a program first | `E_LIMIT` |

## Bounds that reject nothing

These bounds change what the compiler does for a program and reject no
program, as [Limits](../language/limits.md#bounds-that-reject-nothing) says.

| Bound | Value | What it bounds |
| --- | --- | --- |
| `generatedLets` | 4096 | The bindings of a function after the compilation of its reverse passes |
| Declaration ids of a Core module | 4096 | The declarations that the compiled reverse passes add to a module |
| `reverseLeaves` | 256 | The maps of one reverse pass that the compilation reads through `let` statements and `compose` |
| Notes of a resource diagnostic | 32 | The notes that follow one diagnostic of a resource program |
| Search for an uninitialized cell | 131,072 | The records that the checker visits to find the cell that a diagnostic names |
| `captureDiagnostic` | 8192 | The steps of the search for the place of a capture in the request of a flat program. The frontend reports a capture of a source program itself (`E_CAPTURE`) |
| Lean options of a generated program | `maxRecDepth` 32768, `maxHeartbeats` 2000000 | The elaboration of the generated program by Lean in `build` |

The compilation of reverse passes into [Core](glossary.md#core) compiles less
of a program at a bound and rejects nothing:

- A function whose compiled Core would exceed `generatedLets` keeps every one
  of its reverse sites as a call of the
  [runtime reverse pass](glossary.md#runtime-reverse-pass).
- A reverse site keeps that call too when its declarations would exceed the
  declaration ids of a Core module.
- The reading of the maps of a site charges at most `reverseLeaves` maps. A
  `let`-bound map whose recorded maps exceed the remaining budget is one
  [opaque step](glossary.md#opaque-step).
- Below as many levels as there are `let` statements in scope, plus 64, the
  rest of a map is one opaque step. A `let` that is nested deeper than its
  own reading reaches is one opaque step wherever the compilation reads it.
- A map operand whose own `compose` calls exceed the budget is one opaque
  step as a whole, so the compilation compiles none of its maps.

[Reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives)
gives the rules of reverse passes, and
[Diagnostics of resource programs](../storage/resource-programs.md#diagnostics)
those of the notes and of the cell that a diagnostic names. A build that the
Lean options stop is an error of the build (`E_BUILD`), not of the program.

## What the limits do not bound

The limits count units of work and of size. They do not count time, bytes of
memory or native instructions, and the time of a check has no bound of its
own. [What has no limit](../language/limits.md#what-has-no-limit) and
[Limits at run time](../language/limits.md#limits-at-run-time) give the
rules, and
[Execution costs and limits](../internals/resource-checking.md#execution-costs-and-limits)
describes the costs of an executable with runtime extents.
[Appendix A](../guide/cli.md#output-of-the-tools) gives the bounds of the
compiler on the output of the programs that it starts.

## Moved sections

These anchors keep older links working.

- <a id="checker-limits"></a>Checker limits: [Functions](#functions), [Generics and abstract types](#generics-and-abstract-types), [Names](#names), [Edit authority](#edit-authority), [Inputs](#inputs) and [Limits that a source program does not reach](#limits-that-a-source-program-does-not-reach).
- <a id="parser-and-checker-budgets"></a>Parser and checker budgets: [Source text](#source-text) and [Functions](#functions).
- <a id="input-limits"></a>Input limits: [Inputs](#inputs).
- <a id="other-documented-bounds"></a>Other documented bounds: [Indexed declarations](#indexed-declarations), [Resource functions](#resource-functions), [Numerical statements](#numerical-statements) and [Bounds that reject nothing](#bounds-that-reject-nothing).
