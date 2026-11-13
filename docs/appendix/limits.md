# Appendix D: Compiler limits

This appendix lists the [limits](glossary.md#limit) of the compiler with their
values. [Limits](../language/limits.md) gives the rules that hold for every
limit and names the kinds of limits. The chapter of a construct gives the
rules of the construct, and it states a limit that a program meets in
ordinary use.

## How to read the tables

Most tables have these columns:

| Column | Content |
| --- | --- |
| Limit | The name of the limit. A name in code font is a key of the file that [Sources of the values](#sources-of-the-values) names |
| Value | The largest value that the compiler accepts. A program with 4096 of the things that a limit of 4096 counts is within the limit, and a program with 4097 is beyond it |
| Counts | What the limit counts |
| Holds for | The part of a program that has one count, such as a program, a generic or a function |
| Code | The code of the error for a program beyond the limit |

A limit that holds for a program counts the packages, modules and functions
of the program together. The tables of
[Exact affine algebra](#exact-affine-algebra) and of
[Smooth metrics](#smooth-metrics) have no column "Code": every limit there
has the one code that the text above the table gives. The table of
[Numerical statements](#numerical-statements) adds a column for the rule of
each limit. The tables of the last three sections of limits have no column
"Holds for", because they list bounds on a request, bounds that reject
nothing and bounds of the native runtime.

Where a section gives a boundary in a sentence, such as "a body of 2048 such
statements is within the limit", the compiler accepts a program at that
boundary and rejects the next one. A diagnostic with the place `FILE:1:1`
names the first input of the program: the entry file in flat mode and the
root manifest in manifest mode, as
[Diagnostics without a place of their own](../language/diagnostics.md#diagnostics-without-a-place-of-their-own)
says.

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
A diagnostic for one of them has no
[place](../language/diagnostics.md#diagnostics-without-a-place-of-their-own).
The one exception is `moduleNesting` for an inline module, whose diagnostic
has the place of the module.

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

## Request

The frontend writes a program as one request of the
[wire protocol](glossary.md#wire-protocol), and the kernel reads it.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `requestBytes` | 1,073,741,824 | The bytes of the request that the frontend writes for the program | A program | `E_LIMIT` |

The value is 1024 MiB. The frontend counts the bytes of the request while it
writes it and stops at the limit, so it rejects a larger request before the
kernel runs.
[Diagnostics without a place of their own](../language/diagnostics.md#diagnostics-without-a-place-of-their-own)
gives the place of its diagnostic. A program within the limits of
[Inputs](#inputs) can be beyond this one, because the request
holds a record with a place for every expression. A source file of
11,926,914 bytes that holds 47,000 `let` statements of 120 operands each
makes a request of 1,136,761,778 bytes.

The kernel has the same bound on a request that it reads, and it refuses a
larger one without parsing it (`E_PROTOCOL`). A request of the frontend does
not reach it.
[Limits that a source program does not reach](#limits-that-a-source-program-does-not-reach)
gives the other bounds of a request.

## Functions

The kernel decides these limits when it checks the bodies of functions,
methods and lambdas. [Specialization](../stage1b.md#specialization) defines
the specialized instances.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `bodyChecking` | 4096 | The units of the longest path of the checker through a body. The second list below the table says which units a path takes | The body of a function, of a method or of a lambda, in each specialized instance | `E_LIMIT` |
| `generatedLets` | 4096 | The bindings that the compiler generates for a body, in all its branches and nested expressions together | The body of a function, of a method or of a lambda, in each specialized instance | `E_LIMIT` |
| `specializations` | 4096 | The specialized instances. Each lambda is one. Each higher-order function is one for its check on its own and one more for each combination of function values that the program passes to it. Lambdas and instances of higher-order functions count together | A program | `E_LIMIT` |
| `elaborationWork` | 1,000,000 | The units of the bodies that the checker elaborates: one for each function and for each of its parameters, and one for each block, statement and expression of its body. A method counts at each key at which it applies, and a lambda or a higher-order function for each specialized instance. A `value` block of a resource function counts with the scalar bindings that it sees as its parameters | A program | `E_LIMIT` |

The compiler generates these bindings for a body:

- one for each `let` statement;
- three for `unpack p as { scheme: X, point: x };`, and for the form with
  `witness` two and one more for each name of `fields`;
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

A path of the checker through a body takes these units of `bodyChecking`:

- one for each block that it enters, and one for each statement of that
  block up to and with the statement that it enters. The result of a block
  counts as one statement more;
- one for each expression that it enters. A pair of parentheses is no
  expression of its own;
- one more for each call;
- for a call of a function, one more, and one for each argument up to and
  with the argument that it enters, or one when the call has no argument. A
  call of a function value takes one more than a call of a function.

The value of a statement, an operand of an operator, an arm of an `if`, a
field of a `pack` and an argument of a call are each on a path of their own.
An argument of a call of a generic, of a built-in function or of a primitive
takes no unit for its position among the arguments.

A body of 4093 `let` statements with literal values and a literal as its
result is within the limit, and one more statement is beyond it. A block or
an `if` as the result takes three units more than a literal, so the body
holds 4090 such statements. A call `f(1, 2, 3)` of a function as the result
takes six units more than a literal, so the body holds 4087.

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
[Protocol 2](../protocol.md#protocol-2-flat-requests) says how the kernel
counts the units of `dispatchWork`.

## Names

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `namespaceResolution` | 4096 | The steps of resolving one path through modules, imports and reexports | A path | `E_LIMIT` |
| `namespaceImportWork` | 1,000,000 | The members that the checker visits when it checks the `use` declarations | A program | `E_LIMIT` |
| `namespaceProgramWork` | 4,000,000 | The units of work of the names of the whole program: the size of the request that the frontend writes, and the lookups of names in all bodies | A program | `E_LIMIT` |

[Diagnostics without a place of their own](../language/diagnostics.md#diagnostics-without-a-place-of-their-own)
gives the place of the diagnostic for `namespaceProgramWork`.
[Resolution](../language/names-and-paths.md#resolution) states the rule, and
[Protocol 3](../protocol.md#protocol-3-package-namespaces) says how the
kernel counts the units of the three limits.

## Edit authority

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `assemblyEvents` | 4096 | The events of the assembly | A program | `E_LIMIT` |
| `contributionMethods` | 4096 | The methods of all contributions of the package graph | A program | `E_LIMIT` |
| `dispatchKeys` | 4096 | The keys that the `domain` of a grant lists. A generic has at most this many keys, so only a list with a repeated key is longer | A grant | `E_LIMIT` |
| `authorityTraceWork` | 200,000,000 | The units of work of the audit of the assembly. The checker computes the units of each event from the live loans, the applied contributions and the declarations before it audits the event. All events share the budget | A program | `E_LIMIT` |
| `specializations` | 4096 | The checks of the methods of the contributions that the assembly does not apply. The checker checks each such method once for each key at which the method applies, also for a key outside the domain of its generic. This count is separate from the specialized instances of [Functions](#functions) | A program | `E_LIMIT` |

A contribution that the assembly does not apply, with one method whose six
selectors are `Any` for a generic of six parameters, makes 4096 such checks
and is within the limit. With a second such contribution whose method
applies at 1024 keys, the program is beyond it.
[Assemblies](../language/edit-authority.md#assemblies) and
[Contributions](../language/edit-authority.md#contributions) state the
rules, and
[Protocol 5](../protocol.md#protocol-5-scoped-edits-and-assembly) says how
the kernel counts the events, the methods and the units of the audit.

## Indexed declarations

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| Indexed declarations | 4096 | The `indexed` declarations of all packages | A program | `E_LIMIT` |
| Implementations of a classification | 64 | The implementations in the `domain` of a classification | A classification | `E_LIMIT` |
| Parameters of a family | 16 | The parameters of an `indexed family` | A family | `E_LIMIT` |
| Cases of a package declaration | 64 | The cases of an `indexed package` | A package declaration | `E_LIMIT` |
| Fields of a case | 64 | The fields of one case of an `indexed package` | A case | `E_LIMIT` |
| Position in a constraint | 2³² − 1 | The integer that names a parameter in a constraint of a family, such as the `1` of `same_base(0, 1)` | A constraint | `E_LIMIT` |

[Kinds of limits](../language/limits.md#kinds-of-limits) gives the place of
the diagnostic for the number of indexed declarations. A position in a
constraint must also name a parameter of the family, which
[Families](../indexed-source.md#families) requires; the limit bounds the
integer that the frontend reads.
[Indexed declarations](../indexed-source.md) states the rules.

## Exact affine algebra

The kernel checks [presented affine declarations](../affine-geometry.md) by
arithmetic of polynomials with rational coefficients. It bounds a polynomial
expression of the source before it expands the expression. Every substitution
of a check runs within `algebraWork` and `algebraTerms`: a structure map, a
pullback, a base chain, a base isomorphism and the composites of an
isomorphism or of a Cartesian square. A declaration beyond a limit of this
section is an error (`E_LIMIT`).
[Limits](../affine-geometry.md#limits) of that chapter states the rules, and
[Exact affine algebra checker](../verification.md#exact-affine-algebra-checker)
describes the checker and what is Proved about it.

| Limit | Value | Counts | Holds for |
| --- | --- | --- | --- |
| `algebraGenerators` | 16 | The coordinates of a presented affine object. A fiber product counts the coordinates of both factors | An object |
| `algebraRelations` | 32 | The relations of a presented affine object | An object |
| `algebraChain` | 16 | The objects of a base chain, with the object that declares the chain | An object |
| `algebraDegree` | 16 | The degree of a polynomial expression and each of its exponents | A polynomial expression |
| `algebraCoefficientDigits` | 64 | The decimal digits of a literal of a polynomial expression | A literal |
| `algebraNesting` | 64 | The levels of a polynomial expression, as [Polynomial expressions](../language/smooth-declarations.md#polynomial-expressions) counts them. Parentheses and unary `-` signs nest at most 63 deep | A polynomial expression |
| `algebraTerms` | 512 | The terms of each polynomial that a check produces, including each intermediate product | A polynomial |
| `algebraBasis` | 64 | The elements of the basis that the kernel computes for the relations of an object. While it computes the basis, the kernel keeps at most four times as many elements, 256 | An object |
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

## Frames

The kernel expands all entries of one [frame](../language/frames.md), its
declared inverse included, within one run of `algebraWork`. A constant frame
has the bounds of a Gram matrix, which the kernel checks before it computes
the inverse. The kernel computes the two products of a frame that depends on
the point and its declared inverse within a second run. A frame beyond a
limit is an error (`E_LIMIT`).
[Frame declarations](../language/frames.md#frame-declarations) states the
rules.

| Limit | Value | Counts | Holds for |
| --- | --- | --- | --- |
| `algebraGenerators` | 16 | The coordinates of the object of a frame, and so its frame vectors, the components of its arrays and the rows or columns of a map array | A frame |
| `algebraCoefficientDigits` | 64 | The digits of a literal in an entry of a frame, and of an index of `frame_component` or `frame_entry` | A literal |
| `metricEntryBits` | 512 | The bits of the numerator and of the denominator of one entry of a constant frame | An entry |
| `metricMatrixBits` | 16,384 | The bits of the [matrix bound](glossary.md#matrix-bound) of the matrix of a constant frame | A frame |
| `algebraTerms` | 512 | The terms of each polynomial of the two products of a frame and its declared inverse | A polynomial |
| `algebraWork` | 8,000,000 | The units of work of expanding the entries of one frame and its inverse, and of computing the two products | A run |

The kernel charges each product $pq$ of an entry of one matrix and an entry
of the other $(t(p) + 1)\,w(p)\,w(q) + t(p) + 1$ units before it computes it.
Here $t(p)$ is the number of terms of $p$, and $w(p)$ is the sum over the
terms of $p$ of $1 + \lfloor (\lfloor \log_2 |a| \rfloor + \lfloor \log_2 b
\rfloor) / 64 \rfloor$, for a coefficient $a/b$ in lowest terms. The charge
bounds the steps of the product, which adds the products of the terms of $p$
with $q$ to the sum of the earlier ones, one term of $p$ at a time. Adding a
product $q$ to the sum $p$ of the earlier products of an entry costs
$w(p) + w(q) + 1$ units. A frame whose
products need more units is an error (`E_LIMIT`), and the kernel computes no
product beyond the budget. The expansion of the entries is charged as in
[Exact affine algebra](#exact-affine-algebra).

These limits hold when the compiler checks a program. In an executable, the
rational numbers of frame arrays and map arrays have no bound.

## Physical dimensions

The kernel checks the declarations that
[Physical-dimension admission](../adr/0002-nature-dimension.md) admits: base
dimensions, quantities, readings, scales and physical metrics. It checks the
bound of every exponent before it computes a power. A scale magnitude and the
coefficient of an entry of a physical metric have the bound of a Gram entry.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `dimensionBases` | 16 | The `indexed base_dimension` declarations of all packages | A program | `E_LIMIT` |
| `dimensionExponent` | 64 | The absolute value of the exponent of a base dimension in a dimension, and of a scale in an entry of a physical metric | An exponent | `E_LIMIT` |
| `dimensionScaleFactors` | 16 | The scale factors of one entry of a physical metric | An entry | `E_LIMIT` |
| `metricEntryBits` | 512 | The bits of the numerator and of the denominator of a scale magnitude, and of the coefficient of an entry of a physical metric | A scale or an entry | `E_LIMIT` |

## Resource functions

[Resource programs](../storage/resource-programs.md) gives the rules of
resource functions. Most limits of this section have the code
`E_RESOURCE_LIMIT`, and the last column names the other codes.

| Limit | Value | Counts | Holds for | Code |
| --- | --- | --- | --- | --- |
| `value` blocks | 4096 | The `value` blocks of all resource functions: each `value` statement and the block that ends each function. Each resource function ends with one, so a program has at most 4096 resource functions | A program | `E_RESOURCE_LIMIT` |
| Statements | 4096 | The statements of all resource functions, with the statements of both arms of each `if` and the steps of each plan of a contraction tree. The `value` block that ends a function is no statement | A program | `E_RESOURCE_LIMIT` |
| Steps of one function | 4096 | The steps of the body of one resource function before the checker expands its calls: one for the function, one for each statement, and one more for each `allocate`, `borrow`, `release`, `drop` and `fill` statement and for each of their `runtime_` forms | A resource function | `E_RESOURCE_LIMIT` |
| Parameters and owned results | 64 each | The parameters of a resource function, and its owned results | A resource function | `E_RESOURCE_LIMIT` |
| Arguments and results of a call | 64 each | The arguments of a `call` statement, and the bindings that take its owned results | A call | `E_RESOURCE_LIMIT` |
| Views of a contract | 64 | The layouts of one `initialized […]` contract | An owned parameter or result | `E_RESOURCE_TYPE` |
| Expansion of calls | 4096 | The units of one expansion. The checker expands each resource function once for the check of the function on its own, and the entry point once more, each with the functions that it calls. The first list below the table says which units an expansion takes | An expansion | `E_RESOURCE_LIMIT` |
| Depth of calls | 4096 | The units of one chain of calls: one for each function that the chain enters, and one for each statement of such a function up to and with its call. In the last function of the chain, every statement that the checker reaches counts | A chain of calls | `E_RESOURCE_LIMIT` |
| `resourceWork` | 32,000,000 | The weighted units of work of checking all resource functions: the check of each function on its own and the check of the entry point | A program | `E_LIMIT` |
| Initialization records | 4096 | The nodes of the record that the checker keeps of the writes to one allocation: one for the end of the record, one for each write that the record keeps, and one for each join of two arms that keeps the records of both arms. The record keeps no write that the bounded query of the table below shows covered already, and no write that continues the last recorded write | An allocation | `E_RESOURCE_LIMIT` |
| Initialization query | 65,536 | The visits of the record of one allocation by one query of the cells of a view. Over a record of `n` nodes, a query walks at most the smaller of 256 and 65,536 / `n` steps from write to write, and a view with padding shares them among its stored columns | A read of a view | `E_RESOURCE_INIT` |
| Integers | 2⁶⁴ − 1 | An integer of a storage type, of a layout, of an allocation size, of a cell index or of `f64_bits` | An integer | `E_RESOURCE_LIMIT` |
| Bytes of an allocation | 2⁶³ − 1 | The cells of an allocation times the size of a cell, 8 bytes for `F64` and 16 for `Complex<F64>` | An allocation | `E_RESOURCE_OVERFLOW` |
| Rows, columns and leading of a layout | 2³¹ − 1 | The three numbers of a `layout` | A layout | `E_RESOURCE_LAYOUT` |

An expansion of calls takes these units:

- one for each function that it enters, and one for each statement that it
  reaches;
- one more for each storage operation of a statement. A statement such as
  `allocate`, `borrow`, `store`, `release` or `drop` is one operation and
  therefore takes two units. A declaration such as `space` has no operation
  and takes one unit;
- one more for each `value` statement;
- one for the result of the function that the checker expands, unless the
  result type is a pair type. The result of the entry point takes this
  unit.

An entry point that allocates an owner, borrows it, makes 2043 `store`
statements, releases the loan and drops the owner takes 4096 units: one for
the function, two for each of its 2047 statements and one for its result.
One more `store` statement is beyond the expansion of calls. In a chain of
functions that each make one `value` statement and then call the next,
apart from the last, 1024 functions are within the limit and 1025 beyond
it. The entry point is the first function of the chain. With two `value`
statements in each function, 682 functions are within the limit and 683
beyond it.

Every step of one function is a unit of the expansion of the function, so
the limit on the steps rejects no body that the expansion of calls admits.
The checker counts the steps first, and the diagnostic names them where a
body is beyond both limits. A resource function with 1023 pairs of an
`allocate` and a `drop` statement has 4093 steps and is within both. With
1024 pairs it is beyond the steps of one function.

Every unit of the depth of calls is a unit of the expansion of calls too. A
program is therefore beyond the depth only where it is beyond the
expansion, and the diagnostic names the depth where the two limits end at
one statement or call. A chain of resource functions in which each
function only calls the next, with the entry point first, holds at most
2048 functions, and the call of a 2049th is beyond the depth of calls. A
chain of three functions with 1363, 1363 and 1364 `space` statements, in
which the first two call the next after their statements, is within both
limits. With 1365 `space` statements in the third function, the
result of the entry point is beyond the expansion of calls. With 1366, the
last statement is beyond the depth of calls.

A write whose cells follow each other without a gap, such as a `store` or the
`fill` of a view without padding, can continue the last recorded write. It
does so when its first cell follows the last cell of that write, or its last
cell precedes the first, and when that write is a `store`, a write of a view
`layout(offset, n, 1, n, false)` or a record that such writes extended.
The checker then extends that record and adds no node. Stores of consecutive
cells, in increasing or in decreasing order, therefore leave one node,
however many cells they write.

The record also grows at a join of two arms. A join adds no node when the
two arms leave equal records, or when the record of one arm is that of the
other with one more write or with a longer last write. Where each arm adds
one write to the record before the `if`, or extends its last write, the join
adds no node either when the two writes are disjoint, when one contains the
other, or when both have no gap. Two writes without a gap leave the cells
that they share. Where one arm adds a write and the other extends the last
write before the `if`, the join adds no node when the write and the cells of
the extension do not overlap. Any other join keeps the records of both arms.
Each of the two then holds the record before the `if`, so the count about
doubles.

Take a function that stores cells of which no two follow each other: two
`store` statements, and then nine `if` statements whose arms each store two
cells, of which the second is the same cell in both arms. Its record has
4091 nodes. Five further `store` statements of such cells are within the
limit. A sixth is an error with the code `E_RESOURCE_LIMIT`, and so is a
tenth such `if`. The order of the stores in an arm matters: where each arm
stores the shared cell first, the checker accepts a tenth such `if`. Where
the cells of the function are consecutive, its stores extend the last
write, and each join after the first adds one node. After nine such `if`
statements the record then has 14 nodes.

A query of the cells of a view first looks for one recorded write that
covers the view, such as a `fill` or the record of consecutive stores.
Otherwise it walks from write to write through the cells, within the bound
of the table. Stores in an order in which no store continues the one before
leave one node each. Take a view of 255 cells whose stores write first the
cells of even index and then those of odd index. The view can be borrowed
for reading. With 256 cells in this order the `borrow` is an error
(`E_RESOURCE_INIT`), although the stores write every cell. A write that the
query shows covered adds no node. A `fill` of such stores adds none while the
record is short enough for the query to pass them, and a later read of the
cells walks the stores again, within the bound for the record of that time.
[Resource statements](../storage/resource-programs.md#resource-statements)
gives the rule, and
[Checked storage](../storage/checked-storage.md#storage-ir) describes the
records.
[Resource checking work](../storage/checked-storage.md#storage-functions--resource-checking-work)
describes the units of `resourceWork`.

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
it has limits of its own on the request. A limit of an earlier section
bounds a source program first, as the table says for each row, and no
source program is known to reach a limit of this table. A request beyond
one is an error with the code of the last column.
[Request](#request) gives the one bound of a request that a source program
does reach.

| Limit | Value | Counts | Code |
| --- | --- | --- | --- |
| `typeNesting` | 64 | The steps of decoding a function type of a request. A function type nested 63 deep is within the limit, and the parser reports `parseNesting` for a deeper source type | `E_PROTOCOL` |
| `sourceNesting` | 512 | The steps of decoding a body of a request. `parseNesting` and `astDepth` bound a source program first | `E_PROTOCOL` |
| Nesting and numbers of a request | 16,384 levels, 64 digits | The nesting of the arrays and objects of a request, and the digits of one of its numbers, as [Responses](../protocol.md#responses) says | `E_PROTOCOL` |
| `dependencyGraph` | 4096 | The packages on one chain of dependencies of a request. `packageNesting` bounds a source program first | `E_LIMIT` |
| Resource functions | 4096 | The resource functions of a request. The limit on `value` blocks bounds a source program first | `E_RESOURCE_LIMIT` |
| Storage plan | 4096 | The operations of one expansion, with both arms of each branch, and the length of one path of the checker through them. Each operation takes a unit of the expansion of calls, which bounds a source program first | `E_RESOURCE_LIMIT` |
| Requests of the specialization worklist | 2,000,001 | The requests for instances that one pass of the function checker handles. The bound is smaller when a bound that the kernel computes from the number of definitions and of the calls in their bodies is smaller. `specializations` and `elaborationWork` bound a program first | `E_LIMIT` |

## Bounds that reject nothing

These bounds change what the compiler does for a program and reject no
program, as [Limits](../language/limits.md#bounds-that-reject-nothing) says.

| Bound | Value | What it bounds |
| --- | --- | --- |
| `generatedLets` | 4096 | The bindings of a function after the compilation of its reverse passes |
| Declaration ids of a Core module | 4096 | The declarations that the compiled reverse passes add to a module |
| `reverseLeaves` | 256 | The maps of one reverse pass that the compilation reads through `let` statements and `compose`, in [`IndexedReverse.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedReverse.lean) |
| Notes of a resource diagnostic | 32 | The notes that follow one diagnostic of a resource program |
| Search for an uninitialized cell | 131,072 | The records that the checker visits to find the cell that a diagnostic names |
| `captureDiagnostic` | 8192 | The steps of a search for the place of a capture. No route of the kernel executable uses the search: its only use is in a checker that the executable holds and does not call |
| `namespaceNesting` | 1024 | The recursion through a body of the pass that puts the names of the source into a diagnostic. On the routes of the kernel executable, no other pass of the checker of names reads a body, and this pass keeps the diagnostic as it is when it reaches the bound |
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

## Bounds of the native runtime

The storage runtime of an executable has two bounds of its own. Neither
changes which programs the compiler accepts.

| Bound | Value | What it bounds |
| --- | --- | --- |
| Live bytes | 2⁶³ − 1 | The bytes of the live allocations of an executable, with one count for the static allocations and one for the allocations with runtime extents. An allocation that would bring a count above the bound stops the executable (`E_NATIVE_ALLOCATION`) |
| Message of a failed `expect` | 361 bytes | The text of the run-time diagnostic of a failed `expect` or `runtime_expect`, from the code `E_NATIVE_EXPECT` to the end of the line |

[Limits at run time](../language/limits.md#limits-at-run-time) describes the
count of live bytes, and
[Running a resource program](../storage/resource-programs.md#running-a-resource-program)
the message.

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
