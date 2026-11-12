# Generics, methods and dispatch

<a id="dispatch-and-abstract-contracts"></a>A function has one body. A [*generic*](../appendix/glossary.md#generic) is a
function with several bodies, its
[*methods*](../appendix/glossary.md#method). For each call of a generic, the
compiler chooses one method by the types of the arguments. This choice is
[*dispatch*](../appendix/glossary.md#dispatch). It happens at compile time:
each call of a generic becomes a call of one method, and an executable looks
up no method when it runs.

This chapter declares generics and methods, shows how the compiler chooses a
method, and uses the generic arithmetic of the standard library.

## Generics and methods

[`examples/book/dispatch/methods.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/dispatch/methods.vast)
declares a generic with two methods:

```vast
{{#include ../../examples/book/dispatch/methods.vast}}
```

The `generic` declaration names the generic and its parameters. A
[*key*](../appendix/glossary.md#dispatch-key) is a tuple of argument types,
one for each parameter. The [*domain*](../appendix/glossary.md#domain) lists
the keys at which callers may call the generic. `double` has one parameter,
and its callers pass a `Nat` or an `Int`.

A `method` declaration gives one body. It gives each parameter a
[*selector*](../appendix/glossary.md#selector), which says which argument
types the method accepts in that position, and it declares a result type. The
two methods of `double` have different result types.

The types of the arguments are the key of a call. `n` is a `Nat`, so
`double(n)` has the key `(Nat)`. It is a call of the first method, and its
type is `Nat`. The literal `11` is an `Int`, so `double(11)` is a call of the
second method.

Run the program from the repository root:

```sh
target/debug/vastitas check examples/book/dispatch/methods.vast
target/debug/vastitas build examples/book/dispatch/methods.vast -o target/methods
./target/methods
```

The program prints `42`.

Each type of a key is one of the four scalar types `Nat`, `Int`, `Bool` and
`Unit`. A value of another type, such as a pair, is not an argument of a
generic. A generic has at most six parameters.
[Generic declarations](../stage1a.md#generic-declarations) gives the rules of
the declaration.

## Selectors and capabilities

A selector is a scalar type, or a name for several of them. `Number` accepts
`Nat` and `Int`, and `Any` accepts every scalar type. `Nat` and `Int` are
siblings under `Number`: neither is narrower than the other.
[`examples/book/dispatch/selectors.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/dispatch/selectors.vast)
uses a scalar type, `Number` and `Any` as selectors:

```vast
{{#include ../../examples/book/dispatch/selectors.vast}}
```

A method [*applies*](../appendix/glossary.md#applicable-method) at a key
when its selectors accept the types of the key. All three methods of `rank`
apply at `(Int)`, and the first two apply at `(Nat)`. The compiler chooses
the method with the narrowest selector: the `Int` method for `7` and `-7`,
the `Number` method for `n`, and the `Any` method for `true`. The program
prints `42`.

A method can also require a
[*capability*](../appendix/glossary.md#capability): a property that some
scalar types have.
[`examples/book/dispatch/capabilities.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/book/dispatch/capabilities.vast)
requires an order:

```vast
{{#include ../../examples/book/dispatch/capabilities.vast}}
```

`HasOrder` holds for `Nat` and `Int`, the types with `<`. A method applies
only at keys whose types have the capabilities that it requires. The second
method therefore applies at `(Nat)` and at `(Int)`, and not at `(Bool)`. Both
methods apply at `(Nat)` and at `(Int)`, and the second one is chosen there,
because it requires more. A method `below_ten(x: Any)` without the `requires`
clause also applies at `(Bool)`, where the body `x < 10` is an error. The
program prints `42`.

The other capability is `HasEq`, which holds for every scalar type. A program
declares no capabilities of its own.
[Method declarations](../stage1a.md#method-declarations) lists the selectors
and the capabilities.
<a id="abstract-types"></a><a id="abstract-method-contracts"></a>The next
chapter, [Abstract types](abstract-types.md), declares selectors with names
of their own, and methods without a body.

## How a method is chosen

The two examples follow one rule. One method is
[*more specific*](../appendix/glossary.md#more-specific) than another when
its selectors are no broader and its requirements are no weaker, and one of
them is narrower or stronger. At a key, the
[*winner*](../appendix/glossary.md#winner) is the one applicable method
that no other applicable method is more specific than. A call of the generic
at that key is a call of the winner. The order of the declarations never
decides. [Selection](../stage1a.md#selection) gives the rules. The compiler
checks them for the whole generic, not only for the calls that a program
makes.

### Every key has at most one best method

In this program two methods apply at the key `(Int, Int)`:

```vast
{{#include ../../examples/reject/dispatch/crossed-selectors.vast}}
```

```text
{{#include ../../examples/reject/dispatch/crossed-selectors.stderr}}
```

Neither method is more specific than the other, so the key has no winner. The
compiler rejects the generic, and the last note proposes a method that
resolves the key. With a third method `meet(x: Int, y: Int)`, the program is
valid.

The compiler looks for such keys among all keys of scalar types, including
the keys outside the domain. It also requires a winner at every key of the
domain.

### Every body is checked at every key

A method with a broad selector is one body for several keys. The compiler
checks that body once for each key at which the method applies, with each
parameter at the type of the key:

```vast
{{#include ../../examples/reject/dispatch/unused-key.vast}}
```

```text
{{#include ../../examples/reject/dispatch/unused-key.stderr}}
```

The domain of `double` is `(Int)`, but its method also applies at `(Nat)`.
There `x + x` is a `Nat`, and the declared result is `Int`. The compiler
checks a body even at a key that no caller may use, and even where another
method wins. A broad method therefore cannot hide a body that fails for one
of its argument types.

### Arguments choose, results do not

The compiler finds the types of the arguments first and then chooses the
method. The type that the surrounding code expects plays no part:

```vast
{{#include ../../examples/reject/dispatch/literal-key.vast}}
```

```text
{{#include ../../examples/reject/dispatch/literal-key.stderr}}
```

An integer literal as an argument of a generic is an `Int`. The annotation
`Nat` on `n` does not turn `double(21)` into a call of the `Nat` method. Bind
the literal to a `Nat` first, as `methods.vast` does with its binding `n`.

A call must use a key of the domain. `double(true)` is an error for the
generic `double` of `methods.vast`, because `(Bool)` is not in its domain. A
call outside the domain is an error even when a method applies at its key.

## Promotion between `Nat` and `Int`

The standard library has generics for arithmetic on `Nat` and `Int`, in
[`stdlib/src/arithmetic/generic.vast`](https://github.com/MGYamada/Vastitas/blob/main/stdlib/src/arithmetic/generic.vast).
`add` and `maximum` take two numbers, each a `Nat` or an `Int`.
[`examples/dispatch-arithmetic.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/dispatch-arithmetic.vast)
calls both:

```vast
{{#include ../../examples/dispatch-arithmetic.vast}}
```

`add(left, right)` has the key `(Nat, Nat)` and returns a `Nat`. `nat_to_int`
is a function of the library that converts a `Nat` to an `Int`, so `maximum`
has the key `(Int, Int)`. Compile the program in flat mode with the three
library files, because the compiler loads no library on its own:

```sh
target/debug/vastitas build examples/dispatch-arithmetic.vast \
  --lib stdlib/src/arithmetic/int.vast \
  --lib stdlib/src/arithmetic/nat.vast \
  --lib stdlib/src/arithmetic/generic.vast -o target/dispatch-arithmetic
./target/dispatch-arithmetic
```

The program prints `42`.

For two arguments of one type, `add` and `maximum` return that type. For a
`Nat` and an `Int`, in either order, they return an `Int`. The methods for
these mixed keys call the generic `promote`, which converts the `Nat` with
`int` and returns both numbers as a `Pair<Int>`. They then call the `Int`
method on the two components. The library converts nothing implicitly: `int`
in `promote` is its only conversion.
[`examples/promotion.vast`](https://github.com/MGYamada/Vastitas/blob/main/examples/promotion.vast)
calls `promote` itself:

```vast
{{#include ../../examples/promotion.vast}}
```

`promote(n, 22)` has the key `(Nat, Int)`, and its result holds 20 and 22 as
`Int` values. `add(n, -7)` has the same key and returns the `Int` 13. Build
the program with the same three libraries. It prints `42`.

> **What is checked.** The compiler builds the table of winners of every
> generic before it generates code. It rejects the whole program for a key
> with two best methods and for a key of the domain without a winner. It
> also rejects the program for a method body that fails at a key. The
> [proofs](../verification.md#stage-1a-finite-dispatch-and-checker-composition)
> cover the selection. In an accepted table, each key that callers may use
> has the one applicable method that no other applicable method is more
> specific than. The order of the method records that the checker receives
> does not change the table. The specification
> [std::arithmetic::generic](../spec/std-arithmetic-generic.md) states what
> is proved about `promote`, `add` and `maximum`. Tests cover the
> diagnostics and native execution.

## See also

- [Generic declarations](../stage1a.md#generic-declarations): generics, keys
  and domains.
- [Method declarations](../stage1a.md#method-declarations): selectors,
  capabilities and result types.
- [Selection](../stage1a.md#selection): applicable methods, the winner, and
  the checks of a generic and of its calls.
- [Promotion](../stage1a.md#promotion): the results of `promote`, `add` and
  `maximum` at each key.
- [Flat mode](../language/programs.md#flat-mode): programs with `--lib`
  libraries.
- [Appendix D](../appendix/limits.md#generics-and-abstract-types): the limits on the
  parameters and the keys of a generic.
