# `monad::kleisli`

Each function uses a named instance of the finite [`std::category::Monad` schema](../../stdlib/docs/category.md)
and the object indices of its category. In the signatures below, `T X` denotes
the selected functor's action on `X`. The functions take arrows as ordinary
arguments and return arrows of the same category. See the
[module source](../src/kleisli/mod.vast).

| Name | Kind | Contract |
| --- | --- | --- |
| `Kleisli` | finite schema | A view `K` selects a named Monad on `C`. Its `Hom<K, X, Y>` is the base fiber `Hom<C, X, T(Y)>`. |
| `KleisliTriple` | finite schema | A triple selects the same Monad's object action, unit and extension. Pass it as an explicit Monad index. |
| `unit()` | function | At a static object `X`, return the selected unit component from `X` to `T X`. |
| `extend(f)` | function | Given `f` from `X` to `T Y`, return `μ_Y ∘ T(f)` from `T X` to `T Y`. |
| `bind(p, f)` | function | Given `p` from `S` to `T X` and `f` from `X` to `T Y`, return the composite of `p`, then `T f`, then the multiplication at `Y`. |
| `compose(g, f)` | function | Compose Kleisli arrows in the order `f` then `g`. |
| `lift(f)` | function | Follow an ordinary arrow `f` with the unit at its target. |

The [closure Monad example](../../examples/packages/finite-kleisli/src/main.vast)
declares both views of the closure on the two-object chain. The call
`monad::kleisli::unit::<Triple, Obj::lo>()` returns its nonidentity arrow
from `lo` to `hi`, which also inhabits `Hom<K, Obj::lo, Obj::lo>`.
The [LLVM preview](../../docs/guide/cli.md#llvm-preview) compiles this
example through both MidIR phases. Its LLVM entry calls the four specialized
functions and returns zero when all four arrow comparisons and the functor
action agree with the expected results.

The finite adapter takes represented arrows as arguments. At specialization it
uses the selected model's checked object and arrow tables and the named unit
and multiplication. The mathematical Kleisli hom from `A` to `B` is
`Hom<C, A, T(B)>`. Its extension sends `f` to `μ_B ∘ T(f)`; composing
that extension with `p` gives `bind(p, f)`. A named, capture-free function
may compute an arrow argument. In `bind(p, next())` the caller evaluates
`next()` once and passes its returned tag as the second argument to `bind`.
An ordinary function can receive `k: Fn<(), Hom<C, X, Y>>` and pass it
directly to `bind(p, k)` when its result inhabits the second parameter's
fiber. The selected forwarding method calls `k()` once. In `compose(g, f)`
either or both operands can be producers. The caller evaluates the two
argument expressions from left to right, then the method invokes each
producer in parameter order. The mathematical composite applies the arrow
from `f` first. [Direct forwarding fixture](../../llvm/fixtures/kleisli-forward/main.vast) · [Explicit invocation fixture](../../llvm/fixtures/kleisli-callback/main.vast)

A view selects the named Monad instance, including its unit and
multiplication. Two structures with the same functor can therefore have
different extensions. [Operational adapter contract](https://github.com/MGYamada/Vastitas/issues/206)
