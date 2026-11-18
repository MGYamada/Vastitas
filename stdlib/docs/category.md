# `std::category`

The package `vastitas_category` declares schemas for finite categories, functors,
natural transformations and monads.
An application supplies an instance with its own objects, arrows, endpoint
tables, identities and composition table. The package has no dependencies.
See the [module source](../src/category/mod.vast) and
[finite carriers and tables](../../docs/indexed-source.md#finite-carriers-and-tables).

| Name | Kind | Contract |
| --- | --- | --- |
| `Category` | finite schema | An instance supplies the six fields of a finite category and satisfies the identity and associativity laws. |
| `Functor` | finite schema | An instance supplies two named categories and their object and arrow maps. Those maps preserve endpoints, identities and composition. |
| `NatTrans` | finite schema | An instance selects two functors with the same source and target categories. Its component table supplies one arrow per source object and the naturality square commutes for every source arrow. |
| `Monad` | finite schema | An instance selects a category, an endofunctor and two natural transformations for its unit and multiplication. Its component tables satisfy both unit laws and associativity. |
| `compose(g, f)` | function | Given `f: Hom<C, X, Y>` and `g: Hom<C, Y, Z>`, return `g` after `f` in `Hom<C, X, Z>` for the same category. |

The optional [`monad::kleisli` package](../../monad/docs/kleisli.md) consumes
a named instance of this `Monad` schema. Its derived views, unit, extension, bind, composition and lift
use that instance’s category, functor, unit and multiplication.

For `S3` declared with this schema and arrows `g` and `f`, the call
`std::category::compose(g, f)` infers the category and the three objects
from the arguments. The explicit form for arrows on its sole object `o`
is `std::category::compose::<S3, Obj::o, Obj::o, Obj::o>(g, f)`.
The [library test](../../tests/finite_lookup.rs) checks both orders of two
permutations whose composition depends on their order.
