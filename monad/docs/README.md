# `monad` package

Declare a path dependency on [the package manifest](../Vastitas.toml) under
the alias `monad` to use its operational interface. Its functions derive
their arrow types and operations from a named, checked
[`std::category::Monad`](../../stdlib/docs/category.md) and its revision.

| Name | Kind | Contract |
| --- | --- | --- |
| `kleisli` | module | Apply the unit, bind, composition and lift of the selected Monad. [API and example](kleisli.md) |
