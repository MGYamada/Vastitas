# Edit authority across packages

The module that defines a generic holds the edit authority over it. This
chapter lets a second package add a method to the generic of a library.
Three declarations take part, each in a package of its own:

1. The library declares a grant: its permission for one other module to add
   methods at some keys.
2. The second package declares a contribution: the methods that it adds.
3. The program declares an assembly, which applies the contribution under
   the grant.

The first program is
[`examples/packages/edit-borrow`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/edit-borrow).
Its three packages are in the directories `lib`, `addon` and `app`, and their
manifests name them `edit_base`, `edit_addon` and `edit_app`.

## The grant

The library defines the generic `choose` in `lib/main.vast`:

```vast
{{#include ../../examples/packages/edit-borrow/lib/main.vast}}
```

`choose` has one method, which returns 0 for any two numbers. The
[**grant**](../appendix/glossary.md#grant) `integers` permits the root module
of the package `edit_addon` to add methods to `choose`. The module after `to`
is the [**recipient**](../appendix/glossary.md#recipient). The path begins
with the name in the `[package]` table of the recipient's manifest, not with
a dependency alias. The library does not depend on the package that it names.

The [**region**](../appendix/glossary.md#region) of the grant lists the keys
at which the recipient's methods may win. Here it is the one key `(Int, Int)`.

A grant is a permission. It adds no method.

## The contribution

The second package depends on the library under the alias `base`. Its root
module, `addon/main.vast`, declares the methods that it wants to add:

```vast
{{#include ../../examples/packages/edit-borrow/addon/main.vast}}
```

A [**contribution**](../appendix/glossary.md#contribution) is a named set of
methods for one generic. The method of `sum` is more specific than the method
of the library at the key `(Int, Int)`.

A contribution adds no method either. The compiler checks its bodies, and its
methods take part in dispatch only when an assembly applies the contribution.

## The assembly

The third package depends on both others, under the aliases `base` and
`addon`. Its root module, `app/main.vast`, puts the pieces together:

```vast
{{#include ../../examples/packages/edit-borrow/app/main.vast}}
```

The [**assembly**](../appendix/glossary.md#assembly) is a list of
[**events**](../appendix/glossary.md#event). The compiler replays them in
order when it checks the program:

| Event | Effect |
| --- | --- |
| `borrow base::integers as edit;` | Activates the grant `integers` as the [**loan**](../appendix/glossary.md#edit-loan) `edit` |
| `apply addon::sum using edit;` | Adds the methods of the contribution `sum` to `choose`, under the loan |
| `return edit;` | Ends the loan |
| `seal base::choose;` | Closes `choose` and checks it with all its methods |

```sh
target/debug/vastitas check --manifest-path examples/packages/edit-borrow/app/Vastitas.toml
target/debug/vastitas build --manifest-path examples/packages/edit-borrow/app/Vastitas.toml -o target/edit-borrow
./target/edit-borrow
```

The program prints `42`: `choose(40, 2)` is a call of the method that the
add-on contributed. Without the `assembly` block, the same call selects the
method of the library, and the program prints `0`.

A program has at most one assembly. It stands in the root module of the
root package, the package whose manifest the command names. The assembly
gives that package no edit authority of its own: each event uses a grant or
a contribution that some module declared. All of this happens at compile time. The executable
holds the final methods, and nothing changes them when it runs.

## Regions and the seal

The seal checks the generic as a whole, with the methods of the library and
the methods that the assembly added. These are the checks of every generic.
No key has two best methods, and every key that callers may use has a
winner. Every body is valid at every key at which its method applies. One
check is specific to a contribution: its methods may win only at the keys of
the grant's region.

The next program repeats the library and the assembly of `edit-borrow` under
other package names:

```vast
{{#include ../../examples/reject/packages/outside-region/base/main.vast}}
```

```vast
{{#include ../../examples/reject/packages/outside-region/main.vast}}
```

Its contribution, `first`, has a broader selector for the second parameter:

```vast
{{#include ../../examples/reject/packages/outside-region/addon/main.vast}}
```

```text
{{#include ../../examples/reject/packages/outside-region.stderr}}
```

The contributed method applies at `(Int, Int)` and at `(Int, Nat)`, and at
both keys it is more specific than the method of the library. The grant
covers `(Int, Int)` only. The check covers `(Int, Nat)` although that key is
outside the domain of `choose`. A recipient therefore changes the winners
that the grant names and no others.

A loan is exclusive, and an assembly finishes what it starts. A second
`borrow` of a generic whose loan is still active is an error. Every loan must
end with `return` before the seal, and every generic that the assembly edits
must be sealed.
[Assemblies](../language/edit-authority.md#assemblies) and
[Sealing](../language/edit-authority.md#sealing) give the rules.

## Passing a loan on

The second program,
[`examples/packages/edit-authority`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/edit-authority),
has the packages `base`, `addon` and `app`. Its library marks the grant
`delegable`: the recipient may pass a part of the permission on.

```vast
{{#include ../../examples/packages/edit-authority/base/main.vast}}
```

The add-on passes its region on to its own module `ops`, with a
[**delegation**](../appendix/glossary.md#delegation). The contribution `sum`
is in that module:

```vast
{{#include ../../examples/packages/edit-authority/addon/main.vast}}
```

A delegation has the form of a grant. Its region must lie in the region of
the grant that it passes on. The assembly uses it with `reborrow`:

```vast
{{#include ../../examples/packages/edit-authority/app/main.vast}}
```

`reborrow parent via addon::inner as child;` activates the delegation as the
loan `child`, inside the loan `parent`. `apply addon::ops::sum using child;`
adds the method of `ops` under the inner loan. While `child` is active,
`parent` is suspended and applies nothing. Loans end from the inside out, so
`return child;` comes before `return parent;`.

## Handing a generic over

The library of this program also declares a
[**transfer**](../appendix/glossary.md#transfer), `handoff`. The event
`transfer base::handoff;` makes the root module of `addon` the
[**current owner**](../appendix/glossary.md#owner) of `choose`: the module
that holds its edit authority. No loan of `choose` may be active at that event.

After the transfer, `apply addon::boolean;` adds a contribution of `addon`
without a loan, because `addon` holds the edit authority itself. Before the
transfer the same event is an error. `choose` keeps its owner, the package
`base` and the name `choose`, and every path to it stays valid. Only the
right to add methods moves.

```sh
target/debug/vastitas build --manifest-path examples/packages/edit-authority/app/Vastitas.toml -o target/edit-authority
./target/edit-authority
```

The program prints `44`. `choose(40, 2)` is a call of the method of `sum`
and gives 42. `choose(true, true)` is a call of the method of `boolean` and
gives 2. [Transfers](../language/edit-authority.md#transfers) gives the
rules.

> **What is checked.** The compiler replays the events of the assembly in
> order. It checks each event against the grants, delegations, transfers and
> contributions that the modules declared, and it accepts no edit without
> one. At each seal it checks the whole generic. The
> [proofs](../verification.md#edit-authority-acceptance-protocol-6) cover
> the replay of an accepted assembly. One module edits a generic at a time,
> and nested loans return from the inside out. A transfer changes the
> current owner and not the owner. A contributed method wins only at keys
> that lie in every region above its loan. Tests cover the diagnostics and
> native execution.

## See also

- [Edit authority](../language/edit-authority.md): the rules of this
  chapter, by declaration.
- [Grants and delegations](../language/edit-authority.md#grants-and-delegations):
  recipients, regions and `delegable`.
- [Contributions](../language/edit-authority.md#contributions): the methods
  of a contribution and their checks.
- [Assemblies](../language/edit-authority.md#assemblies): the events, their
  order and the rules on loans.
- [Sealing](../language/edit-authority.md#sealing) and
  [Transfers](../language/edit-authority.md#transfers).
- [The package graph](../packages.md#the-package-graph): the packages of a
  program, among which a grant finds its recipient.
