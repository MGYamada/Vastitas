# Edit authority

A [generic](../stage1a.md#declarations) is a family of methods that the
compiler checks as a whole. **Edit authority** decides which module may add
methods to a generic. The module that defines a generic holds that authority.
A **grant** lets another module contribute methods, through the **assembly** of
the root package, which borrows the grant, applies the contributions and seals
the generic. The assembly runs at compile time and fixes one environment. No
method changes at run time. Edit authority exists only in
[manifest mode](programs.md#manifest-mode).

## Owners

Every declaration has a fixed **identity**: its package, the logical path of
its module and its name. Aliases, reexports, file names and the order of
reading do not change an identity. The **current owner** of a generic is the
module that defines it, until a [transfer](#transfers) hands it to another
module.

Rules:

- A `method` declaration must be in the module that defines its generic.
  Another module is an error (`E_OWNER`), and so is a method for an ordinary
  function.
- A child module, `pub`, `use` and an alias grant no edit authority.
- Abstract types and abstract methods have owner rules of their own, which
  [Abstract types](../stage1a.md#abstract-types) gives. A transfer does not
  change them.

## Grants and delegations

> **Syntax**
>
> ```text
> GrantDeclaration ->
>     `grant` IDENTIFIER `:` Path `to` Path `delegable`? `{` `domain` Region `}`
> DelegationDeclaration ->
>     `delegation` IDENTIFIER `:` Path `to` Path `delegable`? `{` `domain` Region `}`
> Region -> `;` | RegionKey ( `,` RegionKey )* `,`? `;`
> RegionKey -> `(` ( ScalarType ( `,` ScalarType )* `,`? )? `)`
> ```

`grant g : f to p::m { domain … }` declares the permission `g` for the module
`m` of the package `p` to edit the generic `f`. The path after `to` is the
**recipient**: its first segment is the name in the `[package]` table of the
recipient's manifest, and the rest is the logical path of its module. `to p`
names the root module of `p`. The **region** lists the argument tuples of
scalar types that the recipient's methods may win; `domain;` is an empty
region. A grant is a permission, not an active edit: it takes effect only when
an assembly borrows it.

A **delegation** has the same form. It lets the holder of a loan pass part of
its permission on to another module, as [Assemblies](#assemblies) describes.
`delegable` marks a grant or a delegation that permits this.

Rules:

- A grant must be declared by a module that holds edit authority over the
  generic at some point of the assembly. A delegation must be declared by the
  recipient of the loan that it extends. A declaration by another module is an
  error (`E_OWNER`).
- The recipient package must be in the dependency closure of the root package,
  and exactly one package there must have that name. Its module must exist and
  must differ from the issuer. Another recipient is an error (`E_OWNER`). A
  dependency alias does not name a recipient, and a declaration never adds a
  package to the package graph.
- The tuples of a region have the arity of the generic. An empty region
  permits no winning tuple.
- Grants, delegations and contributions follow the ordinary
  [visibility](names-and-paths.md#visibility) rules when another module names
  them.
- `to module("…", "…")` is an error (`E_UNSUPPORTED`). The recipient is a path.
- A grant does not permit changes to abstract-type membership or to abstract
  method contracts.

The defining package of
[`examples/packages/edit-borrow`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/edit-borrow)
grants the package `edit_addon` the region `(Int, Int)` of `choose`:

```vast
{{#include ../../examples/packages/edit-borrow/lib/main.vast}}
```

## Contributions

> **Syntax**
>
> ```text
> ContributionDeclaration -> `contribution` IDENTIFIER `:` Path `{` MethodDeclaration* `}`
> ```

A **contribution** is a named set of methods for one generic, declared outside
the generic's module or by its owner. Its identity is its package, module and
name, and each method has its position in the contribution. A contribution
adds its methods only when an assembly applies it.

Rules:

- A contribution holds methods with bodies. An abstract method in a
  contribution is an error (`E_PARSE`).
- Every method of a contribution is checked, also when no assembly applies the
  contribution. The checker checks an unapplied method against the final set of
  methods, for every argument tuple to which it applies, but the method never
  takes part in dispatch.
- Two contributions applied to one generic must not hold methods with the same
  normalized signature (`E_DUPLICATE`).

The package `edit_addon` contributes one method:

```vast
{{#include ../../examples/packages/edit-borrow/addon/main.vast}}
```

## Assemblies

> **Syntax**
>
> ```text
> AssemblyDeclaration -> `assembly` `{` AssemblyEvent* `}`
> AssemblyEvent -> `borrow` Path `as` IDENTIFIER `;`
>     | `reborrow` IDENTIFIER `via` Path `as` IDENTIFIER `;`
>     | `apply` Path ( `using` IDENTIFIER )? `;`
>     | `return` IDENTIFIER `;`
>     | `transfer` Path `;`
>     | `seal` Path `;`
> ```

An assembly is a list of **events** that the compiler replays in order. A
**loan**, an [edit loan](../appendix/glossary.md#edit-loan), is the edit
authority that a `borrow` or `reborrow` event activates; the event names it. The root package coordinates the events, but it gains no
edit authority of its own: every event uses a permission that some module
declared.

| Event | Meaning |
| --- | --- |
| `borrow g as l;` | Activate the grant `g` as the loan `l` |
| `reborrow l via d as k;` | Activate the delegation `d` as the loan `k`, nested in the loan `l` |
| `apply c using l;` | Add the methods of the contribution `c` under the loan `l` |
| `apply c;` | Add the methods of the contribution `c` of the current owner |
| `return l;` | End the loan `l` |
| `transfer t;` | Make the recipient of the transfer `t` the current owner |
| `seal f;` | Close the generic `f` and check it |

Rules:

- A program has at most one assembly, in the root module of the root package.
  An assembly in another module is an error (`E_ASSEMBLY`), and a second one in
  a module is an error (`E_DUPLICATE`). A program without an assembly behaves
  as if it had an empty one.
- A generic has at most one active loan that may edit it. A second `borrow` is
  an error (`E_BORROW`). A loan name must not be used twice in an assembly
  (`E_BORROW`).
- `apply c using l` requires that `l` is active and that its recipient is the
  module of `c`. `apply c` without a loan requires that the module of `c` is
  the current owner. Another `apply` is an error (`E_OWNER`). While a loan of
  the generic is active, `apply` without a loan is an error (`E_BORROW`).
- `reborrow l via d as k` requires that `l` comes from a `delegable` grant or
  delegation, that its recipient declared `d` for the same generic, and that
  the region of `d` lies in the region of `l`. Another `reborrow` is an error
  (`E_OWNER`).
- While `k` is active, its parent `l` is suspended: it may neither edit nor be
  reborrowed (`E_BORROW`). Loans end from the inside out: returning a parent
  before its child is an error (`E_BORROW`), and so is returning a loan that is
  not active.
- Returning a loan keeps the methods that it installed. The generic stays open,
  and the owner may still apply contributions before the seal.
- `seal f` requires that no loan of `f` is active (`E_BORROW`). A sealed
  generic cannot be borrowed or transferred (`E_ASSEMBLY`).
- At the end of the assembly, every loan must be returned (`E_BORROW`), and
  every generic that the assembly edited or transferred must be sealed
  (`E_ASSEMBLY`).
- Applying the same contribution twice under the same permission is the same as
  applying it once. The same contribution with different provenance is an
  error (`E_PROVENANCE`).
- The words of the events, and `grant`, `delegation`, `transfer` and
  `contribution`, are keywords only in these declarations. A binding may use
  them as names.

The root package of `edit-borrow` borrows the grant, applies the
contribution, returns the loan and seals `choose`:

```vast
{{#include ../../examples/packages/edit-borrow/app/main.vast}}
```

The executable prints `42`.

## Sealing

When an assembly seals a generic, the compiler checks the generic as a whole,
with every method that the assembly installed:

- every argument tuple of the generic has no ambiguity, as
  [Finite dispatch](../stage1a.md#selection-and-whole-program-checking)
  describes;
- every tuple of the domain, including the domains of abstract methods, has
  one winning method, whose result type matches every abstract method that
  covers the tuple;
- every tuple that a contributed method wins lies in the region of its grant,
  and in the regions of all the grants and delegations that its loan descends
  from. Another tuple is an error (`E_IMPACT`);
- every method body that applies to some tuple is checked, also when it never
  wins.

Until the seal, an edit may leave an ambiguity or a tuple without a winner, and
a later contribution may repair it. A generic that no assembly edits gets the
same checks without a seal.

## Transfers

> **Syntax**
>
> ```text
> TransferDeclaration -> `transfer` IDENTIFIER `:` Path `to` Path `;`
> ```

`transfer t : f to p::m;` declares an operation that hands the current
ownership of the generic `f` to the module `m` of the package `p`. The
recipient path has the same form as the recipient of a grant. The event
`transfer t;` in the assembly performs it. The identity of `f` does not change.

Rules:

- A transfer must be declared by the current owner of the generic when the
  event runs. Another transfer, also a transfer that already ran, is an error
  (`E_OWNER`).
- No loan may be active when a transfer runs (`E_BORROW`).
- After a transfer, the former owner has no authority over the generic, and
  the recipient applies its contributions without a loan. The `method`
  declarations of the generic stay in the defining module; the recipient adds
  methods only through contributions.
- A transferred generic must be sealed, also when the assembly installs no
  method (`E_ASSEMBLY`).
- Every method, grant, contribution and open obligation of the generic stays
  as it was. A grant of the recipient becomes usable only after the transfer.
- A transfer changes the owner of a generic only. Abstract-type membership,
  abstract method contracts, ordinary functions and single methods have no
  transfer.

[`examples/packages/edit-authority`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/edit-authority)
nests a loan through a delegation and then transfers the generic. The defining
package declares a delegable grant and a transfer:

```vast
{{#include ../../examples/packages/edit-authority/base/main.vast}}
```

The recipient declares the delegation and its contributions:

```vast
{{#include ../../examples/packages/edit-authority/addon/main.vast}}
```

The assembly returns the nested loan before its parent, transfers `choose` and
applies the recipient's contribution without a loan:

```vast
{{#include ../../examples/packages/edit-authority/app/main.vast}}
```

The executable prints `44`.
