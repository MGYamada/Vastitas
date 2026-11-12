# Edit authority

A [generic](../stage1a.md#generic-declarations) is a family of methods that the
compiler checks as a whole. **Edit authority** decides which module may add
methods to a generic. The module that defines a generic holds that authority.
A **grant** lets another module contribute methods, through the **assembly** of
the root package, which borrows the grant, applies the contributions and seals
the generic. The assembly runs at compile time and fixes one environment. No
method changes at run time. Edit authority exists only in
[manifest mode](programs.md#manifest-mode).

## Owners

Every declaration has a fixed **owner**: its package, the logical path of its
module and its name. Aliases, reexports, file names and the order of reading do
not change an owner. The **current owner** of a generic is the
module that defines it, until a [transfer](#transfers) hands it to another
module.

Rules:

- A `method` declaration must be in the module that defines its generic.
  Another module is an error (`E_OWNER`), and so is a method for an ordinary
  function.
- A child module, `pub`, `use` and an alias grant no edit authority. The
  defining module may name its own declaration through an alias.
- Abstract types and abstract methods have owner rules of their own, which
  [Abstract types](../stage1a.md#abstract-types) and
  [Abstract methods](../stage1a.md#abstract-methods) give. A transfer does not
  change them.

## Grants and delegations

> **Syntax**
>
> ```text
> GrantDeclaration ->
>     `grant` IDENTIFIER `:` Path `to` Path `delegable`? `{` `domain` Domain `}`
> DelegationDeclaration ->
>     `delegation` IDENTIFIER `:` Path `to` Path `delegable`? `{` `domain` Domain `}`
> ```

`grant g : f to p::m { domain … }` declares the permission `g` for the module
`m` of the package `p` to edit the generic `f`. The path after `to` is the
**recipient**: its first segment is the name in the `[package]` table of the
recipient's manifest, and the rest is the logical path of its module. `to p`
names the root module of `p`. The **region** lists the
[keys](../stage1a.md#generic-declarations) at which the recipient's methods
may win. It has the form of the domain of a generic; `domain;` is an empty
region. A grant is a permission, not an active edit: it takes effect only
when an assembly borrows it.

A **delegation** has the same form. It lets the holder of a loan pass part of
its permission on to another module, as [Assemblies](#assemblies) describes.
`delegable` marks a grant or a delegation that permits this. The module that
declares a grant or a delegation is its **issuer**.

Rules:

- The target of a grant, a delegation, a transfer or a contribution must be a
  generic. Another declaration is an error (`E_TYPE`).
- The issuer of a grant must hold edit authority over the generic at some
  point of the assembly, even when no event borrows the grant. Another issuer
  is an error (`E_OWNER`).
- A delegation has no authority until a `reborrow` uses it, as
  [Assemblies](#assemblies) says. An unused delegation is not checked against
  its issuer.
- The recipient package must be in the
  [package graph](../packages.md#the-package-graph), and exactly one package
  there must have that name. Its module must exist and must differ from the
  issuer. Another recipient is an error (`E_OWNER`).
- A dependency alias does not name a recipient, and a declaration never adds a
  package to the package graph. The package of the issuer need not depend on
  the package of the recipient.
- The recipient must be a path, so the name of the recipient package must be
  an identifier. A name that is no identifier forms no path: `to my-addon` is
  an error (`E_PARSE`). No grant, delegation or transfer names a package with
  such a name as its recipient.
- Every key of a region must have one type per parameter of the generic
  (`E_ARITY`), and each type must be a scalar type (`E_TYPE`). A key must not
  occur twice in a region (`E_DUPLICATE`). An empty region permits no win.
- Grants, delegations, transfers and contributions follow the ordinary
  [visibility](names-and-paths.md#visibility) rules when another module names
  them (`E_VISIBILITY`).
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
> ContributionDeclaration ->
>     `contribution` IDENTIFIER `:` Path `{` MethodDeclaration* `}`
> ```

A **contribution** is a named set of methods for one generic. Any module may
declare one. Its owner is its package, module and name, and each method has
its position in the contribution. A contribution adds its methods only when an
assembly applies it.

Rules:

- A contribution holds at least one method, and every method has a body. An
  empty contribution is an error (`E_ASSEMBLY`), and an abstract method in a
  contribution is an error (`E_PARSE`).
- Every method of a contribution must be a method of the contribution's
  generic. A method of another generic is an error (`E_OWNER`).
- The body of a method of a contribution names declarations by the rules of
  the module that declares the contribution. It may call a private function
  of that module, under a loan and after a
  [transfer](#transfers) alike. Applying the contribution makes no private
  declaration visible to another module (`E_VISIBILITY`).
- The compiler checks every method of a contribution, even when no event
  applies the contribution. It checks an unapplied method against the final
  set of methods, at every key at which the method applies, but the method
  never takes part in dispatch.
- The methods of an applied contribution are methods of the generic. The rule
  of [Method declarations](../stage1a.md#method-declarations) against equal
  selectors and requirements covers them (`E_DUPLICATE`): within one
  contribution, between applied contributions, and against the `method`
  declarations. It does not cover an unapplied contribution.

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
authority that a `borrow` or `reborrow` event activates; the event names it.
The root package coordinates the events, but it gains no edit authority of its
own: every event uses a permission that some module declared.

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
  An assembly in another module is an error (`E_ASSEMBLY`), and a second
  assembly in one module is an error (`E_DUPLICATE`). A program without an
  assembly behaves as if it had an empty one.
- Each event must name a declaration of the kind that the table gives:
  `borrow` a grant, `via` a delegation, `apply` a contribution, `transfer` a
  transfer and `seal` a generic. Another kind is an error (`E_TYPE`).
- A generic has at most one active loan that may edit it. A second `borrow` is
  an error (`E_BORROW`). A loan name must not be used twice in an assembly
  (`E_BORROW`).
- In `apply c using l`, the loan `l` must be active (`E_BORROW`). It must be a
  loan of the generic of `c`, and its recipient must be the module of `c`
  (`E_OWNER`).
- In `apply c` without a loan, the module of `c` must be the current owner
  (`E_OWNER`), and no loan of the generic may be active (`E_BORROW`).
- In `reborrow l via d as k`, the loan `l` must be active (`E_BORROW`). It
  must come from a `delegable` grant or delegation, its recipient must have
  declared `d` for the same generic, and the region of `d` must lie in the
  region of `l` (`E_OWNER`).
- While `k` is active, its parent `l` is suspended: it may neither edit nor be
  reborrowed (`E_BORROW`). Loans end from the inside out: returning a parent
  before its child is an error (`E_BORROW`), and so is returning a loan that is
  not active.
- Returning a loan keeps the methods that it installed. The generic stays open,
  and the current owner may still apply contributions before the seal.
- No loan of `f` may be active at `seal f` (`E_BORROW`). A later event must
  not edit, borrow, transfer or seal a sealed generic (`E_ASSEMBLY`).
- At the end of the assembly, every loan must be returned (`E_BORROW`).
- Every generic to which the assembly applied a contribution must be sealed
  (`E_ASSEMBLY`). So must every generic that it transferred, even when the
  assembly installed no method. A generic that the assembly only borrowed
  needs no seal.
- Applying the same contribution twice under the same permission is the same as
  applying it once. The same contribution with different provenance is an
  error (`E_PROVENANCE`).
- An assembly must have at most 4096 events, and the contributions of the
  package graph must hold at most 4096 methods. Otherwise it is an error
  (`E_LIMIT`). The checks of the methods of the contributions that the
  assembly does not apply have a limit too (`E_LIMIT`).
  [Appendix D](../appendix/limits.md#edit-authority) gives these three
  limits and the two other limits of edit authority: on the keys that the
  domain of a grant lists and on the work of the audit of the assembly.
- `borrow`, `reborrow`, `via`, `using`, `seal`, `to`, `delegable`, `grant`,
  `delegation`, `transfer`, `contribution` and `assembly` are keywords only in
  these declarations, and a binding may use them as names. `apply` is a
  [reserved name](lexical-structure.md#reserved-names), and `as` and `return`
  are [strict keywords](lexical-structure.md#keywords).

The root package of `edit-borrow` borrows the grant, applies the
contribution, returns the loan and seals `choose`:

```vast
{{#include ../../examples/packages/edit-borrow/app/main.vast}}
```

The executable prints `42`.

## Sealing

When an assembly seals a generic, the compiler checks the generic as a whole,
with every method that the assembly installed. The checks are those of
[Selection](../stage1a.md#selection) and of
[Abstract methods](../stage1a.md#abstract-methods): ambiguity, winners in the
callable domain, result types, and every method body.

Rules:

- Every key that a contributed method wins must lie in the region of its
  grant, and in the regions of all the grants and delegations that its loan
  descends from. Another key is an error (`E_IMPACT`), including a key outside
  the callable domain of the generic.
- Until the seal, an edit may leave an ambiguity or a key without a winner,
  and a later contribution may repair it.
- A generic that no assembly edits gets the checks of Selection without a
  seal.

## Transfers

> **Syntax**
>
> ```text
> TransferDeclaration -> `transfer` IDENTIFIER `:` Path `to` Path `;`
> ```

`transfer t : f to p::m;` declares an operation that makes the module `m` of
the package `p` the current owner of the generic `f`. The recipient path has
the same form as the recipient of a grant. The event `transfer t;` in the
assembly performs it. `f` keeps its owner; only its current owner changes.

Rules:

- A transfer must be declared by the current owner of the generic when the
  event runs. Another transfer, including one that already ran, is an error
  (`E_OWNER`).
- A transfer declaration that no event runs must still come from a module that
  is the current owner at some point of the assembly (`E_OWNER`).
- No loan of the generic may be active when its transfer runs (`E_BORROW`).
- After a transfer, the former current owner must not apply a contribution
  without a loan, and it must not transfer the generic (`E_OWNER`). The
  grants that it declared stay usable.
- The recipient applies its contributions without a loan. The `method`
  declarations of the generic stay in the defining module; the recipient adds
  methods only through contributions.
- Every method, grant, contribution and open obligation of the generic stays
  as it was. A grant of the recipient becomes usable only after the transfer.
- A transfer changes the current owner of a generic only. Abstract-type
  membership, abstract method contracts, ordinary functions and single
  methods have no transfer.

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
