# Edit authority

A finite [function family](../stage1a.md#generic-declarations) consists of
one or more `fn` declarations that the compiler checks as a whole. **Edit
authority** decides which module may add methods to the family. Its defining
module holds that authority.
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

- A `fn` method outside a contribution must be in the module that defines
  its family. Naming a family from another module grants no authority to
  append a method (`E_OWNER`).
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
may win. It lists comma-separated tuples of scalar types followed by a
semicolon; `domain;` is an empty region. A grant takes effect only
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
- A delegation has no authority until a `delegate` block uses it, as
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
[`examples/packages/authority/edit-borrow`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/authority/edit-borrow)
grants the package `edit_addon` the region `(Int, Int)` of `choose`:

```vast
{{#include ../../examples/packages/authority/edit-borrow/lib/main.vast}}
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
  contribution, between applied contributions, and against the defining
  module's `fn` bodies. It does not cover an unapplied contribution.

The package `edit_addon` contributes one method:

```vast
{{#include ../../examples/packages/authority/edit-borrow/addon/main.vast}}
```

## Assemblies

> **Syntax**
>
> ```text
> AssemblyDeclaration -> `assemble` Path `{` AssemblyItem* `}`
> AssemblyItem -> BorrowBlock | ApplyStatement | `transfer` Path `;`
> BorrowBlock -> `borrow` Path ( `as` IDENTIFIER )? `{` LoanItem* `}`
> LoanItem -> ApplyStatement | `delegate` Path ( `as` IDENTIFIER )? `{` LoanItem* `}`
> ApplyStatement -> `apply` Path ( `,` Path )* `;`
> ```

Only the root module of the root package can assemble a family. Its path
resolves to the defining package, module and name, including through imports.
A second block for the same family is an error (`E_ASSEMBLY`), even through
a different alias. A family without a block receives no edits.

`borrow g { … }` activates the grant `g`. A nested `delegate d { … }`
suspends its parent loan until the closing brace. The declaration `d` must
come from the parent grant's recipient; the parent must be delegable and
cover the delegated region. Each grant, delegation, contribution and transfer
must target the enclosing family.

Inside a loan, `apply c, d;` applies the two contributions in order under
the innermost loan. Its grantee must be their defining module (`E_OWNER`).
At the top level of `assemble`, `apply` uses the current owner's authority.
A top-level `transfer t;` changes the current owner as specified by `t`.
Returning a loan keeps its edits; the current owner can still apply a repair
after the loan's closing brace and before the family's closing brace.

The frontend concatenates the blocks in source order into the protocol's
[event list](../protocol.md#scoped-edits-and-assembly). Opening a loan emits
a borrow or reborrow, its closing brace emits a return, and the closing brace
of the family emits its seal. Each return and seal points to that single brace.
The optional `as name` sets the loan's diagnostic label. An omitted label
gets a deterministic fresh name derived from the grant or delegation. The
compiler reserves explicit labels even in later blocks. An explicit label
may not be reused (`E_BORROW`).

Lean reads the edit blocks in the supplied entry file and checks that their
commands, original paths, optional labels and closing braces match the
structured records. It expands the commands and compares all events and
source spans with the trace used for method selection.

Lean checks event authority, family identity, the exclusive leaf loan,
inside-out returns, owner transfers, final seals, coverage and footprints.
It checks these even when it receives a trace that did not come from source.
Applying the same contribution twice with the same permission is one edit;
different provenance is an error (`E_PROVENANCE`). The complete expanded
trace, including implicit returns and seals, has a shared limit of 4096
events; [Appendix D](../appendix/limits.md#edit-authority) gives the other
authority limits.

The flat `assembly { … }` syntax is removed. `return`, `seal`,
`reborrow … via` and `apply … using` are not source commands in an
`assemble` block.

The root package of `edit-borrow` borrows the grant, applies the
contribution, returns the loan and seals `choose`:

```vast
{{#include ../../examples/packages/authority/edit-borrow/app/main.vast}}
```

The executable writes `base::choose(40, 2) = 42` and exits with status 0.

## Sealing

A block such as `assemble apply_twice {}` can seal a singleton function,
including one whose parameters include a `Fn` value or an indexed object.
The seal records its defining package, module and name. Sealing that
function again through an import alias is an error (`E_ASSEMBLY`).

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
- The recipient applies its contributions without a loan. The original
  `fn` bodies stay in the defining module. The recipient adds methods
  through contributions.
- Every method, grant, contribution and open obligation of the generic stays
  as it was. A grant of the recipient becomes usable only after the transfer.
- A transfer names the whole finite dispatch family. A scalar singleton can
  acquire methods under that authority. Abstract-type memberships and
  contracts remain in their defining modules.

[`examples/packages/authority/edit-authority`](https://github.com/MGYamada/Vastitas/tree/main/examples/packages/authority/edit-authority)
nests a loan through a delegation and then transfers the generic. The defining
package declares a delegable grant and a transfer:

```vast
{{#include ../../examples/packages/authority/edit-authority/base/main.vast}}
```

The recipient declares the delegation and its contributions:

```vast
{{#include ../../examples/packages/authority/edit-authority/addon/main.vast}}
```

The assembly returns the nested loan before its parent, transfers `choose` and
applies the recipient's contribution without a loan:

```vast
{{#include ../../examples/packages/authority/edit-authority/app/main.vast}}
```

The executable writes `base::choose(40, 2) + base::choose(true, true) = 44`
and exits with status 0.
