# Items

An **item** is a declaration at the top level of a source file or of a module.
Functions, generics and modules are items. Statements and expressions occur
only inside the bodies of items.

> **Syntax**
>
> ```text
> Item -> `pub`? VisibleItem | HiddenItem
> VisibleItem -> Function | GenericDeclaration | AbstractTypeDeclaration
>     | ModuleDeclaration | UseDeclaration | IndexedDeclaration | ResourceFunction
>     | GrantDeclaration | DelegationDeclaration | TransferDeclaration
>     | ContributionDeclaration
> HiddenItem -> MethodDeclaration | AbstractMethodDeclaration | SubtypeDeclaration
>     | AssemblyDeclaration
> ```

## Kinds of items

| Item | Begins with | Flat mode | Rules |
| --- | --- | --- | --- |
| Function | `fn` | Yes | [Functions](functions.md) |
| Generic | `generic` | Yes | [Generic declarations](../stage1a.md#generic-declarations) |
| Method | `method` | Yes | [Method declarations](../stage1a.md#method-declarations) |
| Abstract type | `abstract type` | Yes | [Abstract types](../stage1a.md#abstract-types) |
| Subtype | `subtype` | Yes | [Abstract types](../stage1a.md#abstract-types) |
| Abstract method | `abstract method` | Yes | [Abstract methods](../stage1a.md#abstract-methods) |
| Module | `mod` | No | [Module declarations](modules.md#module-declarations) |
| Import | `use` | No | [`use` declarations](modules.md#use-declarations) |
| Indexed declaration | `indexed` | No | [Indexed declarations](../indexed-source.md) |
| Resource function | `resource fn` | No | [Resource programs](../storage/resource-programs.md) |
| Grant, delegation | `grant`, `delegation` | No | [Grants and delegations](edit-authority.md#grants-and-delegations) |
| Transfer | `transfer` | No | [Transfers](edit-authority.md#transfers) |
| Contribution | `contribution` | No | [Contributions](edit-authority.md#contributions) |
| Assembly | `assembly` | No | [Assemblies](edit-authority.md#assemblies) |

`IndexedDeclaration` stands for every declaration that begins with `indexed`.
[Indexed declarations](../indexed-source.md) gives its production and says
which chapter has the rules of each kind of declaration.

Rules:

- In [flat mode](programs.md#flat-mode), an item of a kind that the table
  marks "No" is an error (`E_UNSUPPORTED`).
- A token that begins no item where an item is expected is an error
  (`E_PARSE`).
- Items may appear in any order. An item may refer to an item that a later
  part of the program declares.

This program of flat mode has eight items of six kinds: an abstract type,
two subtypes, a generic, an abstract method, two methods and a function:

```vast
{{#include ../../examples/abstract-contracts.vast}}
```

The executable prints `42`.

## Visibility

In manifest mode, `pub` makes an item public, and an item without `pub` is
private. [Visibility](names-and-paths.md#visibility) says where public and
private items are visible.

Rules:

- `pub` before an item is an error in flat mode (`E_UNSUPPORTED`).
- `pub` before a method, an abstract method, a subtype or an assembly is an
  error (`E_PARSE`). These items have no visibility of their own.

The root module of this package has three items: a module, an import and a
function. `pub` makes `increment` public, so that the root module may import
it:

```vast
{{#include ../../examples/packages/inline-module/main.vast}}
```

The executable prints `42`.

## Names of items

Every item that has a name shares one namespace with the other items of its
module: functions, resource functions, generics, abstract types, `indexed`
declarations, grants, delegations, transfers and contributions. In flat mode
the namespace holds the items of the whole program. In manifest mode the
namespace of a module also holds its child modules, the names that its `use`
declarations bind, and the dependency aliases of its package. Methods, abstract
methods, subtypes and assemblies have no name of their own.

Rules:

- Two names of one namespace must differ. Equal names are an error
  (`E_DUPLICATE`).
- A binding must not take a name of the namespace of its module, as
  [Scopes of bindings](statements.md#scopes-of-bindings) says.
- [Reserved names](lexical-structure.md#reserved-names) says which names an
  item must not have.
