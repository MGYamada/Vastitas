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
| Generic | `generic` | Yes | [Finite dispatch](../stage1a.md#declarations) |
| Method | `method` | Yes | [Finite dispatch](../stage1a.md#declarations) |
| Abstract type | `abstract type` | Yes | [Abstract types](../stage1a.md#abstract-types) |
| Subtype | `subtype` | Yes | [Abstract types](../stage1a.md#abstract-types) |
| Abstract method | `abstract method` | Yes | [Abstract method contracts](../stage1a.md#abstract-method-contracts) |
| Module | `mod` | No | [Modules and paths](../packages.md#modules-and-paths) |
| Import | `use` | No | [Modules and paths](../packages.md#modules-and-paths) |
| Indexed declaration | `indexed` | No | [Indexed source](../indexed-source.md#declarations-and-source-example), [smooth declarations](smooth-declarations.md) |
| Resource function | `resource fn` | No | [Resource programs](../storage/resource-programs.md) |
| Grant, delegation | `grant`, `delegation` | No | [Edit borrowing](../packages.md#edit-borrowing), [delegation](../packages.md#explicit-delegation) |
| Transfer | `transfer` | No | [Permanent transfer](../packages.md#permanent-transfer) |
| Contribution, assembly | `contribution`, `assembly` | No | [Edit borrowing](../packages.md#source-declarations) |

Rules:

- In [flat mode](programs.md#flat-mode), an item of a kind that the table
  marks "No" is an error (`E_UNSUPPORTED`).
- A token that begins no item where an item is expected is an error
  (`E_PARSE`).
- Items may appear in any order. An item may refer to an item that a later
  part of the program declares.

## Visibility

In manifest mode, `pub` makes an item visible outside the module that declares
it.
An item without `pub` is private to its module.
[Visibility and ownership](../packages.md#visibility-and-ownership) gives the
rules.

Rules:

- `pub` before an item is an error in flat mode (`E_UNSUPPORTED`).
- `pub` before a method, an abstract method, a subtype or an assembly is an
  error (`E_PARSE`). These items have no visibility of their own.
- A module must contain at most one assembly. A second one is an error
  (`E_DUPLICATE`).

## Names of items

Functions, generics and abstract types share one namespace, the namespace of
their module in manifest mode and of the whole program in flat mode. In
manifest mode the namespace of a module also holds its child modules and the
names that its `use` imports bind. A binding must not take a name of this
namespace, as [Scopes of bindings](statements.md#scopes-of-bindings) says.

Rules:

- Two items of the namespace with the same name are an error
  (`E_DUPLICATE`). In manifest mode, an item with the name of a child module
  or of an import of its module is an error (`E_DUPLICATE`).
- An item name must not be a [reserved name](lexical-structure.md#reserved-names)
  (`E_RESERVED`), apart from the exception for `indexed` declarations that the
  rules of that section give.
