# Notation

This chapter explains how the Vastitas Reference writes syntax, rules and
implementation notes. The [glossary](../appendix/glossary.md) defines the terms
that the Reference uses.

## Grammar

The Reference gives the syntax of a construct as a set of productions. Each
production defines one nonterminal:

```text
Name -> Expression
```

The expression on the right uses the following notation.

| Notation | Example | Meaning |
| --- | --- | --- |
| UpperCamelCase | `UseDeclaration`, `UsePath` | A nonterminal, defined by its own production |
| UPPER_CASE | `IDENTIFIER`, `INTEGER_LITERAL` | A token class that the lexer produces |
| `` `text` `` | `` `use` ``, `` `::` ``, `` `;` `` | A keyword or punctuation token, spelled exactly as shown |
| x y | `` `use` UsePath `` | Sequence: x followed by y |
| x \| y | `` IDENTIFIER \| `generic` `` | Either x or y |
| x? | `` `pub`? `` | Zero or one x |
| x\* | `` ( `::` PathSegment )* `` | Zero or more x |
| x+ | `` ( `,` Type )+ `` | One or more x |
| ( x ) | `` ( `as` IDENTIFIER )? `` | Grouping |
| x except y | `IDENTIFIER except ReservedName` | Anything that x matches and y does not match |

The postfix operators `?`, `*` and `+` apply to the item immediately before
them. A sequence binds more tightly than `|`, and `except` applies to the
single item before it. Parentheses group items.

The productions do not mention whitespace or comments, which may separate any
two tokens.

## Syntax blocks

A section that defines a construct opens with a **Syntax** block: a quoted
block whose code is labelled `text`. For example, a `use` declaration in a
package has this syntax:

> **Syntax**
>
> ```text
> UseDeclaration -> `pub`? `use` UsePath ( `as` IDENTIFIER )? `;`
> UsePath -> PathSegment ( `::` PathSegment )*
> PathSegment -> IDENTIFIER | `generic`
> ```

The block gives the form of a construct only. The rules after it say which
programs that match the form are valid.

## Rules

The rules of a construct follow its description as a bulleted list. They use
these words:

- **must** and **must not** state a requirement on a program.
- **may** states a permission.
- **is an error (`E_CODE`)** states that the compiler rejects the input with a
  diagnostic whose code is `E_CODE`. A code that begins with `E_NATIVE_` is
  reported by the generated program when it runs.

[Appendix B](../appendix/diagnostics.md) lists the diagnostic codes and the
[format of a diagnostic line](../appendix/diagnostics.md#output-format).

## Implementation notes

A quoted block that begins with **Implementation note.** describes how the
compiler checks or implements a rule:

> **Implementation note.** The Lean kernel rebuilds the package graph and
> assigns every owner. The frontend supplies no trusted owner.

An implementation note adds no rule and changes none. Readers who only want the
language can skip it.

## Status words

The words Implemented, Tested, Proved and Planned have the meanings that the
[Introduction](../index.md#what-exists-today) gives them.
