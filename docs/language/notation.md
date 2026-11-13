# Notation

This chapter explains how the Vastitas Reference lays out a section and how it
writes syntax, rules and implementation notes. The
[glossary](../appendix/glossary.md) defines the terms that the Reference uses.

## Sections

A Reference section that defines a construct contains, in order:

1. a **Syntax** block, in the grammar notation below;
2. a description of the construct;
3. its rules, as a bulleted list under the label "Rules:";
4. examples.

A chapter begins with a paragraph that defines its subject, before the first
Syntax block. A section without a construct of its own, such as a section on
scopes, has no Syntax block.

## Grammar

The Reference gives the syntax of a construct as a set of productions. Each
production defines one nonterminal:

```text
Name -> Expression
```

The expression on the right uses the following notation.

| Notation | Example | Meaning |
| --- | --- | --- |
| UpperCamelCase | `UseDeclaration`, `Path` | A nonterminal, defined by its own production |
| UPPER_CASE | `IDENTIFIER`, `INTEGER_LITERAL` | A token class, such as identifiers or integer literals |
| `` `text` `` | `` `use` ``, `` `::` ``, `` `;` `` | A keyword or punctuation token, spelled as shown |
| x y | `` `use` Path `` | Sequence: x followed by y |
| x \| y | `` IDENTIFIER \| `generic` `` | Either x or y |
| x? | `` `pub`? `` | Zero or one x |
| x\* | `` ( `::` PathSegment )* `` | Zero or more x |
| x+ | `` ( `,` Type )+ `` | One or more x |
| ( x ) | `` ( `as` IDENTIFIER )? `` | Grouping |
| x except y | `IDENTIFIER_OR_KEYWORD except STRICT_KEYWORD` | Anything that x matches and y does not match; y is one item or a group |
| [`a`-`z`] | `` [`0`-`9`] `` | One character in the range, inclusive |

The postfix operators `?`, `*` and `+` apply to the item immediately before
them. A sequence binds more tightly than `|`, and `except` applies to the
single item before it. Parentheses group items. A long production continues
on the following lines, which are indented.

Productions whose name is in UPPER_CASE define token classes and other lexical
forms in terms of characters. The other productions are in terms of tokens,
and they do not mention whitespace or comments, which may separate any two
tokens. [Lexical structure](lexical-structure.md) defines the tokens.

## Syntax blocks

A Syntax block is a quoted block that starts with **Syntax** and holds the
productions in a code block labelled `text`. For example, a `use` declaration
in a package has this syntax, apart from the `pub` that may precede any
[item](items.md):

> **Syntax**
>
> ```text
> UseDeclaration -> `use` Path ( `as` IDENTIFIER )? `;`
> Path -> PathSegment ( `::` PathSegment )*
> PathSegment -> IDENTIFIER | `generic`
> ```

The block gives the form of a construct only. The rules after it say which
programs that match the form are valid. Where a production lists the words
that may stand at a place, a rule may also give the error for another word
there, as the rules of
[reverse-pass primitives](smooth-declarations.md#reverse-pass-primitives) do
for the mode of a pullback.

## Rules

The rules of a construct use these words:

- **must** and **must not** state a requirement on a program.
- **may** states a permission.
- **is an error (`E_CODE`)** states that a program that breaks the rule fails
  with a diagnostic whose code is `E_CODE`. The compiler reports the error and
  produces no executable, unless the rule says that the generated program
  checks it at run time.
- A code in parentheses after a requirement, as in "must have type `Nat`
  (`E_TYPE`)", is the code of the error for a program that breaks the
  requirement. Where the code differs between
  [flat mode and manifest mode](programs.md), the rule gives both.

In [Storage and ownership](../storage-ownership.md), **must** also states
requirements on the compiler and on its measurements, as that chapter says.

[Diagnostics](diagnostics.md) gives the form of a diagnostic, its place and
its code, and [Appendix B](../appendix/diagnostics.md) lists the codes.

## Implementation notes

A quoted block that begins with **Implementation note.** describes how the
compiler checks or implements a rule. It says which component does the work
and how:

> **Implementation note.** The Lean kernel rebuilds the package graph and
> assigns every owner. The frontend supplies no trusted owner.

An implementation note adds no rule and changes none. Readers who only want the
language can skip it.

## Status words

The words Implemented, Tested, Proved and Planned have the meanings that the
[Introduction](../index.md#what-exists-today) gives them. A claim in a
[specification](../specifications.md) has one of six
[claim statuses](../specifications.md#claim-statuses), which divide Proved by
the specification environment of the theorem and add Assumed and Not claimed.
