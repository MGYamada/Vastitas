# Lexical structure

The compiler reads each source file as a sequence of tokens. This chapter
defines the source text, the tokens and the words that the language reserves.

## Source text

A source file is UTF-8 text. Its lines end with LF (U+000A) or with CR LF
(U+000D U+000A). The characters in this table are **line separators** of other
conventions, which the language does not use:

| Characters | Names |
| --- | --- |
| U+000D without a following U+000A | Carriage return alone |
| U+000B, U+000C | Line tabulation, form feed |
| U+001C to U+001E | Information separators |
| U+0085, U+2028, U+2029 | Next line, line separator, paragraph separator |

**Whitespace** is any other character with the Unicode `White_Space` property.
Whitespace and comments separate tokens and have no other meaning.

Rules:

- A source file must not begin with a byte order mark (U+FEFF). A byte order
  mark is an error (`E_LEX`).
- A line separator of the table must not appear anywhere in a file, including
  comments and string literals. Each is an error (`E_LEX`).
- Outside comments and string literals, every character is ASCII or
  whitespace. Another character is an error (`E_LEX`).

## Comments

A line comment runs from `//` to the end of the line. It may contain Unicode
text, apart from the characters that the rules exclude.

Rules:

- A comment must not contain the bidirectional controls U+061C, U+200E,
  U+200F and U+202A to U+202E, or the invisible characters U+200B, U+2060 to
  U+206F and U+FEFF. Each is an error (`E_LEX`), because it can make the
  comment display differently from how the compiler reads the file.
- `/*` outside a comment is an error (`E_UNSUPPORTED`). The language has no
  block comments.

```vast
// Point p lies on the object X. ✓
fn twice(x: Int) -> Int { x + x }
```

## Identifiers

> **Syntax**
>
> ```text
> IDENTIFIER_OR_KEYWORD ->
>     ( ASCII_LETTER | `_` ) ( ASCII_LETTER | ASCII_DIGIT | `_` )*
> IDENTIFIER -> IDENTIFIER_OR_KEYWORD except STRICT_KEYWORD
> ASCII_LETTER -> [`a`-`z`] | [`A`-`Z`]
> ASCII_DIGIT -> [`0`-`9`]
> ```

An identifier names a function, a binding, a type, a module or another
declaration. Identifiers are case sensitive. They have no length limit other
than the [input limits](../appendix/limits.md#input-limits).

## Keywords

> **Syntax**
>
> ```text
> STRICT_KEYWORD -> `abstract` | `as` | `domain` | `else` | `false` | `fn`
>     | `for` | `generic` | `if` | `let` | `loop` | `method` | `mut` | `pack`
>     | `requires` | `return` | `subtype` | `true` | `type` | `unpack` | `while`
> ```

A **strict keyword** has a fixed meaning, and it is never an identifier. Four
of them, `while`, `for`, `loop` and `mut`, name constructs that the language
does not have, and `return` occurs only as an event of an
[assembly](edit-authority.md#assemblies). Other words act as keywords only at the places where a
construct's syntax spells them, and they are identifiers elsewhere. Examples
are `pub`, `use`, `mod`, `indexed`, `resource`, `scheme`, `point`, `witness`
and `fields`.

Rules:

- Where an expression begins, `return`, `while`, `for`, `loop` and `mut` are
  each an error (`E_UNSUPPORTED`). `let mut` followed by a name is an error
  (`E_UNSUPPORTED`).
- Where the syntax expects a name, `return` is an error (`E_UNSUPPORTED`), and
  `while`, `for`, `loop` and `mut` are each an error (`E_RESERVED`).
- In every other case, a strict keyword at a place where the syntax does not
  allow it is an error (`E_PARSE`). Examples are `return` at the top level of a
  file and `let fn = 1;`.
- In [manifest mode](programs.md#manifest-mode), `generic` may be a segment of
  a path, as in `std::arithmetic::generic::add`.

## Reserved names

A **reserved name** is an identifier that a declaration or a binding must not
use, apart from the exceptions that the rules give. These names are reserved:

| Names | Reserved for |
| --- | --- |
| `Nat`, `Int`, `Bool`, `Unit`, `Pair`, `Fn`, `Any`, `Number` | [Types](types.md) and [dispatch selectors](../stage1a.md#method-declarations) |
| `Scheme`, `CInfScheme`, `Point`, `Morphism`, `Pointed` | [Geometric types](geometric-types.md) |
| `QQ`, `CInfReal` | [Coefficient markers](geometric-types.md#settings-and-markers) |
| `int`, `pair`, `pair_first`, `pair_second` | [Built-in functions](expressions.md#built-in-functions) |
| `Affine`, `Base`, `origin`, `id`, `compose`, `apply`, `dimension` | [Geometric operations](geometric-types.md#operations) |
| Every name that begins with `__vastitas_` | Names that the compiler generates |
| `mod`, `use`, `pub`, `self`, `super`, in [manifest mode](programs.md#manifest-mode) | [Modules and paths](names-and-paths.md) |

Rules:

- A declaration or binding that uses a reserved name is an error
  (`E_RESERVED`).
- An `indexed` declaration may use one of the fourteen names of the geometric
  core: the names of the geometric types, the two markers and the seven
  geometric operations. A `use` without `as` that imports such a declaration
  binds that name too. This is how a package declares its own `Point` or
  `origin`, as [Indexed source](../indexed-source.md#declarations-and-source-example)
  describes.
- An expression that names an identifier beginning with `__vastitas_` is an
  error (`E_RESERVED`).

## Integer literals

> **Syntax**
>
> ```text
> INTEGER_LITERAL -> ASCII_DIGIT+
> ```

An integer literal denotes a natural number in decimal notation, without a
bound on its size. Leading zeros do not change the value: `007` denotes 7.
A literal has no sign. `-1` applies [negation](expressions.md#operator-expressions)
to the literal `1`. [Literal expressions](expressions.md#literal-expressions)
say which type a literal has.

Rules:

- A letter or `_` directly after the digits of a literal is an error
  (`E_LEX`). Literals have no digit separators and no type suffixes. The
  exceptions are `e`, `E`, `f32` and `f64`, which make a floating-point
  literal.
- `0x` or `0X` begins a hexadecimal floating-point literal. A hexadecimal
  literal without a binary exponent `p` is an error (`E_LEX`). Integer literals
  have no radix prefixes.

## Other literals

A **floating-point literal** is a sequence of digits with a decimal point, an
exponent `e` or `E`, or a suffix `f32` or `f64`, or a hexadecimal literal such
as `0x1.8p0`. A **string literal** is text between double quotes. Each is a
token.

Rules:

- A floating-point literal is valid only as the payload of `f64(…)` or
  `complex(…)` in a resource program, as
  [Explicit source contracts](../storage/resource-programs.md#explicit-source-contracts)
  describes. Elsewhere it is an error (`E_UNSUPPORTED`).
- No construct accepts a string literal. A string literal is an error
  (`E_UNSUPPORTED`).

## Punctuation

The tokens below are punctuation. The lexer reads the longest token that
matches, so `<=` is one token, not `<` followed by `=`.

| Tokens | Use |
| --- | --- |
| `+` `-` `*` `!` `&&` `\|\|` | [Operators](expressions.md#operator-expressions) |
| `==` `!=` `<` `<=` `>` `>=` | Comparisons, and `<` `>` around type arguments |
| `->` | Result types, image bindings and resource calls |
| `::` | [Paths](names-and-paths.md) |
| `<:` | [Abstract types and subtypes](../stage1a.md#abstract-types) |
| `(` `)` `{` `}` `[` `]` | Delimiters |
| `,` `:` `;` `=` | Separators |
| `.` | Ports of a [tensor network](../linalg/networks-and-packing.md) |
| `^` | Exponents in [polynomials](smooth-declarations.md#polynomial-expressions) |

Rules:

- `/` and `%` are errors (`E_UNSUPPORTED`). The language has no division and
  no remainder.
- After the type arguments of a type, such as `Pair<Int>`, the parser reads the
  token `>=` as `>` followed by `=`. `let p: Pair<Int>= pair(1, 2);` is a valid
  binding.
