# `nature`: API reference

These pages list the exports of each public module of the package `nature`,
with a one-line contract for each name. The examples of the book, and these
pages, name the package by the dependency alias `nature`. The
[README](../README.md) says what the package is for and how to depend on it,
and the chapter
[Frames and physical dimensions](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/frames-and-dimensions.md)
of the book introduces it.

A page gives the rules of no construct. Each page links the sections of the
book that hold the rules, the specifications that state the contracts with
their evidence, and the records of the decisions that admitted the module.

## The package root

The root module of the package `vastitas_nature`, the package of
[`nature/Vastitas.toml`](../Vastitas.toml), is
[`nature/src/mod.vast`](../src/mod.vast). It exports:

| Name | Kind | Contract |
| --- | --- | --- |
| `dimension` | module | The physical dimensions of the coordinates of smooth affine objects ([page](dimension.md)) |

## Pages

| Module | Package | Content |
| --- | --- | --- |
| [`nature::dimension`](dimension.md) | `vastitas_nature` | Readings, physical interpretations, base dimensions and quantity kinds |

## The check

`python3 scripts/library_docs.py` compares the table of each page with the
public items of its module: every `pub` item must have a row, and every row
must name a public item.
