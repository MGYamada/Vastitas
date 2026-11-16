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
[`nature/lib.vast`](../lib.vast). It exports:

| Name | Kind | Contract |
| --- | --- | --- |
| `dimension` | re-export | The root module of the package `vastitas_dimension` of [`nature/src/dimension/`](../src/dimension), the dependency `dimension_library`: the physical dimensions of the coordinates of smooth affine objects ([page](dimension.md)) |
| `model` | re-export | The root module of the package `vastitas_model` of [`nature/src/model/`](../src/model), the dependency `model_library`: the physical models of `std` fields ([page](model.md)) |
| `errorbar` | re-export | The root module of the package `vastitas_errorbar` of [`nature/src/errorbar/`](../src/errorbar), the dependency `errorbar_library`: calibrations, datasets and their comparisons with a model ([page](errorbar.md)) |

The re-exports keep the owners of the declarations: `nature::dimension::Length`
and a path to `Length` through a direct dependency on `nature/src/dimension`
name one declaration.

## Pages

| Module | Package | Content |
| --- | --- | --- |
| [`nature::dimension`](dimension.md) | `vastitas_dimension` | Readings, physical interpretations, base dimensions and quantity kinds |
| [`nature::model`](model.md) | `vastitas_model` | Models of `std` fields: their readings, conventions, preparations, observables, predictions and regimes |
| [`nature::errorbar`](errorbar.md) | `vastitas_errorbar` | Calibrations, datasets and their recorded comparisons with a model |

## The check

`python3 scripts/library_docs.py` compares the table of each page with the
public items of its module: every `pub` item must have a row, and every row
must name a public item.
