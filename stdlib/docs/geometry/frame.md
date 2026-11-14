# `std::geometry::frame`

- Module: `std::geometry::frame`
- Package: `vastitas_geometry`, the package of
  [`stdlib/src/geometry/Vastitas.toml`](../../src/geometry/Vastitas.toml), which
  `vastitas_std` re-exports as `std::geometry`
- Source: [`stdlib/src/geometry/frame/mod.vast`](../../src/geometry/frame/mod.vast)

The module declares the families of the ordered frames of the smooth affine
objects of [`std::geometry::smooth::affine`](smooth/affine.md). A frame of a
smooth affine object `X` is a global frame of the tangent bundle of `X`: an
ordered basis of every tangent fiber, given by its columns in the coordinate
frame of `X`. The families index the frames of an object, the arrays of
vectors and covectors in a frame, and the matrices of linear maps between the
fibers of two frames.

The module declares the families only. A frame and each frame primitive name
one frame, so the application declares them, as it declares `flat` and
`sharp` with their metric; the library declares no frame, and no frame is a
default. Frames, objects and variance are static, and points are values at
run time.

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `Frame<X>` | family | `frame`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the frames of the smooth affine object `X` |
| `Coords<b>` | family | `frame_vector`, over `Frame`: the arrays of vectors in the frame `b`, each with its point, and the failure value |
| `CoCoords<b>` | family | `frame_covector`, over `Frame`: the arrays of covectors in the coframe dual to `b`, each with its point, and the failure value |
| `FrameMap<b, c>` | family | `frame_map`, over `Frame` twice: the matrices of linear maps from the fibers of `b` to those of `c`, with both points, and the failure value |

## Use

[`examples/packages/stdlib-frames/main.vast`](../../../examples/packages/stdlib-frames/main.vast),
which `tests/examples.rs` builds and runs, declares frames of its plane and
the primitives that name them, such as:

- `indexed frame b: Frame<Plane> = columns((1, 0), (1, 2));`
- `indexed primitive to_b = frame_encode(Tangent, Coords, frame = b);`
- `indexed primitive b_to_e = frame_transition(Smooth, FrameMap, source = b, target = e);`

It encodes, decodes and changes frames, reads the matrix of a map, and prints
`42`.
[`examples/packages/frames-and-dimensions/`](../../../examples/packages/frames-and-dimensions),
which `tests/frames_dimensions.rs` builds, runs and mutates, uses `Coords`,
`CoCoords` and `FrameMap` across several frames and prints `42`.
`tests/stdlib_frames.rs` runs an application that declares frames on its own
objects. The book chapter
[Frames and physical dimensions](https://github.com/MGYamada/Vastitas/blob/main/docs/guide/frames-and-dimensions.md)
introduces frames.

## Rules and proofs

- [Frames](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md):
  [frame matrices](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#frame-matrices),
  [the frame profile](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#the-frame-profile),
  [frame declarations](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#frame-declarations),
  [encoding and decoding](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#encoding-and-decoding),
  [map arrays and transitions](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#map-arrays-and-transitions),
  [operand checks](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#operand-checks)
  and [the scope](https://github.com/MGYamada/Vastitas/blob/main/docs/language/frames.md#scope-of-frames).
- The specification [std::geometry::frame](https://github.com/MGYamada/Vastitas/blob/main/docs/spec/std-geometry-frame.md):
  static frames, adequacy, transitions, change of frame and pairing, with
  their evidence.
- [Frames and physical dimensions](https://github.com/MGYamada/Vastitas/blob/main/docs/verification.md#frames-and-physical-dimensions):
  what is proved and what is tested.
- [ADR 0001 §11](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#11-ordered-frames-of-smooth-affine-objects-amendment-2026-11-13):
  [contract and jurisdiction](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#contract-and-jurisdiction-1),
  [laws](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#laws-1)
  and [the public-name audit](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0001-mathematics-first-stdlib.md#compatibility-and-public-name-audit-1).
