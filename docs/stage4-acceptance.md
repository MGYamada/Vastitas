# Stage 4 frames and dimensions acceptance

This map links each acceptance condition of historical Stage 4 to its
implementation, positive and negative tests, oracle and bridge theorems, and
native evidence. Stage 4 is a finite, checked profile of ordered frames,
change of frame and physical dimensions over exact QQ, on top of the smooth
affine profile of Stage 3
([tracker #759](https://github.com/MGYamada/Vastitas/issues/759)). It does not
include performance: the Fast like C verdict stays with #222.

Every condition below is Planned. The rows gain their evidence as the steps
land.

## Scope and decisions

The conditions are the checklist C1–C24 of #759, which turns the Stage 4
example of the [historical roadmap](guide/historical-roadmap.md#stage-4-bundles-and-tensor-diagrams)
into executable checks. The decisions behind the profile are:

- **Exact profile.** Frame arrays and their contraction live in the exact QQ
  profile. Buffers exist only in the numerical profile; its proved contraction
  facts are cited for the roadmap's sentence on buffers, and realizing exact
  arrays in floating-point storage is outside the profile.
- **Field.** QQ only. Exact `Rat` stays inside the runtime and surfaces as
  `Pair<Int>` observations. There are no floats.
- **Frames.** Declarations of the family `Frame<X>` over smooth affine
  objects. Arrays name their frame statically through a frame index, so a
  frame mismatch is a static error. A polynomial frame carries an inverse that
  the kernel checks as a polynomial identity; the inverse of a constant frame
  is computed by the kernel and never comes from the wire.
- **Map arrays** take their rows from the reverse pass of Stage 3. There is no
  pushforward.
- **Physical dimensions** belong to `nature::dimension`. A physical
  interpretation is evidence about a `std` metric and never produces it, so no
  `std` validity depends on `nature`.
- **No monoidal model.** A certified `⊗` is outside the profile.
- **Wire.** Protocol 9 only, with no protocol 10.
- **Admission.** [ADR 0001 §11](adr/0001-mathematics-first-stdlib.md#11-ordered-frames-of-smooth-affine-objects-amendment-2026-11-13)
  admits `std::geometry::frame`, and [ADR 0002](adr/0002-nature-dimension.md)
  admits `nature::dimension`.

## Steps

| Step | Pull request | Merge |
| --- | --- | --- |
| S0: the tracker, ADR 0001 §11, ADR 0002, this map | this change | — |

## Status terms

- **Proved (oracle)** is a theorem about kernel data and runtime definitions in
  `lean/VastitasOracle/`, mathlib-free, about the checker that accepts the
  input.
- **Proved (bridge)** is a mathlib theorem in `lean-bridge/`.
- **Tested** is a regression or integration test, including native execution.
  Testing is not a proof of all inputs.
- **Planned** has no evidence yet.

## Acceptance conditions

| Row | Condition | Status |
| --- | --- | --- |
| C1 | Constant frames: kernel-computed inverse, `E_FRAME` cases, the empty frame of `Pt`, bounds | Planned |
| C2 | Polynomial frames: declared inverse checked as an identity; singular and wrong inverses rejected | Planned |
| C3 | Static frame identity: other frame, other object, fiber against array, variance (`E_ENDPOINT`) | Planned |
| C4 | Adequacy: decoding and encoding are inverse, for vectors and covectors | Planned |
| C5 | Transitions: identity, composition, inverse; no transition across objects | Planned |
| C6 | Pairing does not depend on the frame | Planned |
| C7 | One accepted map in two nonorthogonal frame pairs: the arrays differ and decode to the same map | Planned |
| C8 | The same accepted Core; the chain rule in frames | Planned |
| C9 | A point-dependent frame at two points | Planned |
| C10 | Contraction keeps endpoints; buffers cited from the numerical profile | Planned |
| C11 | Rank-deficient maps and zero-dimensional arrays | Planned |
| C12 | Gram matrices in frames and their transport | Planned |
| C13 | Frame weakening | Planned |
| C14 | Wire: protocol 9 only; forged and tampered data rejected | Planned |
| C15 | Independent reference model | Planned |
| C16 | `nature` declarations | Planned |
| C17 | `dx² + dt²` under a length and a time coordinate is rejected | Planned |
| C18 | A metric with compatible scales is accepted, with its gradient | Planned |
| C19 | Quantity kinds with equal dimensions stay distinct | Planned |
| C20 | The boundary between `std` and `nature` | Planned |
| C21 | The libraries from path packages; public names | Planned |
| C22 | The native acceptance program and its mutation test | Planned |
| C23 | Continuous integration | Planned |
| C24 | Independent whole-stage review | Planned |
