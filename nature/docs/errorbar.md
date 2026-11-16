# `nature::errorbar`

- Module: `nature::errorbar`
- Package: `vastitas_errorbar`, the package of
  [`nature/src/errorbar/Vastitas.toml`](../src/errorbar/Vastitas.toml), which
  depends on `std`. The root of `vastitas_nature` re-exports it as
  `nature::errorbar`.
- Source: [`nature/src/errorbar/mod.vast`](../src/errorbar/mod.vast)

The module declares the data and the uncertainties of the finite profile of
historical Stage 6, which ADR 0002 admits as `nature::errorbar`. On the
smooth affine object `X` of a [model](model.md):

- a calibration gives measured values, each an exact value with a standard
  uncertainty, to some coordinates of `X`, with the method of evaluation
  (type A or type B), a reference and a revision; its fingerprint is the
  kernel's digest of its content;
- a dataset of a model under a calibration has one coverage factor `k` and at
  most 64 points (`datasetPoints`): the values of the other coordinates and a
  measured value of the observable; with the calibrated values, every point
  lies on the chart `D(g)` of the branch of the model's prediction, and a
  point off it is `E_ERRORBAR`, whatever the closed form of the average;
- a comparison records a dataset, the fingerprint of its calibration and a
  verdict, consistent or inconsistent.

The kernel evaluates the model's prediction exactly at each point and
recomputes the verdict: a point is consistent when
`(prediction − value)² ≤ k²·(u² + Σ (∂prediction)²·u_c²)`. A wrong verdict is
`E_ERRORBAR`. A comparison whose calibration changed is stale (`E_STALE`),
and the diagnostic names the current fingerprint. The propagation is first
order and the uncertainties are uncorrelated; both are assumptions of a
comparison. An uncertainty is physical: it never means the rounding error or
the enclosure of a numerical method. Calibrations, datasets and comparisons
change no value, no validity and no generated code of a `std` declaration.

The fingerprint is `fnv1a64:` and 16 hexadecimal digits: the FNV-1a digest
of the canonical content of the calibration, its calibrated coordinates in
the order of the coordinates of the object with their values and
uncertainties, its method, its reference and its revision.

The module declares the families only; the application declares its
calibrations, datasets and comparisons. The source syntax of these
declarations and the tested example come with the later steps of the Stage 6
tracker [#841](https://github.com/MGYamada/Vastitas/issues/841).

## Exports

| Name | Kind | Contract |
| --- | --- | --- |
| `Calibration<X>` | family | `calibration`, over `CInfAffine` of `std::geometry::smooth::affine`, with `canonical(0)`: the calibrations of coordinates of the smooth affine object `X`, each with its measured values, method, reference and revision |
| `Dataset<X>` | family | `dataset`, over `CInfAffine`, with `canonical(0)`: the datasets of a model on `X` under a calibration, each with its coverage factor and at most 64 points |
| `Comparison<X>` | family | `comparison`, over `CInfAffine`, with `canonical(0)`: the recorded comparisons of a dataset on `X` with its model, each with the fingerprint of its calibration and a verdict that the kernel recomputes |

## Rules and proofs

- [ADR 0002](https://github.com/MGYamada/Vastitas/blob/main/docs/adr/0002-nature-dimension.md):
  the responsibility boundary of `nature`, its admission test, and the
  amendment that admits `nature::errorbar`.
- The Stage 6 tracker [#841](https://github.com/MGYamada/Vastitas/issues/841):
  the acceptance conditions and the delivery of the module.
- [Appendix D, Limits](https://github.com/MGYamada/Vastitas/blob/main/docs/appendix/limits.md#physical-models-and-data):
  the bound `datasetPoints` on the points of a dataset.
