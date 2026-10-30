A minimal, self-contained lean4export 3.1.0 NDJSON proof-term fixture
for the Lean proposition:
```lean
theorem Vastitas.idProp : ∀ (P : Prop), P → P := fun _ h => h
```
The nodes are hand-assembled from the documented NDJSON format and are
checked against nanoda by the integration test. The header follows the
format-3.1.0 example from ammkrn/nanoda_lib; its historical Lean version
metadata is illustrative, not an attestation that this proof was exported
by that compiler. Production users provide exports generated with
`lean4export`.

See https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
and https://github.com/ammkrn/nanoda_lib (Apache-2.0).
