import Lean.Data.Json
import VastitasKernel.IndexedPrimitiveFamilies

/-! # The indexed primitive table for the Rust frontend

Prints `families` (`VastitasKernel/IndexedPrimitiveFamilies.lean`) as one line
of JSON, `[{"op", "algebraic", "fields": [{"name", "kind"}]}]`, in the order of
`families`, with the fields in wire order and each kind spelled by
`Source.WireKind.wire`. `scripts/check_primitive_table.py` builds the module,
runs `lake -d lean-kernel env lean scripts/primitive_table.lean` and renders
`src/primitive_table.rs` from the output; it fails when the checked-in table
differs. The script reads the registry only: it adds no declaration to the
kernel and no trusted code. -/

open Lean VastitasKernel.Indexed

private def fieldJson (field : WireField) : Json :=
  Json.mkObj [("name", Json.str field.name), ("kind", Json.str field.kind.wire)]

private def familyJson (family : PrimitiveFamily) : Json :=
  Json.mkObj [
    ("op", Json.str family.op),
    ("algebraic", Json.bool family.algebraic),
    ("fields", Json.arr (family.fields.map fieldJson).toArray)]

#eval IO.println (Json.arr (families.map familyJson).toArray).compress
