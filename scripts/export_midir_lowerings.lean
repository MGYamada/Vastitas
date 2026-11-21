import VastitasOracle.LiteralCoverage
import VastitasOracle.FiniteOpcodeCoverage
import Lean.Data.Json

open Lean VastitasKernel.MidIR

-- Each exported origin/opcode pair is associated with its checked local theorem.
example := @VastitasOracle.MidIR.literal_constructor_coverage
example := @VastitasOracle.MidIR.finite_tag_constructor_coverage
example := @VastitasOracle.MidIR.finite_tag_missing_rejected
example := @VastitasOracle.MidIR.finite_lookup_constructor_coverage
example := @VastitasOracle.MidIR.finite_lookup_slots
example := @VastitasOracle.MidIR.finite_lookup_wrong_sort

private def row (entry : Name × String) (proof : Name) : Json :=
  Json.mkObj [("origin", toJson entry.1.toString), ("opcode", toJson entry.2),
    ("theorem", toJson proof.toString)]

def main : IO Unit := do
  let literals := literalRegistry.map fun entry => row entry ``VastitasOracle.MidIR.literal_constructor_coverage
  let finite := row finiteTagRegistryRow ``VastitasOracle.MidIR.finite_tag_constructor_coverage
  let lookup := row lookupRegistryRow ``VastitasOracle.MidIR.finite_lookup_constructor_coverage
  IO.println (toJson (literals ++ [finite, lookup])).compress
