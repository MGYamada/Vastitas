import VastitasOracle.LiteralCoverage
import VastitasOracle.FiniteOpcodeCoverage
import VastitasOracle.ConversionCoverage
import VastitasOracle.PairCoverage
import VastitasOracle.BindingCoverage
import Lean.Data.Json

open Lean VastitasKernel.Indexed VastitasKernel.MidIR

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
  let conversion := row natToIntRegistryRow ``VastitasOracle.MidIR.nat_to_int_constructor_coverage
  let call := row staticCallRegistryRow ``VastitasOracle.MidIR.static_call_constructor_coverage
  let binding (origin proof : Name) := Json.mkObj [
    ("origin", toJson origin.toString), ("opcode", Json.null), ("theorem", toJson proof.toString)]
  let alternatives (origin : Name) (tags : List String) (proof : Name) := Json.mkObj [
    ("origin", toJson origin.toString), ("opcode", toJson tags), ("theorem", toJson proof.toString)]
  let pairs := [
    alternatives ``Core.Term.pair VastitasOracle.MidIR.pairConstructionTags ``VastitasOracle.MidIR.pair_constructor_coverage,
    alternatives ``Core.Term.project VastitasOracle.MidIR.pairProjectionTags ``VastitasOracle.MidIR.projection_constructor_coverage]
  let bindings := [
    binding ``Core.Term.variable ``VastitasOracle.MidIR.variable_constructor_coverage,
    binding ``Core.Term.scope ``VastitasOracle.MidIR.scope_constructor_coverage,
    binding ``Core.Term.ascribe ``VastitasOracle.MidIR.ascription_constructor_coverage,
    binding ``Core.Term.letE ``VastitasOracle.MidIR.let_constructor_coverage]
  IO.println (toJson (literals ++ [finite, lookup, call, conversion] ++ pairs ++ bindings)).compress
