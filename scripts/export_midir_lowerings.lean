import VastitasOracle.LiteralCoverage
import Lean.Data.Json

open Lean VastitasKernel.MidIR

-- Compiling this check ties the emitted rows to the universally quantified
-- theorem about the actual SSA builder and the two phase denotations.
example := @VastitasOracle.MidIR.literal_constructor_coverage

def main : IO Unit := do
  let rows := literalRegistry.map fun (origin, tag) =>
    Json.mkObj [("origin", toJson origin.toString), ("opcode", toJson tag)]
  IO.println (toJson rows).compress
