import VastitasOracle.LiteralCoverage
import VastitasOracle.FiniteOpcodeCoverage
import VastitasOracle.ConversionCoverage
import VastitasOracle.PairCoverage
import VastitasOracle.UnaryCoverage
import VastitasOracle.BindingCoverage
import VastitasOracle.BranchCoverage
import VastitasOracle.BinaryCoverage
import VastitasOracle.StorageProgram
import Lean.Data.Json

open Lean VastitasKernel.Indexed VastitasKernel.MidIR

-- Each exported origin/opcode pair is associated with its checked local theorem.
example := @VastitasOracle.MidIR.literal_constructor_coverage
example := @VastitasOracle.MidIR.finite_tag_constructor_coverage
example := @VastitasOracle.MidIR.finite_tag_missing_rejected
example := @VastitasOracle.MidIR.finite_lookup_constructor_coverage
example := @VastitasOracle.MidIR.finite_lookup_slots
example := @VastitasOracle.MidIR.finite_lookup_wrong_sort

example := @VastitasOracle.MidIR.linked_unary_method
example := @VastitasOracle.MidIR.linked_branch_method

private def row (entry : Name × String) (proof : Name) : Json :=
  Json.mkObj [("origin", toJson entry.1.toString), ("opcode", toJson entry.2),
    ("theorem", toJson proof.toString)]

/-- Every storage ABI symbol must name the physical instruction and local
operand theorem that justify its coverage row. -/
private def storageRow (callee : StorageEffects.Callee) : Json :=
  let (origin, proof) : Name × Name := match callee with
    | .allocate => (``VastitasKernel.Storage.Native.Instruction.allocate, ``VastitasOracle.StorageProgram.allocate_operands)
    | .drop => (``VastitasKernel.Storage.Native.Instruction.drop, ``VastitasOracle.StorageProgram.drop_operands)
    | .fill => (``VastitasKernel.Storage.Native.Instruction.fill, ``VastitasOracle.StorageProgram.fill_operands)
    | .store => (``VastitasKernel.Storage.Native.Instruction.store, ``VastitasOracle.StorageProgram.store_operands)
    | .expect => (``VastitasKernel.Storage.Native.Instruction.expect, ``VastitasOracle.StorageProgram.expect_operands)
    | .copy => (``VastitasKernel.Storage.Native.Instruction.copy, ``VastitasOracle.StorageProgram.copy_operands)
    | .gemm => (``VastitasKernel.Storage.Native.Instruction.gemm, ``VastitasOracle.StorageProgram.gemm_representation)
    | .pack3 => (``VastitasKernel.Storage.Native.Instruction.pack3, ``VastitasOracle.StorageProgram.pack3_operands)
    | .regroup3 => (``VastitasKernel.Storage.Native.Instruction.regroup3, ``VastitasOracle.StorageProgram.regroup3_operands)
    | .diagonalScale => (``VastitasKernel.Storage.Native.Instruction.diagonalScale, ``VastitasOracle.StorageProgram.diagonal_scale_operands)
    | .diagonalAdjoint => (``VastitasKernel.Storage.Native.Instruction.diagonalAdjoint, ``VastitasOracle.StorageProgram.diagonal_adjoint_operands)
    | .diagonalPair => (``VastitasKernel.Storage.Native.Instruction.diagonalPair, ``VastitasOracle.StorageProgram.diagonal_pair_operands)
  row (origin, "storage." ++ callee.name) proof

def main : IO Unit := do
  let literals := literalRegistry.map fun entry => row entry ``VastitasOracle.MidIR.literal_constructor_coverage
  let finite := row finiteTagRegistryRow ``VastitasOracle.MidIR.finite_tag_constructor_coverage
  let lookup := row lookupRegistryRow ``VastitasOracle.MidIR.finite_lookup_constructor_coverage
  let conversion := row natToIntRegistryRow ``VastitasOracle.MidIR.nat_to_int_constructor_coverage
  let call := row staticCallRegistryRow ``VastitasOracle.MidIR.static_call_constructor_coverage
  let storageRows := StorageEffects.Callee.all.map storageRow
  let structural (origin proof : Name) := Json.mkObj [
    ("origin", toJson origin.toString), ("opcode", Json.null), ("theorem", toJson proof.toString)]
  let alternatives (origin : Name) (tags : List String) (proof : Name) := Json.mkObj [
    ("origin", toJson origin.toString), ("opcode", toJson tags), ("theorem", toJson proof.toString)]
  let alternativesRows := [
    alternatives ``Core.Term.binary VastitasOracle.MidIR.binaryTags ``VastitasOracle.MidIR.binary_constructor_coverage,
    alternatives ``Core.Term.unary VastitasOracle.MidIR.unaryTags ``VastitasOracle.MidIR.unary_constructor_coverage,
    alternatives ``Core.Term.pair VastitasOracle.MidIR.pairConstructionTags ``VastitasOracle.MidIR.pair_constructor_coverage,
    alternatives ``Core.Term.project VastitasOracle.MidIR.pairProjectionTags ``VastitasOracle.MidIR.projection_constructor_coverage]
  let structureRows := [
    structural ``Core.Term.branch ``VastitasOracle.MidIR.branch_constructor_coverage,
    structural ``Core.Term.variable ``VastitasOracle.MidIR.variable_constructor_coverage,
    structural ``Core.Term.scope ``VastitasOracle.MidIR.scope_constructor_coverage,
    structural ``Core.Term.ascribe ``VastitasOracle.MidIR.ascription_constructor_coverage,
    structural ``Core.Term.letE ``VastitasOracle.MidIR.let_constructor_coverage]
  IO.println (toJson (literals ++ [finite, lookup, call, conversion] ++ alternativesRows ++ structureRows ++ storageRows)).compress
