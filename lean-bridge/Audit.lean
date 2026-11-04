import VastitasBridge
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Require the public results as well as auditing every bridge declaration.
-- Missing imports or a namespace change must not turn this into a vacuous audit.
run_cmd do
  let env ← getEnv
  for name in #[
      `VastitasBridge.Analysis.DaleckiiKrein.fderivCandidate_eq_double_sum,
      `VastitasBridge.Analysis.DaleckiiKrein.hasFDerivWithinAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.hasFDerivAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.matrix_hasFDerivAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.matrix_fderiv_cfc_apply,
      `VastitasBridge.Analysis.DaleckiiKrein.fderiv_cfc_scalar,
      `VastitasBridge.AlgebraicGeometry.Buchberger.exists_isStandardRep,
      `VastitasBridge.AlgebraicGeometry.Buchberger.isGroebnerBasis_of_sPairReduces,
      `VastitasBridge.AlgebraicGeometry.Buchberger.IsGroebnerBasis.span_leadingTerm,
      `VastitasBridge.AlgebraicGeometry.Buchberger.IsGroebnerBasis.normalForm_unique,
      `VastitasBridge.AlgebraicGeometry.Buchberger.IsGroebnerBasis.sub_mem_iff_normalForm_eq,
      `VastitasBridge.AlgebraicGeometry.Buchberger.IsGroebnerBasis.mem_iff_normalForm_eq_zero,
      `VastitasBridge.AlgebraicGeometry.Buchberger.exists_isNormalForm,
      `VastitasBridge.AlgebraicGeometry.Buchberger.IsGroebnerBasis.span_eq,
      `VastitasBridge.AlgebraicGeometry.Buchberger.span_eq_of_cofactors,
      `VastitasBridge.AlgebraicGeometry.Buchberger.isGroebnerBasis_of_certificate,
      `VastitasBridge.AlgebraicGeometry.Buchberger.list_isGroebnerBasis_of_certificate,
      `VastitasBridge.AlgebraicGeometry.Buchberger.sPairReduces_of_normalized,
      `VastitasBridge.AlgebraicGeometry.Buchberger.degLex_lt_iff_exists,
      `VastitasBridge.AlgebraicGeometry.Kernel.compare_lt_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.canonical_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_add,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_mul,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_injective,
      `VastitasBridge.AlgebraicGeometry.Kernel.canonicalEquiv,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMvN_combination,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_sPolynomial,
      `VastitasBridge.AlgebraicGeometry.Kernel.encode_lt,
      `VastitasBridge.AlgebraicGeometry.Kernel.divide_spec,
      `VastitasBridge.AlgebraicGeometry.Kernel.normalForm_spec,
      `VastitasBridge.AlgebraicGeometry.Kernel.budgeted_divide,
      `VastitasBridge.AlgebraicGeometry.Kernel.verify_isGroebnerBasis,
      `VastitasBridge.AlgebraicGeometry.Kernel.verify_normalForm,
      `VastitasBridge.AlgebraicGeometry.Kernel.verify_normalForm_eq_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.verify_mem_iff] do
    unless env.contains name do
      throwError "missing required bridge theorem {name}"
  -- Select by defining module, as the oracle audit does: a name prefix would
  -- miss private declarations and declarations in other namespaces.
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some owner := env.allImportedModuleNames[index.toNat]? |
      throwError "missing defining module for {name}"
    unless (`VastitasBridge).isPrefixOf owner do continue
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name} from {owner}"
    count := count + 1
    if isPrivateName name then privateCount := privateCount + 1
  if count == 0 then
    throwError "no bridge declarations audited"
  logInfo m!"bridge axiom audit passed for {count} declarations ({privateCount} private)"
