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
      `VastitasBridge.AlgebraicGeometry.Kernel.verify_mem_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_subst,
      `VastitasBridge.AlgebraicGeometry.Kernel.canonical_subst,
      `VastitasBridge.AlgebraicGeometry.Kernel.Verified.span_basis,
      `VastitasBridge.AlgebraicGeometry.Kernel.Verified.normalForm_eq_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.mk_surjective,
      `VastitasBridge.AlgebraicGeometry.Kernel.verified_of_validAffine,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_mk,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_compose,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_subst,
      `VastitasBridge.AlgebraicGeometry.Kernel.specMap_compose,
      `VastitasBridge.AlgebraicGeometry.Kernel.images_eq_iff,
      `VastitasBridge.AlgebraicGeometry.Kernel.MorphismValid.bridge,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_triangle,
      `VastitasBridge.AlgebraicGeometry.Kernel.structureValid_bridge,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.relationIdeal_dual,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.epsilon_ne_zero,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.epsilon_sq,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.p_ne_q,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.closedPoint_comp,
      `VastitasBridge.AlgebraicGeometry.Kernel.DualNumbers.spec_base_eq,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_embed,
      `VastitasBridge.AlgebraicGeometry.Kernel.toMv_var,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.equivAway,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.equivAway_comp_toL,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.range_comap_toL,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.certificate_of_checkConstruction,
      `VastitasBridge.AlgebraicGeometry.Kernel.specMap_preimage_basicOpen,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_identity,
      `VastitasBridge.AlgebraicGeometry.Kernel.pullbackHom_inverse,
      `VastitasBridge.AlgebraicGeometry.Kernel.equivOfImages,
      `VastitasBridge.AlgebraicGeometry.Kernel.isoValid_bridge,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.isPushout,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.isPullback,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.isoTensor,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.specIsoPullback,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.desc_unique,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.pairHom_X,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.specMap_pair,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.certificate_of_checkConstruction,
      `VastitasBridge.AlgebraicGeometry.Kernel.validAffine_of_affineData,
      `VastitasBridge.AlgebraicGeometry.Kernel.validAffine_bindings_canonical,
      `VastitasBridge.AlgebraicGeometry.Kernel.validAffine_structureImages_canonical,
      `VastitasBridge.AlgebraicGeometry.Kernel.validAffine_structure,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.checkConstruction_localization_element,
      `VastitasBridge.AlgebraicGeometry.Kernel.PrincipalOpen.accepted,
      `VastitasBridge.AlgebraicGeometry.Kernel.Fiber.accepted,
      `VastitasBridge.Differential.pderiv_aeval,
      `VastitasBridge.Differential.hasFDerivAt_eval,
      `VastitasBridge.Differential.hasFDerivAt_eval_pi,
      `VastitasBridge.Differential.npow_eq_pow,
      `VastitasBridge.Differential.evalAt_eq_eval,
      `VastitasBridge.Differential.evalAt_eq_eval_evalPoint,
      `VastitasBridge.Differential.toMv_partial,
      `VastitasBridge.Differential.canonical_partial,
      `VastitasBridge.Differential.wellFormed_iff,
      `VastitasBridge.Differential.toMv_compose,
      `VastitasBridge.Differential.imageFamily_compose,
      `VastitasBridge.Differential.WellFormed.compose,
      `VastitasBridge.Differential.cot_getD,
      `VastitasBridge.Differential.apply_compose,
      `VastitasBridge.Differential.cot_compose,
      `VastitasBridge.Differential.denote_wellFormed,
      `VastitasBridge.Differential.eval_denote,
      `VastitasBridge.Differential.backward_eq_cot,
      `VastitasBridge.Differential.backward_eq_cot_saved,
      `VastitasBridge.Differential.pullback_composite,
      `VastitasBridge.Differential.pullback_eq_composite,
      `VastitasBridge.Differential.smoothEqual_iff,
      `VastitasBridge.Differential.pullback_comp,
      `VastitasBridge.Differential.Cov.reverse_eq_pullback,
      `VastitasBridge.Differential.hasFDerivAt_realProgram,
      `VastitasBridge.Differential.realProgram_realPoint,
      `VastitasBridge.Differential.reverse_covector_eq_comp_fderiv,
      `VastitasBridge.Differential.pullback_eq_fderiv_adjoint,
      `VastitasBridge.Differential.pullback_covector_eq_comp_fderiv,
      `VastitasBridge.Differential.pullback_getD_eq_fderiv_adjoint] do
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
