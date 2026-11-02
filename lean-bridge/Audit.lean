import VastitasBridge
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Require the public results as well as auditing every bridge declaration.
-- Missing imports or a namespace change must not turn this into a vacuous audit.
run_cmd do
  let env ← getEnv
  for name in #[
      `VastitasBridge.Analysis.DaleckiiKrein.hasFDerivWithinAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.hasFDerivAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.matrix_hasFDerivAt_cfc,
      `VastitasBridge.Analysis.DaleckiiKrein.matrix_fderiv_cfc_apply,
      `VastitasBridge.Analysis.DaleckiiKrein.fderiv_cfc_scalar] do
    unless env.contains name do
      throwError "missing required bridge theorem {name}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`VastitasBridge).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
      count := count + 1
  if count == 0 then
    throwError "no bridge declarations audited"
  logInfo m!"bridge axiom audit passed for {count} declarations"
