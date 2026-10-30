import VastitasOracle
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Audit actual compiled oracle and kernel declarations, including transitive
dependencies. This file is a build check, not an assumed theorem. -/
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`VastitasOracle).isPrefixOf name || (`VastitasKernel).isPrefixOf name ||
        (`VastitasPromotion).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
      count := count + 1
  logInfo m!"axiom audit passed for {count} declarations"

