import experiments.iterator_prefix.FinitePrefixDraft
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Standalone experiment audit. Neither the compiler nor the production oracle
imports this file. Check every model declaration and its transitive axioms. -/
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`IteratorPrefixDraft).isPrefixOf name then
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "unapproved axiom {axiomName} in {name}"
      count := count + 1
  if count == 0 then throwError "iterator model declarations were not loaded"
  logInfo m!"iterator prefix model: axiom audit passed for {count} declarations"
