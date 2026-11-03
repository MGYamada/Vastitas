import VastitasOracle
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr

open Lean Elab Command

/- Audit actual compiled oracle and kernel declarations, including transitive
dependencies. This file is a build check, not an assumed theorem. -/
run_cmd do
  let env ← getEnv
  let roots := #[`VastitasOracle, `VastitasKernel, `VastitasPromotion]
  let mut counts := roots.map fun _ => (0 : Nat)
  let mut privateCount : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let some owner := env.allImportedModuleNames[index.toNat]? |
      throwError "missing defining module for {name}"
    let some group := roots.findIdx? (fun root => root.isPrefixOf owner) | continue
    -- Module provenance includes private declarations and unrelated namespaces.
    -- These substitutions have no equality proof; csimp rewrites do.
    if (Lean.getExternAttrData? env name).isSome then
      throwError "unproved extern implementation in {name} from {owner}"
    if let some implementation := Lean.Compiler.getImplementedBy? env name then
      throwError "unproved implemented_by substitution in {name} from {owner}: {implementation}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name} from {owner}"
    counts := counts.set! group (counts[group]! + 1)
    if isPrivateName name then privateCount := privateCount + 1
  for index in [:roots.size] do
    unless counts[index]! > 0 do
      throwError "no declarations from required module group {roots[index]!}"
    logInfo m!"module group {roots[index]!}: {counts[index]!} declarations"
  logInfo m!"axiom audit passed for {counts.foldl (· + ·) 0} declarations ({privateCount} private)"
  -- #350's least witness must come from accessibility search, not choice.
  for name in #[`VastitasOracle.LeastFuel.least, `VastitasOracle.LeastFuel.least_spec,
      `VastitasOracle.LeastFuel.least_minimal] do
    unless env.contains name do
      throwError "missing least-fuel search declaration {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Quot.sound].contains axiomName do
        throwError "choice or unapproved axiom {axiomName} in least-fuel search {name}"
  logInfo "least-fuel search uses no Classical.choice or custom axiom"

