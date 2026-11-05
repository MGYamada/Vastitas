import Lean.Elab.Command
import VastitasOracle

open Lean Elab Command

/-! # Chain-rule independence of the compiled reverse Core theorems (#623)

This file is a build check, not an assumed theorem. Build the oracle first, then
run `cd lean && lake env lean -DwarningAsError=true ../scripts/check_chain_rule_free.lean`.

The specification of compiled reverse Core states which theorems do not use
the oracle's chain rule (`SmoothCalculus.cot_compose` and the theorems built on
it). The oracle's import closure contains `SmoothCalculus` anyway, because
`SmoothReverseCore` proves its coordinate theorems in the same module. The
check is therefore on constants: it walks every constant that each listed
theorem uses, through types, values and constructors, as the axiom audit does,
and fails if one of them reaches a chain-rule theorem. Controls check that the
coordinate theorems, which use the chain rule, are found to reach it. -/
namespace VastitasChainRuleFree

/-- The chain-rule theorems of the oracle. -/
def chainRule : Array Name := #[
  `VastitasOracle.SmoothCalculus.cot_compose_of_length,
  `VastitasOracle.SmoothCalculus.cot_compose,
  `VastitasOracle.SmoothCalculus.backward_eq_cot,
  `VastitasOracle.SmoothCalculus.backward_eq_cot_saved,
  `VastitasOracle.SmoothCalculus.pullback_composite,
  `VastitasOracle.SmoothCalculus.pullback_eq_composite,
  `VastitasOracle.SmoothCalculus.Cov.pullback_comp]

/-- The theorems that the specification states without the chain rule. -/
def independent : Array Name := #[
  `VastitasOracle.SmoothJacobian.transposeApply_jacobian,
  `VastitasOracle.SmoothJacobian.jacobianStep_eq_of_output,
  `VastitasOracle.SmoothJacobian.jacobianStep_eq,
  `VastitasOracle.SmoothJacobian.registry_reverse_sound,
  `VastitasOracle.SmoothReverseCore.forwardLets_evaluates,
  `VastitasOracle.SmoothReverseCore.forwardLets_primal,
  `VastitasOracle.SmoothReverseCore.saved_function_evaluates,
  `VastitasOracle.SmoothReverseCore.saved_function_pullback,
  `VastitasOracle.SmoothReverseCore.saved_function_foreign_seed,
  `VastitasOracle.SmoothReverseCore.recomputed_function_evaluates,
  `VastitasOracle.SmoothReverseCore.recomputed_function_pullback,
  `VastitasOracle.SmoothReverseCore.saved_eq_recomputed,
  `VastitasOracle.SmoothReverseCore.site_saved_core,
  `VastitasOracle.SmoothReverseCore.site_recomputed_core,
  `VastitasOracle.SmoothReverseCore.site_differential_core,
  `VastitasOracle.SmoothReverseCore.site_saved_rewrite,
  `VastitasOracle.SmoothReverseCore.site_recomputed_rewrite,
  `VastitasOracle.SmoothReverseCore.site_differential_rewrite,
  `VastitasOracle.SmoothReverseCore.site_tape_rewrite,
  `VastitasOracle.IndexedReverseCore.validate_iff,
  `VastitasOracle.IndexedReverseCore.compiled_entry_resolves,
  `VastitasOracle.SmoothReverseCompiled.entry_well_formed,
  `VastitasOracle.SmoothReverseCompiled.compiled_saved_entry,
  `VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry,
  `VastitasOracle.SmoothReverseCompiled.compiled_saved_entry_foreign_seed,
  `VastitasOracle.SmoothReverseCompiled.compiled_entries_compute,
  `VastitasOracle.SmoothReverseCompiled.resolve_factors,
  `VastitasOracle.SmoothReverseCompiled.compileSite_term,
  `VastitasOracle.SmoothReverseCompiled.compiled_site_evaluates,
  `VastitasOracle.SmoothReverseCompiled.public_wire_entries,
  `VastitasOracle.SmoothReverseCompiled.legacy_wire_entries,
  `VastitasOracle.SmoothReverseCompiled.public_resource_entries,
  `VastitasOracle.SmoothReverseCompiled.public_pure_entry_computes]

/-- Theorems that use the chain rule; the check must find it. -/
def controls : Array Name := #[
  `VastitasOracle.SmoothReverseCore.saved_function_cot,
  `VastitasOracle.SmoothReverseCompiled.compiled_saved_entry_cot,
  `VastitasOracle.SmoothReverseCompiled.compiled_recomputed_entry_cot]

/-- Constants that a declaration refers to: its type, its value (also for
theorems and opaque constants) and the constructors of an inductive type. -/
def dependencies (info : ConstantInfo) : Array Name :=
  let used (expressions : List Expr) := expressions.foldl (fun found e => found ++ e.getUsedConstants) #[]
  match info with
  | .defnInfo v => used [v.type, v.value]
  | .thmInfo v => used [v.type, v.value]
  | .opaqueInfo v => used [v.type, v.value]
  | .inductInfo v => used [v.type] ++ v.ctors.toArray
  | info => used [info.type]

/-- Every constant reachable from `root`. -/
def reachable (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := NameSet.empty.insert root
  let mut stack := #[root]
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    let some info := env.find? name | continue
    for dependency in dependencies info do
      unless visited.contains dependency do
        visited := visited.insert dependency
        stack := stack.push dependency
  return visited

run_cmd do
  let env ← getEnv
  for name in chainRule ++ independent ++ controls do
    unless env.contains name do
      throwError "unknown constant {name}"
  for name in independent do
    let reached := reachable env name
    for rule in chainRule do
      if reached.contains rule then
        throwError "{name} uses the chain rule: it reaches {rule}"
  for name in controls do
    let reached := reachable env name
    unless chainRule.any reached.contains do
      throwError "control {name} does not reach the chain rule"
  logInfo m!"chain-rule independence: {independent.size} theorems reach none of the {chainRule.size} chain-rule theorems; the {controls.size} controls reach them"

end VastitasChainRuleFree
