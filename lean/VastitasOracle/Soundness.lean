import VastitasOracle.SourceModuleSafety
import VastitasOracle.ActivationSafety

namespace VastitasOracle
open VastitasKernel VastitasKernel.Semantics

/-- Stage 0's combined checker-soundness and type-safety result. The premise is
success of the actual public checker on decoded input IR. The conclusions relate
the input declarations/bodies to the checked terms, establish independent typing
and a strict dependency order, and give a finite typed evaluation for every
well-typed argument environment. Runtime endpoint interpretation is part of
ValueHasType and does not assume injectivity of nominal object interpretations.

This theorem does not cover parsing, JSON decoding, diagnostic coordinates,
code-generation equivalence, the Lean/C toolchain, or execution traces/costs. -/
theorem checkModule_sound (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkModule raw requireMain = .ok certified) :
    Elaboration.ModuleCorresponds raw certified.val ∧
    Typing.ModuleWellTyped certified.val ∧
    Dependency.ModuleOrdered certified.val ∧
    ∀ function ∈ certified.val.functions, ∀ world env,
      ContextHasType world env function.params →
      ∃ value, Eval certified.val.functions env function.body value ∧
        ValueHasType world value function.returnType := by
  obtain ⟨_, _, typed, ordered⟩ := checkModule_typed_and_ordered raw requireMain certified accepted
  exact ⟨Elaboration.checkModule_source_correspondence raw requireMain certified accepted,
    typed, ordered, ActivationSafety.module_total_for_arguments certified.val typed ordered⟩

end VastitasOracle
