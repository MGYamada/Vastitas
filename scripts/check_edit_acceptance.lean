import VastitasOracle.EditAcceptance

/-! Compile-time regressions for the composition boundary. Executable forged-IR
cases stay in the existing EditRegression and TypeAuditRegression suites. -/
namespace VastitasOracle.EditBorrowing.Regression
open VastitasKernel VastitasKernel.Edit

-- Proofs are indexed by the complete decoded input, policy, assembly and Core.
-- These attempts must fail even when a caller has another well-typed Core.
example (program otherProgram : Namespace.Program) (requireMain _otherPolicy : Bool)
    (certified otherCore : CertifiedModule)
    (assembled _otherAssembly : Assembled program.indexed)
    (_foreignAssembly : Assembled otherProgram.indexed)
    (_otherTyped : Typing.ModuleWellTyped otherCore.val)
    (evidence : FiniteEditAcceptance program requireMain certified assembled) :
    FiniteEditAcceptance program requireMain certified assembled := by
  fail_if_success
    have : FiniteEditAcceptance otherProgram requireMain certified _foreignAssembly := evidence
  fail_if_success
    have : FiniteEditAcceptance program _otherPolicy certified assembled := evidence
  fail_if_success
    have : FiniteEditAcceptance program requireMain certified _otherAssembly := evidence
  fail_if_success
    have : FiniteEditAcceptance program requireMain otherCore assembled := evidence
  exact evidence

-- A genuinely different returned Core is impossible for this input and policy,
-- even if a caller constructs another assembly candidate and annotation subtype.
example (program : Namespace.Program) (requireMain : Bool)
    (certified otherCore : CertifiedModule)
    (accepted : checkEditProgram program requireMain = .ok certified)
    (different : certified.val ≠ otherCore.val) :
    ¬ ∃ assembled : Assembled program.indexed,
      FiniteEditAcceptance program requireMain otherCore assembled := by
  obtain ⟨assembled, evidence⟩ := checkEditProgram_finite_acceptance program requireMain certified accepted
  rintro ⟨otherAssembly, otherEvidence⟩
  exact different (congrArg Subtype.val (evidence.unique otherEvidence).2)

-- Rejection cannot be bypassed by supplying a fabricated success certificate.
example (program : Namespace.Program) (requireMain : Bool) (diagnostic : Diagnostic)
    (rejected : checkEditProgram program requireMain = .error diagnostic) :
    ¬ ∃ (certified : CertifiedModule) (assembled : Assembled program.indexed),
      FiniteEditAcceptance program requireMain certified assembled := by
  rintro ⟨certified, assembled, evidence⟩
  have impossible := rejected.symm.trans evidence.accepted
  cases impossible

end VastitasOracle.EditBorrowing.Regression
