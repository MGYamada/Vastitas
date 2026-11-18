import FunctionLowering

/-! Independently establish Core typing for the entire returned module. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem moduleTyped : Indexed.Core.Typing.ModuleTyped compiledModule := by
  constructor
  · exact (Core.Typing.validDeclarations_iff accumulated).mp data
  · decide
  · simp [Core.Typing.freshSerials,compiledModule,compiledMain,Core.Typing.allocatedSerials]
  · intro f member
    have eq : f = compiledMain := List.mem_singleton.mp member
    subst f
    simp [Core.Typing.FunctionTyped,compiledMain,Core.Typing.ParametersValid,Core.Typing.HasType,
      Core.Typing.UnaryTyping,Core.Typing.Compatible,Core.Term.result,Core.Result.Valid,
      intType,Core.DataType.Valid,Core.DataType.Scoped,Core.DataType.refs]

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.moduleTyped
