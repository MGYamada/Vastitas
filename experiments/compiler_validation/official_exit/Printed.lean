import Inputs

open VastitasKernel.LLVM VastitasQualification.ExitFixture
set_option maxRecDepth 20000

theorem printed : ExitMain.parse bytes = some ⟨target, ExitMain.statusOf value⟩ := by rfl

#print axioms printed
