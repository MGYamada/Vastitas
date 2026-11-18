import AuthorityPreparation

/-! Identify the single lifted definition and its exact prepared function environment. -/
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed Indexed.FunctionSource
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

abbrev mainFunction := pureInput.source.functions[0]!.2
def mainDefinition : Definition := ⟨0,0,ExitFixture.owner,mainFunction,false,ExitFixture.owner.scope⟩
def liftedMain : Lifted := ⟨#[mainDefinition],1⟩

theorem liftMain : DispatchSource.liftMethods pureInput.source.functions preparedPure.methods preparedPure.instances = .ok liftedMain := by cbv

theorem dispatcher : preparedPure.dispatcher = .ok {} := by rfl
theorem entry : Compiler.sourceEntryValid pureInput.source = true := by rfl
theorem definitions : Compiler.validScopedDefinitions preparedPure.seeds liftedMain = true := by decide

def oneFunction : Compiler.Prepared := {
  definition := mainDefinition, context := [], parameters := [], result := .pure .int,
  paramTypes := [], resultType := .data (.pure .int) }

def compilerInput (g : Option (GeometryProfile DeclId)) (refs : List Source.Reference) : Compiler.PreparedProgram := {
  input := {
    source := pureInput.source, body := ⟨idx,accumulated,g⟩,
    prepared := #[oneFunction],
    named := ({} : Std.HashMap DeclId Nat).insert ExitFixture.owner 0, sourceCount := 1,
    dispatch := {}, excluded := preparedPure.excluded },
  initial := {references := refs} }

def readyCompiler := compilerInput (some geometry) (geometryNames.map (ref ·)).reverse

attribute [local cbv_opaque] accumulated idx

theorem register (g : Option (GeometryProfile DeclId)) (r : List Source.Reference) :
    (liftedMain.definitions.mapM (Compiler.prepareDefinition ⟨idx,accumulated,g⟩)).run {references := r} =
      .ok (#[oneFunction],{references := r}) := by
  let input : Source.Bodies.Input := ⟨idx,accumulated,g⟩
  have one : (Compiler.prepareDefinition input mainDefinition).run {references := r} =
      .ok (oneFunction,{references := r}) := by rfl
  change (#[mainDefinition].mapM (Compiler.prepareDefinition input)).run _ = _
  rw [Array.mapM_eq_mapM_toList]
  simp only [List.mapM_cons,List.mapM_nil, StateT.run_map,StateT.run_bind,one]
  rfl

theorem prepared : Compiler.prepareProgram pureInput.source accumulated liftedMain {} preparedPure.excluded = .ok readyCompiler := by
  unfold Compiler.prepareProgram
  conv => lhs; arg 1; whnf
  have budget : WorkBudget.check (liftedMain.definitions.toList.map (·.function)) = .ok () := by cbv
  have noFinite : pureInput.source.finiteFunctions = [] := rfl
  rw [budget, exportResolved, noFinite]
  simp only [bind,Except.bind,List.isEmpty_nil,ite_true]
  rw [show pureInput.source.headers.indexed = idx from rfl,register]
  cbv
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.prepared
