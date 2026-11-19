import VastitasKernel.LLVM.ExitFunction
import VastitasOracle.MidIR
import VastitasOracle.ExactFold

set_option autoImplicit false

namespace VastitasOracle.ExitFunction
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.MidIR (Phase IntLiteral)
open LLVM.ExitFunction (Artifact Stage core)

/-- Run the designated Core entry with no arguments or prior bindings. -/
def coreEntry (m : Core.Module) (fuel : Nat) : Option Value := do
  let id ← m.main
  let f ← m.functions.find? (fun f => f.id == id)
  eval m fuel (← bindArguments f.parameters []) f.body

/-- Enter the module through its actual symbol table and nominal signature. -/
def midEntry {p : Phase} (m : VastitasKernel.MidIR.Module p) : Option Value := do
  let id ← m.entry
  let f ← m.functions[id]?
  MidIR.invoke m 1 f.target []

theorem coreLiteral (m : Core.Module) (lit : IntLiteral) (fuel : Nat) :
    eval m (fuel + 3) (fun _ => none) (.scope lit.term) = some (.integer lit.value) := by
  cases lit <;> rfl

private theorem linkedLiteral {p : Phase} {m : VastitasKernel.MidIR.Module p}
    {f : Core.Function} {key : FunctionSource.Compiler.Key} {lit : IntLiteral}
    (st : Stage m f key lit) (symbol : f.id = 0) : midEntry m = some (.integer lit.value) := by
  have index : st.entry.target.symbol = 0 :=
    (congrArg VastitasKernel.MidIR.CallTarget.symbol st.target).trans symbol
  simp [midEntry, st.linked, symbol, st.sole, MidIR.invoke, index, guard,
    MidIR.runWith_intLiteral m.env _ st.entry lit st.instructions]

/-- Both linked MidIR phases retain the full unbounded Int evaluated by the
returned Core. Only the modeled C main result projects it to an exit status.
Complete LLVM bytes, including the target, agree for every accepted input. -/
theorem correspondence {json : Lean.Json} {main : Bool} {req : ResourceSource.Wire.CheckedInput json main}
    {target : TargetHeader} (a : Artifact req target) (bytes : List UInt8)
    (parsed : ExitMain.parse bytes = some a.toModule) (fuel : Nat) :
    bytes = ExitMain.print a.toModule ∧
    coreEntry (core req) (fuel + 3) = some (.integer a.literal.value) ∧
    midEntry a.opt = some (.integer a.literal.value) ∧
    midEntry a.exe = some (.integer a.literal.value) ∧
    (ExitMain.evaluate a.toModule).toNat = (a.literal.value % 256).toNat ∧
    (ExitMain.evaluate a.toModule).toNat < 256 := by
  refine ⟨(ExitMain.parse_iff _ _).mp parsed, ?_, linkedLiteral a.optStage a.symbol,
    linkedLiteral a.exeStage a.symbol, ?_, ?_⟩
  · simp [coreEntry, a.entry, a.onlyCore, a.signature.1, bindArguments, a.body, coreLiteral]
  · simpa [ExitMain.evaluate, LLVM.ExitFunction.CheckedEntry.toModule] using ExitMain.statusOf_exact a.literal.value
  · simpa [ExitMain.evaluate, LLVM.ExitFunction.CheckedEntry.toModule] using
      (ExitMain.statusOf a.literal.value).toNat_lt_size

/-- All witnesses concern the same current request and actual checked body.
Ordered call-site keys, including mixed division operands, are the ones used
by the function revision. Each has a unique method in the protected package. -/
theorem fold_correspondence {json : Lean.Json} {main : Bool} {req : ResourceSource.Wire.CheckedInput json main}
    {target : TargetHeader} (a : LLVM.ExitFunction.FoldArtifact req target) (bytes : List UInt8)
    (parsed : ExitMain.parse bytes = some a.toModule) :
    bytes = ExitMain.print a.toModule ∧
    (∃ bound, ∀ fuel ≥ bound, coreEntry (core req) fuel = some (.integer a.literal.value)) ∧
    midEntry a.opt = some (.integer a.literal.value) ∧
    midEntry a.exe = some (.integer a.literal.value) ∧
    (ExitMain.evaluate a.toModule).toNat = (a.literal.value % 256).toNat ∧
    a.sites.map LLVM.ExitFunction.Site.key = Indexed.ExactOperators.selections req.checked.pureProgram.executable.core.module ∧
    (∀ site ∈ a.sites, VastitasKernel.MidIR.ExactFold.candidates site.selection =
        [(site.method.ordinal, site.method.result)]) ∧
    a.exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked := by
  refine ⟨(ExitMain.parse_iff _ _).mp parsed, ?_, linkedLiteral a.optStage a.symbol,
    linkedLiteral a.exeStage a.symbol, ExitMain.statusOf_exact _, a.revisionSites, fun site _ => site.method.sole, a.revision⟩
  obtain ⟨bound, observed⟩ := ExactFold.evaluates (core req) a.body
  refine ⟨bound, fun fuel enough => ?_⟩
  simp [coreEntry, a.entry, a.onlyCore, a.signature.1, bindArguments]
  exact observed fuel enough

end VastitasOracle.ExitFunction
