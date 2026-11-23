import VastitasOracle.MidIR
import VastitasKernel.LLVM.ExactFunction

set_option autoImplicit false

namespace VastitasOracle.ExactLibrary
open VastitasKernel LLVM.ExactLibrary VastitasKernel.MidIR
open Indexed.Core.Semantics

deriving instance ReflBEq, LawfulBEq for VastitasKernel.MidIR.Ty

abbrev slotType := Kind.type

private theorem kind_type {t : MidIR.Ty} {k : Kind} (h : Kind.ofTy t = some k) : slotType k = t := by
  cases t <;> cases h <;> rfl

def instruction : Step → Op .execution
  | .nat n => ⟨.natural n,[]⟩
  | .int n => ⟨.integer n,[]⟩
  | .apply op refs => ⟨.exactOp op,refs.map fun i => ⟨0,i⟩⟩

def block (c : Code) : Block .execution :=
  ⟨(c.params.map slotType).toArray,(c.steps.map instruction).toArray,.ret ⟨0⟩ ⟨0,c.result⟩⟩

private theorem mapM_reconstruct {α β : Type} {encode : α → Option β} {decode : β → α}
    (inverse : ∀ a b, encode a = some b → decode b = a) (xs : List α) (ys : List β)
    (h : xs.mapM encode = some ys) : ys.map decode = xs := by
  induction xs generalizing ys with
  | nil => change some [] = some ys at h; cases h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨y,ey,rest,er,r⟩ := h
    cases Option.some.inj r
    simp only [List.map_cons, inverse x y ey, ih _ er]

private theorem refs_inverse (refs : List Ref) (h : refs.all (·.block == 0) = true) :
    (refs.map (·.slot)).map (fun i => (⟨0,i⟩ : Ref)) = refs := by
  induction refs with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨b,i⟩ := r
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl,tail⟩ := h
    simp [ih tail]

/-- An accepted LLVM library reconstructs the original execution SSA block,
including parameter sorts, every operation, all operand slots and the return. -/
theorem reconstruct (target : LLVM.TargetHeader) (f : MidIR.Function .execution) (c : Code)
    (lowered : translate target f = some c) :
    c.header = target ∧ slotType c.resultType = f.result ∧ f.blocks = #[block c] := by
  simp only [translate, bind, Option.bind_eq_some_iff] at lowered
  obtain ⟨ks,hp,k,hk,h⟩ := lowered
  have output := kind_type hk
  have paramTypes := mapM_reconstruct (decode := slotType) (xs := f.params.toList) (ys := ks) (h := hp)
    (fun _ _ h => kind_type h)
  split at h <;> try contradiction
  rename_i b hb
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, checks, h⟩ := h
  split at h <;> try contradiction
  rename_i result ht
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨steps, os, _, _, hc⟩ := h
  cases Option.some.inj hc
  have ops := mapM_reconstruct (decode := instruction) (h := os) (fun op step h => by
    rcases op with ⟨code,args⟩
    dsimp only at h
    split at h <;> try contradiction
    · cases h; rfl
    · cases h; rfl
    · simp only [guard, pure] at h
      split at h <;> try contradiction
      next holds =>
        cases h
        simp [instruction, refs_inverse _ holds])
  have same : b.params = f.params := by
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, guard] at checks
    split at checks <;> simp_all
  refine ⟨rfl,output,?_⟩
  apply Array.toList_inj.mp
  rw [hb]
  simp [block, paramTypes, ops, ← same, ← ht]

/-- Foreign calls are interpreted on unbounded source values. These laws are
assumptions on their implementations, including successful literal allocation.
The C shim and the machine instruction selector remain outside the Oracle. -/
structure Runtime where
  natural : Nat → Option Value
  integer : Int → Option Value
  call : ExactOp → List Value → Option Value

structure Runtime.Exact (r : Runtime) : Prop where
  natural : ∀ n, r.natural n = some (.natural n)
  integer : ∀ n, r.integer n = some (.integer n)
  call : ∀ op args, r.call op args = Evaluation.exactValue op args

private def foreignOp (runtime : Runtime) : Step → Evaluation.SemanticOp
  | .nat n => ⟨[], fun args => if args.isEmpty then runtime.natural n else none⟩
  | .int n => ⟨[], fun args => if args.isEmpty then runtime.integer n else none⟩
  | .apply op refs => ⟨refs.map (fun i => ⟨0,i⟩), runtime.call op⟩

/-- Observe the returned value of the parsed ABI module under the supplied
runtime. Each call reads its explicit SSA arguments in order. -/
def run (runtime : Runtime) (c : Code) (args : List Value) : Option Value :=
  Evaluation.runGraph #[⟨(c.params.map slotType).toArray, (c.steps.map (foreignOp runtime)).toArray,
    .ret ⟨0⟩ ⟨0,c.result⟩⟩] args

private theorem observe_instruction (rt : Runtime) (law : rt.Exact) (env : Indexed.Environment)
    (resolve : Evaluation.Resolver) (s : Step) :
    Evaluation.observeOp resolve env (instruction s) = foreignOp rt s := by
  cases s <;> simp [Evaluation.observeOp, Evaluation.denote, instruction, foreignOp,
    law.natural, law.integer]
  exact funext fun args => (law.call _ args).symm

/-- All argument lists, including malformed ones, have the same partial
return observation at the execution graph and the modeled foreign calls. -/
theorem run_from_execution (rt : Runtime) (law : rt.Exact) (env : Indexed.Environment)
    (resolve : Evaluation.Resolver) (target : LLVM.TargetHeader) (f : MidIR.Function .execution)
    (c : Code) (lowered : translate target f = some c) (args : List Value) :
    Evaluation.runWith env f resolve args = run rt c args := by
  have graph := (reconstruct target f c lowered).2.2
  simp [Evaluation.runWith, graph, Evaluation.observeBlock, block, run, List.map_map,
    Function.comp_def, observe_instruction rt law]

theorem bytes_correspondence {json : Lean.Json} {req : ResourceSource.Wire.CheckedInput json false}
    {header : LLVM.TargetHeader} (a : LLVM.ExactFunction.Artifact req header)
    (bytes : List UInt8) (parsed : parse bytes = some a.model)
    (rt : Runtime) (law : rt.Exact) (args : List Value) :
    bytes = a.model.print ∧ a.model.valid = true ∧ a.model.header = header ∧
      slotType a.model.resultType = a.exeFn.result ∧ a.exeFn.blocks = #[block a.model] ∧
      VastitasOracle.MidIR.run a.opt.env a.optFn args = run rt a.model args ∧
      VastitasOracle.MidIR.run a.exe.env a.exeFn args = run rt a.model args ∧
      a.exe.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked := by
  have ⟨target,result,graph⟩ := reconstruct _ _ _ a.lowered
  have checked := VastitasOracle.MidIR.checked_runWith a.exe.env a.exeFn (fun _ _ => none) args
  have fromExe : VastitasOracle.MidIR.run a.exe.env a.exeFn args = run rt a.model args :=
    checked.symm.trans (run_from_execution rt law _ _ _ _ _ a.lowered _)
  have stages := (VastitasOracle.MidIR.execute_module a.opt a.exe a.exeFrom).2.2.2
  simp [a.soleExe,a.soleOpt] at stages
  have phase := congrArg (fun o : VastitasOracle.MidIR.FunctionObservation => o.apply args) stages
  exact ⟨(parse_sound parsed).2,(parse_sound parsed).1,target,result,graph,phase.symm.trans fromExe,fromExe,a.revision⟩

end VastitasOracle.ExactLibrary
