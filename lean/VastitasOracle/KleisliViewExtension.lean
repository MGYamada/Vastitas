import VastitasOracle.KleisliViewSemantics
import VastitasOracle.FiniteMonadExtend

/-! Execution of a view's canonical extension on the public executable Core.
The selected model and the executable declaration environment both come from
the same accepted wire request. -/
namespace VastitasOracle.KleisliViewExtension

open VastitasKernel VastitasKernel.Indexed Indexed.FunctionSource Compiler
open FiniteKleisli (Context Hom Obj T triple)
open Core.Semantics

set_option maxRecDepth 4096

private theorem bind_ok {a : Except ε α} {next : α → Except ε β}
    (ok : (a >>= next) = .ok value) : ∃ x, a = .ok x ∧ next x = .ok value := by
  cases a with
  | error e => contradiction
  | ok x => exact ⟨x,rfl,ok⟩

/-- Finite discovery and sealing replace the prepared table, preserving the header declarations. -/
private theorem prepared_env {decls : Core.Declarations} {pp : PreparedProgram}
    (ok : prepareProgram source decls lifted disp excluded = .ok pp) :
    pp.input.body.declarations = decls := by
  unfold prepareProgram at ok
  obtain ⟨ordinary, fromOrdinary, rest⟩ := bind_ok ok
  have initial : ordinary.input.body.declarations = decls := by
    obtain ⟨_,_,h⟩ := bind_ok fromOrdinary
    obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
    obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok h
    cases h
    rfl
  by_cases no : source.finiteFunctions.isEmpty = true
  · simp only [no, ite_true] at rest
    cases rest
    exact initial
  · simp only [no] at rest
    obtain ⟨_,_,h⟩ := bind_ok rest
    obtain ⟨⟨_,_,_⟩,_,h⟩ := bind_ok h
    obtain ⟨⟨_,_,_⟩,_,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    obtain ⟨_,_,h⟩ := bind_ok h
    obtain ⟨⟨_,_,_⟩,_,h⟩ := bind_ok h
    cases h
    exact initial

/-- Lowering the executable pass places its input declarations in the emitted module. -/
private theorem pass_env {pp : PreparedProgram} (ok : lowerPass pp false = .ok pass) :
    pass.module.declarations = pp.input.body.declarations := by
  unfold lowerPass at ok
  simp only [Bool.false_and, Bool.false_eq_true, ite_false] at ok
  obtain ⟨⟨_,_⟩,_,h⟩ := bind_ok ok
  cases h
  rfl

/-- A named view and its underlying Monad give the same static model slot.
Every successful instantiation of the extension body at this key evaluates
to the mathematical extension in the executable Core of the same revision. -/
theorem public_extend {json : Lean.Json} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteKleisli kind schema monad⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let checked := input.checked.pureProgram.authority.headers.declarations
    let env := checked.resolved.declarations.indexed
    let module := input.checked.pureProgram.executable.core.module
    ResourceSource.Wire.RevisionMatches json input.checked ∧
      KleisliViews.selected (FiniteCategories.view env) kind owner = some monad ∧
      FiniteSort.monadOwner? env owner = some monad ∧
      ∃ base fields, ⟨schema, .kleisliSchema kind base⟩ ∈ env ∧ ⟨base, .monadSchema⟩ ∈ env ∧
        ⟨monad, .finiteMonad base fields⟩ ∈ env ∧
        ∃ m, FiniteSort.monad? env monad = some (fields, m) ∧ ∃ c : Context checked fields m,
          KleisliViewSemantics.Interpretation c ∧
          ∀ (x y : Obj m) (f : Hom c x (T c y)) (t : FiniteTemplate),
          t.inputs = [.monadHom 0 (.slot 1) (.action (.slot 2))] →
          t.result = .monadHom 0 (.action (.slot 1)) (.action (.slot 2)) →
          t.body = .monadCompose 0 (.component 0 2 true) (.monadMap 0 (.variable 0)) →
          ∀ params resultType term, t.instantiate checked.resolved.declarations
            [.monad monad, .object fields.category x.1, .object fields.category y.1] [0] =
              .ok (params, resultType, term) →
          ∀ values : Values, values 0 = some (.finiteTag (.hom fields.category x.1 (T c y).1) f.tag) →
          ∀ fuel : Nat, eval module (fuel+4) values term = some
            (.finiteTag (.hom fields.category (T c x).1 (T c y).1) ((triple c).extend f).tag) := by
  let program := input.checked.pureProgram
  let checked := program.authority.headers.declarations
  let env := checked.resolved.declarations.indexed
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed
  obtain ⟨revision, selected, base, fields, schemaMem, baseMem, monadMem, m, found, c, laws⟩ :=
    KleisliViewSemantics.public_view input member
  have viewDecl : lookup env owner = some (.finiteKleisli kind schema monad) :=
    KleisliSelection.member_lookup good.unique member
  have monadDecl : lookup env monad = some (.finiteMonad base fields) :=
    KleisliSelection.member_lookup good.unique monadMem
  have explicitOwner : FiniteSort.monadOwner? env owner = some monad := by
    unfold FiniteSort.monadOwner?
    rw [viewDecl]
    exact selected
  have model : FiniteSort.monad? env monad = some (fields, m) := by
    change Indexed.FiniteMonads.model (FiniteCategories.view env) base fields = some m at found
    simp [FiniteSort.monad?, monadDecl, found]
  have environment : program.executable.core.module.declarations = checked.resolved.declarations := by
    rw [program.executable.coreInput, pass_env program.executable.reconstructed]
    exact prepared_env program.prepareFrom
  refine ⟨revision, selected, explicitOwner, base, fields, schemaMem, baseMem, monadMem, m, model, c, laws, ?_⟩
  intro x y f t inputs output body ps res term instantiated values arg fuel
  exact FiniteMonadExtend.eval_instantiated_extend c f model t inputs output body instantiated
    program.executable.core.module environment values arg fuel

end VastitasOracle.KleisliViewExtension
