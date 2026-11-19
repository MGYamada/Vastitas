import VastitasKernel.ResourceProtocol
import VastitasOracle.IndexedAuthority
import VastitasOracle.IndexedSource

/-! Structural guarantees for the explicit legacy syntax export, on the same
declarations accepted by the public checker `ResourceSource.Wire.check`. These
are not whole-source evaluation, general geometric mathematics or
native-toolchain refinement. -/
namespace VastitasOracle.GeometryCompatibility
open VastitasKernel VastitasKernel.Indexed

theorem checked_profile {program : Source.Program} (checked : Source.CheckedDeclarations program)
    (profile : GeometryProfile DeclId) (selected : checked.resolved.geometry = some profile) :
    checked.resolved.declarations.Valid ∧ profile.valid checked.resolved.declarations = true := by
  refine ⟨Core.Typing.validDeclarations_iff _ |>.mp checked.accepted, ?_⟩
  simpa [selected] using checked.geometryAccepted

theorem settings_distinct {env : Core.Declarations} {profile : GeometryProfile DeclId}
    (accepted : profile.valid env = true) : profile.scheme.marker ≠ profile.smooth.marker := by
  simp only [GeometryProfile.valid, Bool.and_eq_true, bne_iff_ne] at accepted
  exact accepted.1.1.1.1.1.1

theorem setting_contracts {env : Core.Declarations} {profile : GeometryProfile DeclId}
    (accepted : profile.valid env = true) (base : BaseKind) : (profile.setting base).valid env profile = true := by
  simp only [GeometryProfile.valid, Bool.and_eq_true] at accepted
  cases base
  · exact accepted.1.1.1.2
  · exact accepted.1.1.2

/-- The base-valued package and its origin use the same canonical global and
the same declared point family. A marker is never substituted for that object. -/
theorem origin_and_package {env : Core.Declarations} {profile : GeometryProfile DeclId}
    (accepted : profile.valid env = true) (base : BaseKind) :
    env.primitive? (profile.setting base).origin =
      some (.origin (profile.setting base).objectType profile.point (profile.setting base).baseObject) ∧
    env.package? (profile.package base) = some ⟨(profile.setting base).objectType,
      [⟨profile.point, [.witness, .global (profile.setting base).baseObject]⟩]⟩ := by
  have contract := setting_contracts accepted base
  simp only [GeometrySetting.valid, Bool.and_eq_true, beq_iff_eq] at contract
  exact ⟨contract.1.1.1.2, contract.2⟩

theorem prepared_profile {program : FunctionSource.Program} {env : Core.Declarations}
    {lifted : FunctionSource.Lifted} {dispatch : FunctionSource.Compiler.DispatchInput}
    {excluded : Std.HashSet Nat} {prepared : FunctionSource.Compiler.PreparedProgram}
    (lowered : FunctionSource.Compiler.prepareProgram program env lifted dispatch excluded = .ok prepared) :
    ∃ references, (Source.resolveGeometry program.headers env).run [] =
      .ok (prepared.input.body.geometry, references) := by
  unfold FunctionSource.Compiler.prepareProgram at lowered
  simp only [bind, Except.bind] at lowered
  split at lowered
  · contradiction
  · rename_i ordinary preparedOrdinary
    have exportProfile : ∃ refs, (Source.resolveGeometry program.headers env).run [] =
        .ok (ordinary.input.body.geometry, refs) := by
      change (FunctionSource.WorkBudget.check (lifted.definitions.toList.map (·.function)) >>= _) =
        .ok ordinary at preparedOrdinary
      simp only [bind, Except.bind] at preparedOrdinary
      repeat' (split at preparedOrdinary <;> try contradiction)
      cases preparedOrdinary
      exact ⟨_, by assumption⟩
    repeat' (split at lowered <;> try contradiction)
    all_goals cases lowered; exact exportProfile

theorem lowered_profile {program : Source.Program} {resolved : Source.Resolved}
    (lowered : Source.lower program = .ok resolved) :
    ∃ references, (Source.resolveGeometry program resolved.declarations).run [] =
      .ok (resolved.geometry, references) := by
  simp only [Source.lower, bind, Except.bind] at lowered
  -- Every elaboration step before the geometry export either fails or passes on.
  repeat' (split at lowered <;> try contradiction)
  cases lowered
  exact ⟨_, by assumption⟩

/-- The compiler of the accepted request's pure program uses the profile that
its declarations selected. -/
theorem compiler_uses_checked_profile {json : Lean.Json}
    (input : ResourceSource.Wire.CheckedInput json requireMain) :
    input.checked.pureProgram.compiler.input.body.geometry =
      input.checked.pureProgram.authority.headers.declarations.resolved.geometry := by
  obtain ⟨leftRefs, left⟩ := prepared_profile input.checked.pureProgram.prepareFrom
  obtain ⟨rightRefs, right⟩ := lowered_profile input.checked.pureProgram.authority.headers.declarations.lowered
  rw [left] at right
  exact (Prod.mk.inj (Except.ok.inj right)).1

/-- This declaration certificate belongs to the exact decoded request and the
actual authority/Fn/dispatch checker result of its pure program, not a
parallel model. -/
theorem wire_profile {json : Lean.Json} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (profile : GeometryProfile DeclId)
    (selected : input.checked.pureProgram.authority.headers.declarations.resolved.geometry = some profile) :
    ResourceSource.Wire.program json = .ok input.input ∧
    AuthoritySource.checkProgram input.input.pureProgram (requireMain && input.input.entry.isNone) =
      .ok input.checked.pureProgram ∧
    profile.valid input.checked.pureProgram.authority.headers.declarations.resolved.declarations = true ∧
    Core.Typing.ModuleTyped input.checked.pureProgram.executable.lowered.module := by
  exact ⟨input.decoded, input.checked.pureAccepted,
    (checked_profile input.checked.pureProgram.authority.headers.declarations profile selected).2,
    (IndexedAuthority.both_passes input.checked.pureProgram).2.1⟩

end VastitasOracle.GeometryCompatibility
