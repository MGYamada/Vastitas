import VastitasKernel.Core
import VastitasKernel.Runtime

/-!
Proofs about the executable endpoint rules used by the Stage 0 checker.
These statements do not assert Rust parsing correctness, native code generation
correctness, or a model of arbitrary schemes and smooth schemes.
-/
namespace VastitasOracle

open VastitasKernel

theorem checkApply_sound (map point result : Ty)
    (accepted : checkApply map point = .ok result) :
    ApplyContract map point result := by
  cases map <;> cases point <;>
    simp_all [checkApply, ApplyContract]
  split at accepted <;> simp_all [pure, Except.pure]
  rename_i x y target source conditions
  obtain ⟨hxt, hxy, hxs⟩ := conditions
  exact ⟨target, y, ⟨rfl, rfl⟩, source, ⟨rfl, rfl⟩,
    accepted.symm, hxt ▸ hxy, hxt ▸ hxs⟩

theorem checkApply_result_wellFormed (map point result : Ty)
    (accepted : checkApply map point = .ok result) :
    result.WellFormed := by
  obtain ⟨x, y, s, _, _, rfl, hxy, hxs⟩ := checkApply_sound map point result accepted
  exact hxy.symm.trans hxs

def ComposeContract (g f result : Ty) : Prop :=
  ∃ x y z, f = .morphism x y ∧ g = .morphism y z ∧
    result = .morphism x z ∧ x.baseKind = y.baseKind ∧ y.baseKind = z.baseKind

theorem checkCompose_sound (g f result : Ty)
    (accepted : checkCompose g f = .ok result) :
    ComposeContract g f result := by
  cases g <;> cases f <;>
    simp_all [checkCompose, ComposeContract]
  split at accepted <;> simp_all [pure, Except.pure]
  rename_i middle target source middle' conditions
  obtain ⟨hmm, hsm, hmt⟩ := conditions
  exact ⟨source, middle', ⟨rfl, rfl⟩, target, ⟨rfl, rfl⟩,
    accepted.symm, hmm ▸ hsm, hmm ▸ hmt⟩

theorem checkCompose_result_wellFormed (g f result : Ty)
    (accepted : checkCompose g f = .ok result) :
    result.WellFormed := by
  obtain ⟨x, y, z, _, _, rfl, hxy, hyz⟩ := checkCompose_sound g f result accepted
  exact hxy.trans hyz

def PackContract (object : ObjectRef) (point result : Ty) : Prop :=
  point = .point object (.base object.baseKind) ∧ result = .pointed object.baseKind

theorem checkPack_sound (object : ObjectRef) (point result : Ty)
    (accepted : checkPack object point = .ok result) :
    PackContract object point result := by
  cases point <;> simp_all [checkPack, PackContract]
  split at accepted <;> simp_all [pure, Except.pure]

theorem checkPack_point_wellFormed (object : ObjectRef) (point result : Ty)
    (accepted : checkPack object point = .ok result) : point.WellFormed := by
  obtain ⟨rfl, _⟩ := checkPack_sound object point result accepted
  rfl

/-- A valid renaming changes names, not geometric settings or coefficient bases. -/
def BasePreserving (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  ∀ ref, (renameRef substitution ref).baseKind = ref.baseKind

/-- Each actual lookup-table entry respects the base of its formal argument. -/
def ValidSubstitution (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  ∀ pair ∈ substitution, pair.1.baseKind = pair.2.baseKind

theorem validSubstitution_basePreserving (substitution : List (ObjectRef × ObjectRef))
    (valid : ValidSubstitution substitution) : BasePreserving substitution := by
  intro ref
  cases found : substitution.find? (fun pair => pair.1 == ref) with
  | none => simp [renameRef, found]
  | some pair =>
    have matched : (pair.1 == ref) = true :=
      List.find?_some (p := fun entry : ObjectRef × ObjectRef => entry.1 == ref) found
    have same : pair.1 = ref := eq_of_beq matched
    have bases := valid pair (List.mem_of_find?_eq_some found)
    simpa [renameRef, found] using bases.symm.trans (congrArg ObjectRef.baseKind same)

theorem rename_wellFormed (substitution : List (ObjectRef × ObjectRef))
    (preserves : BasePreserving substitution) (ty : Ty) (wellFormed : ty.WellFormed) :
    (ty.rename substitution).WellFormed := by
  cases ty <;> simp_all [Ty.rename, Ty.WellFormed, BasePreserving]

theorem rename_application_contract (substitution : List (ObjectRef × ObjectRef))
    (preserves : BasePreserving substitution) (map point result : Ty)
    (contract : ApplyContract map point result) :
    ApplyContract (map.rename substitution) (point.rename substitution)
      (result.rename substitution) := by
  obtain ⟨x, y, s, rfl, rfl, rfl, hxy, hxs⟩ := contract
  refine ⟨renameRef substitution x, renameRef substitution y, renameRef substitution s,
    rfl, rfl, rfl, ?_, ?_⟩
  · exact (preserves x).trans (hxy.trans (preserves y).symm)
  · exact (preserves x).trans (hxs.trans (preserves s).symm)

theorem renamed_point_retains_target (substitution : List (ObjectRef × ObjectRef))
    (target source : ObjectRef) :
    (Ty.point target source).rename substitution =
      .point (renameRef substitution target) (renameRef substitution source) := rfl

/-- Unpacking gives the hidden object a fresh local name in the same base. -/
theorem unpacked_point_can_repack (base : BaseKind) (fresh : Nat) :
    checkPack (.local base fresh) (.point (.local base fresh) (.base base)) =
      .ok (.pointed base) := by
  simp [checkPack, ObjectRef.baseKind, pure, Except.pure]

theorem different_unpacked_names_do_not_mix (base : BaseKind) (left right : Nat)
    (different : left ≠ right) :
    checkPack (.local base left) (.point (.local base right) (.base base)) ≠
      .ok (.pointed base) := by
  simp [checkPack, ObjectRef.baseKind, Ne.symm different]

theorem checkScopeRefs_sound (allowed refs : List ObjectRef)
    (accepted : checkScopeRefs allowed refs = .ok ()) :
    ∀ ref ∈ refs, ref.InScope allowed := by
  induction refs with
  | nil => simp
  | cons ref rest ih =>
    simp only [checkScopeRefs] at accepted
    split at accepted
    · rename_i inScope
      intro other member
      simp only [List.mem_cons] at member
      obtain rfl | member := member
      · exact inScope
      · exact ih accepted other member
    · contradiction

/-- This is the exact executable scope rule called by the checker at block exits. -/
theorem checkScope_sound (allowed : List ObjectRef) (ty : Ty)
    (accepted : checkScope allowed ty = .ok ()) : ty.Scoped allowed :=
  checkScopeRefs_sound allowed ty.refs accepted

theorem fresh_unpacked_point_cannot_escape (allowed : List ObjectRef)
    (base : BaseKind) (fresh : Nat) (notBound : ObjectRef.local base fresh ∉ allowed) :
    checkScope allowed (unpackedPointType base fresh) = .error (.local base fresh) := by
  simp [checkScope, unpackedPointType, Ty.refs, checkScopeRefs, ObjectRef.InScope, notBound]

theorem repackaged_point_does_not_escape (allowed : List ObjectRef) (base : BaseKind) :
    checkScope allowed (.pointed base) = .ok () := rfl

namespace RuntimeLaws

open VastitasKernel.Runtime

theorem origin_target (object : Object) : (origin object).target = object := rfl

theorem origin_source (object : Object) :
    (origin object).source = baseObject object.base := rfl

theorem id_source (object : Object) : (idMap object).source = object := rfl

theorem id_target (object : Object) : (idMap object).target = object := rfl

theorem compose_source (g f : Morphism) : (composeMap g f).source = f.source := rfl

theorem compose_target (g f : Morphism) : (composeMap g f).target = g.target := rfl

theorem apply_target (map : Morphism) (point : Point) :
    (applyMap map point).target = map.target := rfl

theorem apply_preserves_test_object (map : Morphism) (point : Point) :
    (applyMap map point).source = point.source := rfl

theorem apply_identity (object : Object) (point : Point) (belongs : point.target = object) :
    applyMap (idMap object) point = point := by
  cases point
  simp_all [applyMap, idMap]

theorem apply_composition (g f : Morphism) (point : Point) :
    applyMap (composeMap g f) point = applyMap g (applyMap f point) := rfl

theorem pack_unpack_scheme (object : Object) (point : Point) :
    (Pointed.mk object point).scheme = object := rfl

theorem pack_unpack_point (object : Object) (point : Point) :
    (Pointed.mk object point).point = point := rfl

theorem pack_unpack_preserves_association (object : Object) (point : Point)
    (belongs : point.target = object) :
    (Pointed.mk object point).point.target = (Pointed.mk object point).scheme := belongs

end RuntimeLaws
end VastitasOracle
