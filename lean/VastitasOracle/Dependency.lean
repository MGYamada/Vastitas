import VastitasKernel.Dependency
import Std.Data.HashSet.Lemmas

namespace VastitasOracle.Dependency
open VastitasKernel.Dependency

/-- A successful executable audit establishes an independently stated order:
all callees have already been declared and every function ID is unique. -/
theorem auditFrom_sound (entries : List Entry) (known : List Nat)
    (seen : Std.HashSet Nat)
    (represents : ∀ id, id ∈ seen ↔ id ∈ known)
    (accepted : auditFrom seen entries = true) : OrderedFrom known entries := by
  induction entries generalizing known seen with
  | nil => exact .nil known
  | cons entry rest ih =>
    simp only [auditFrom, Bool.and_eq_true,
      List.all_eq_true] at accepted
    obtain ⟨⟨fresh, dependencies⟩, restAccepted⟩ := accepted
    apply OrderedFrom.cons
    · intro member
      have present : seen.contains entry.id = true :=
        Std.HashSet.contains_iff_mem.mpr ((represents entry.id).mpr member)
      rw [present] at fresh
      contradiction
    · intro dependency member
      exact (represents dependency).mp
        (Std.HashSet.contains_iff_mem.mp (dependencies dependency member))
    · apply ih (entry.id :: known) (seen.insert entry.id) _ restAccepted
      intro id
      simp only [Std.HashSet.mem_insert, List.mem_cons, beq_iff_eq]
      rw [represents]
      simp only [eq_comm]

theorem audit_sound (entries : List Entry) (accepted : audit entries = true) :
    OrderedFrom [] entries := by
  apply auditFrom_sound entries [] {} _ accepted
  intro id
  simp

theorem auditModule_sound (module : VastitasKernel.CheckedModule)
    (accepted : auditModule module = true) : ModuleOrdered module :=
  audit_sound (entries module) accepted

/-- A proposed function cannot depend on itself or a later declaration. -/
theorem head_has_no_calls {entry : Entry} {rest : List Entry}
    (ordered : OrderedFrom [] (entry :: rest)) : entry.dependencies = [] := by
  cases ordered with
  | cons _ dependencies _ =>
    cases h : entry.dependencies with
    | nil => rfl
    | cons dependency tail =>
      have impossible := dependencies dependency (by simp [h])
      simp at impossible

end VastitasOracle.Dependency
