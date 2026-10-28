import VastitasKernel.Indexed

/-! Executable decision procedures for independent indexed judgments. -/
namespace VastitasKernel.Indexed.Audit
open VastitasKernel.Indexed

theorem constraintHolds_iff (env : Environment) (indices : List Index) (constraint : Constraint) :
    constraintHolds env indices constraint = true ↔ constraint.Holds env indices := by
  cases constraint <;> simp only [constraintHolds, Constraint.Holds]
  all_goals repeat' split
  all_goals try simp only [beq_iff_eq]
  all_goals grind

theorem validParents_iff (env : Environment) (ranks : List (DeclId × Nat))
    (entry : Entry) (parents implementations : List DeclId) :
    validParents env ranks entry parents implementations = true ↔
      ∀ parent ∈ parents, ∃ ps ds,
        lookup env parent = some (.classification ps ds) ∧
        (∀ id ∈ implementations, id ∈ ds) ∧ classRank ranks parent < classRank ranks entry.id := by
  simp only [validParents, List.all_eq_true]
  apply forall_congr'
  intro parent
  apply forall_congr'
  intro _
  cases h : lookup env parent with
  | none => simp
  | some declaration =>
    cases declaration <;> simp [Bool.and_eq_true, List.all_eq_true, and_assoc]

theorem validEntry_iff (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) :
    validEntry env ranks entry = true ↔ entry.Valid env ranks := by
  cases h : entry.declaration <;>
    simp [validEntry, Entry.Valid, h, Bool.and_eq_true, List.all_eq_true, validParents_iff,
      and_assoc]

theorem validEnvironment_iff (env : Environment) :
    validEnvironment env = true ↔ env.Valid := by
  simp only [validEnvironment, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    validEntry_iff, and_assoc]
  exact ⟨fun ⟨bounded, unique, declarations⟩ => ⟨bounded, unique, declarations⟩,
    fun valid => ⟨valid.bounded, valid.unique, valid.declarations⟩⟩

theorem validApplication_iff (env : Environment) (application : Application) :
    validApplication env application = true ↔ application.Valid env := by
  simp only [validApplication, Application.Valid]
  cases h : lookup env application.family with
  | none => simp
  | some declaration =>
    cases declaration <;>
      simp [Bool.and_eq_true, List.all_eq_true, constraintHolds_iff, and_assoc]

instance (env : Environment) (app : Application) : Decidable (app.Valid env) :=
  decidable_of_iff (validApplication env app = true) (validApplication_iff env app)

instance (env : Environment) : Decidable env.Valid :=
  decidable_of_iff (validEnvironment env = true) (validEnvironment_iff env)

end VastitasKernel.Indexed.Audit
