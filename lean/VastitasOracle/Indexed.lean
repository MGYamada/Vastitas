import VastitasKernel.IndexedAudit

/-! Declaration and indexed-application audits for the exact finite input.
This foundation does not yet assert public protocol-7 acceptance or evaluation. -/
namespace VastitasOracle.Indexed
open VastitasKernel.Indexed

export VastitasKernel.Indexed.Audit
  (constraintHolds_iff validParents_iff validEntry_iff validEnvironment_iff validApplication_iff)

theorem checked_environment_valid (checked : CheckedEnvironment) : checked.environment.Valid :=
  (validEnvironment_iff _).mp checked.accepted

theorem checked_application_valid (env : CheckedEnvironment) (checked : CheckedApplication env) :
    checked.application.Valid env.environment :=
  (validApplication_iff _ _).mp checked.accepted

theorem globals_fixed (substitution : List (ObjectRef × ObjectRef)) (id : DeclId) :
    renameRef substitution (.global id) = .global id := rfl

theorem application_family_fixed (app : Application) (substitution : List (ObjectRef × ObjectRef)) :
    (app.rename substitution).family = app.family := rfl

theorem scoped_local (app : Application) (allowed : List ObjectRef) (type : ObjectType) (brand : Nat)
    (scopeValid : app.Scoped allowed) (occurs : ObjectRef.local type brand ∈ app.refs) :
    ObjectRef.local type brand ∈ allowed := scopeValid _ occurs

theorem checkEnvironment_input (env : Environment) (checked : CheckedEnvironment)
    (accepted : checkEnvironment env = .ok checked) : checked.environment = env := by
  unfold checkEnvironment at accepted
  split at accepted
  · cases accepted
    rfl
  · contradiction

theorem checkApplication_input (env : CheckedEnvironment) (app : Application)
    (checked : CheckedApplication env) (accepted : checkApplication env app = .ok checked) :
    checked.application = app := by
  unfold checkApplication at accepted
  split at accepted
  · cases accepted
    rfl
  · contradiction

/-- Each real inheritance edge decreases the independently audited rank. -/
theorem parent_rank (env : Environment) (valid : env.Valid) (entry : Entry) (member : entry ∈ env)
    (parents implementations : List DeclId)
    (declaration : entry.declaration = .classification parents implementations)
    (parent : DeclId) (parentMember : parent ∈ parents) :
    classRank (classRanks env) parent < classRank (classRanks env) entry.id := by
  have entryValid := valid.declarations entry member
  simp only [Entry.Valid, declaration] at entryValid
  obtain ⟨_, _, _, _, smaller⟩ := entryValid.2.2.2.2.2 parent parentMember
  exact smaller

/-- A nonempty chain of actual class-parent edges. -/
inductive Inherits (env : Environment) : DeclId → DeclId → Prop
  | edge (entry : Entry) (member : entry ∈ env) (parents implementations : List DeclId)
      (declaration : entry.declaration = .classification parents implementations)
      (parent : DeclId) (parentMember : parent ∈ parents) : Inherits env entry.id parent
  | trans {a b c} : Inherits env a b → Inherits env b c → Inherits env a c

theorem inherits_rank (env : Environment) (valid : env.Valid) (relation : Inherits env a b) :
    classRank (classRanks env) b < classRank (classRanks env) a := by
  induction relation with
  | edge entry member parents implementations declaration parent parentMember =>
    exact parent_rank env valid entry member parents implementations declaration parent parentMember
  | trans _ _ first second => exact Nat.lt_trans second first

theorem inheritance_acyclic (env : Environment) (valid : env.Valid) (id : DeclId) :
    ¬Inherits env id id := fun cycle => Nat.lt_irrefl _ (inherits_rank env valid cycle)

end VastitasOracle.Indexed
