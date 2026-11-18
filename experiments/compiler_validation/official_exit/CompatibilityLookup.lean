import NamespaceValidation

namespace VastitasQualification.CompatLookup
open VastitasKernel
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def owner (scope : Namespace.Scope) (name : String) : Namespace.Owner := ⟨scope, name⟩
def target (scope : Namespace.Scope) (name : String) : Namespace.Target := ⟨owner scope name, .indexedDeclaration, true⟩

theorem indexLookup (xs : List Namespace.Target) (o : Namespace.Owner) :
    (Namespace.ownerIndex xs)[o]? = (xs.find? fun t => t.owner == o) := by
  induction xs with
  | nil => simp [Namespace.ownerIndex]
  | cons x xs ih =>
    change ((Namespace.ownerIndex xs).insert x.owner x)[o]? = _
    by_cases same : x.owner = o
    · simp [same]
    · simp [Std.HashMap.getElem?_insert,beq_eq_false_iff_ne.mpr same,ih]

theorem findTarget (scope : Namespace.Scope) (ns : List String) (n : String) (h : n ∈ ns) :
    ((ns.map (target scope)).find? fun t => t.owner == (owner scope n)) = some ((target scope) n) := by
  induction ns with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.map_cons,List.find?_cons]
    by_cases eq : a = n
    · subst a; simp [target]
    · have diff : ((target scope) a).owner ≠ (owner scope n) := fun e => eq (congrArg Namespace.Owner.name e)
      simp [beq_eq_false_iff_ne.mpr diff, ih (List.mem_cons.mp h |>.resolve_left (Ne.symm eq))]

theorem knownMember (p : Namespace.Indexed) (scope : Namespace.Scope) (pkg : Namespace.PackageLookup)
    (n : String) (span : Span) (_selfNe : n ≠ "self") (_superNe : n ≠ "super")
    (pkgFound : p.byPackage[scope.package.source]? = some pkg)
    (emptyDeps : pkg.dependencies[n]? = none)
    (hit : p.byOwner[(⟨scope, n⟩ : Namespace.Owner)]? = some (target scope n)) :
    Namespace.resolve p scope [n] span = .ok (target scope n) := by
  obtain ⟨fuel,limit⟩ : ∃ fuel, Limits.namespaceResolution = fuel + 2 := ⟨Limits.namespaceResolution - 2, by decide⟩
  unfold Namespace.resolve
  rw [limit]
  have charged : StateT.run (Namespace.charge span) (fuel+2) = .ok ((),fuel+1) := rfl
  simp [Namespace.resolveAt, pkgFound, Namespace.preludeOperator,hit,emptyDeps, Namespace.memberAt,
    Namespace.visible, target, charged, Namespace.descend]
  rfl
end VastitasQualification.CompatLookup

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def compatibilityScope : Namespace.Scope := ⟨Indexed.CompatibilityProfile.profileId, []⟩
abbrev compatOwner := CompatLookup.owner compatibilityScope
abbrev compatTarget := CompatLookup.target compatibilityScope
def names : List String := ["QQ", "GridQQ", "Scheme", "BaseQQ", "affineQQ", "baseQQ", "originQQ", "identityQQ", "dimensionQQ",
  "CInfReal", "GridSmooth", "CInfScheme", "BaseSmooth", "affineSmooth", "baseSmooth", "originSmooth", "identitySmooth", "dimensionSmooth",
  "Objects", "Point", "Morphism", "Pointed", "compose", "apply"]

theorem listTargets : idx.declarations = ⟨ExitFixture.owner,.function,true⟩ :: names.map compatTarget := by rfl

theorem ownerMember (n : String) (h : n ∈ names) : idx.byOwner[compatOwner n]? = some (compatTarget n) := by
  change (Namespace.ownerIndex idx.declarations)[compatOwner n]? = _
  rw [CompatLookup.indexLookup,listTargets,List.find?_cons]
  have ne : ExitFixture.owner ≠ compatOwner n := fun e => by
    have h := congrArg (fun o : Namespace.Owner => o.scope.package.source) e
    change "vastitas:compat:flat" = "vastitas:compat:2-6" at h
    contradiction
  change (match ExitFixture.owner == compatOwner n with
    | true => some (⟨ExitFixture.owner,.function,true⟩ : Namespace.Target)
    | false => (names.map compatTarget).find? (fun (t : Namespace.Target) => t.owner == compatOwner n)) = _
  rw [beq_eq_false_iff_ne.mpr ne]
  exact CompatLookup.findTarget compatibilityScope names n h

def compatPkg := idx.packages[1]!
theorem compatPkgFound : idx.byPackage[compatibilityScope.package.source]? = some compatPkg.lookup := by
  let rootPkg := idx.packages[0]!
  change (({} : Std.HashMap String Namespace.PackageLookup).insert compatPkg.id.source compatPkg.lookup |>.insert rootPkg.id.source rootPkg.lookup)[compatPkg.id.source]? = _
  have distinct : rootPkg.id.source ≠ compatPkg.id.source := by decide
  rw [Std.HashMap.getElem?_insert]
  simp only [beq_eq_false_iff_ne.mpr distinct, Bool.false_eq_true, ite_false,Std.HashMap.getElem?_insert_self]

theorem resolveMember (n : String) (h : n ∈ names) (span : Span) :
    Namespace.resolve idx compatibilityScope [n] span = .ok (compatTarget n) := by
  have good : ∀ a ∈ names, a ≠ "self" ∧ a ≠ "super" := by decide
  obtain ⟨selfNe,superNe⟩ := good n h
  have own := ownerMember n h
  have emptyDeps : compatPkg.lookup.dependencies[n]? = none := Std.HashMap.getElem?_empty
  have hit : idx.byOwner[(⟨compatibilityScope, n⟩ : Namespace.Owner)]? = some (compatTarget n) := own
  exact CompatLookup.knownMember idx compatibilityScope compatPkg.lookup n span selfNe superNe compatPkgFound emptyDeps hit

def ref (name : String) (span : Span := {}) : Source.Reference := ⟨compatibilityScope, ⟨[name],span⟩, compatTarget name⟩
theorem resolveIdName (name : String) (span : Span) (refs : List Source.Reference) (hn : name ∈ names) :
    (Source.resolveId idx compatibilityScope ⟨[name],span⟩).run refs = .ok (compatOwner name,ref name span :: refs) := by
  unfold Source.resolveId
  simp [resolveMember name hn span,ref]
  rfl

def fallbackId (n : String) (s : Span) (r : List Source.Reference) :=
  Source.resolveId idx compatibilityScope ⟨[n],s⟩ r

theorem shortcut (n : String) (s : Span) (r : List Source.Reference) :
    Source.resolveId idx (⟨Indexed.CompatibilityProfile.profileId, []⟩ : Namespace.Scope) ⟨[n],s⟩ r =
      if n ∈ names then .ok (compatOwner n,ref n s :: r) else fallbackId n s r := by
  by_cases h : n ∈ names
  · simp only [h,ite_true]; exact resolveIdName n s r h
  · simp only [h,ite_false]; rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.shortcut
