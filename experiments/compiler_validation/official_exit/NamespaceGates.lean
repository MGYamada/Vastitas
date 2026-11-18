import Source

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def idx := candidate.pureProgram.source.headers.indexed
theorem prices : Namespace.inputPrices idx = .ok (⟨0, by decide⟩,{}) := by rfl
theorem price : Namespace.priceInput idx wire = .ok ⟨34,by decide⟩ := by
  unfold Namespace.priceInput
  rw [prices]
  cbv

theorem supported : Indexed.AuthoritySource.supported candidate.pureProgram = .ok () := by rfl

theorem package_lookup : (Namespace.packageAt idx idx.root).isSome = true := by
  unfold Namespace.packageAt
  let rootPkg := idx.packages[0]!
  let compatPkg := idx.packages[1]!
  change (Option.map Namespace.PackageLookup.source
    ((({} : Std.HashMap String Namespace.PackageLookup).insert compatPkg.id.source compatPkg.lookup |>.insert rootPkg.id.source rootPkg.lookup)[rootPkg.id.source]?)).isSome = true
  rw [Std.HashMap.getElem?_insert_self]
  rfl

theorem uniqueOwners : Namespace.UniqueOwners idx := by
  unfold Namespace.UniqueOwners
  decide

private def pkg := Indexed.CompatibilityProfile.profileId
private def tagPrefix :=
  "ns_f_" ++ Namespace.encode pkg.source ++ Namespace.encode pkg.name ++ Namespace.encode pkg.version ++ "" ++ "end_"
private def tags : List String := (Indexed.CompatibilityProfile.profilePackage.modules.flatMap (·.declarations)).map
  (fun d => Namespace.encode d.name)

theorem qualifiedNames : Finite.distinct (idx.declarations.map (Namespace.symbol idx.toProgram)) = true := by
  apply (Finite.distinct_iff _).mpr
  change ("main" :: tags.map (fun t => tagPrefix ++ t)).Nodup
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨t, _, eq⟩ := List.mem_map.mp h
    have n := congrArg String.length eq
    have long : 4 < tagPrefix.length := by decide
    have short : "main".length = 4 := rfl
    rw [String.length_append,short] at n
    omega
  · have nodup : tags.Nodup := by decide
    exact List.Pairwise.map (fun t => tagPrefix ++ t) (fun a b different eq => different ((String.append_right_inj _).mp eq)) nodup

/-- The 24 compatibility declarations and the ordinary main share the real
namespace validator. Both the nominal owners and the generated symbol strings
are distinct. The public checker charges the full request 34 units. -/
theorem namespace_gates : idx.declarations.length = 25 ∧ Namespace.UniqueOwners idx ∧
    Finite.distinct (idx.declarations.map (Namespace.symbol idx.toProgram)) = true ∧
    (Namespace.packageAt idx idx.root).isSome = true ∧
    Namespace.priceInput idx wire = .ok ⟨34, by decide⟩ :=
  ⟨rfl,uniqueOwners,qualifiedNames,package_lookup,price⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.namespace_gates
