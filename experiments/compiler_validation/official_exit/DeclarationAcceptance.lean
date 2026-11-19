import DeclarationLowering
namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

theorem rankQuery (m : Std.HashMap DeclId Nat) (key : DeclId) :
    classRank m.toList key = (m[key]?).getD 0 := by
  cases h : m[key]? with
  | none =>
    have no : m.contains key = false := by rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
    rw [classRank, Std.HashMap.find?_toList_eq_none_iff_contains_eq_false.mpr no]; rfl
  | some n =>
    have mem : m.contains key = true := by rw [Std.HashMap.contains_eq_isSome_getElem?, h]; rfl
    have f := Std.HashMap.find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some.mpr ⟨Std.HashMap.getKey?_eq_some_of_contains mem,h⟩
    rw [classRank,f]; rfl

theorem sizeInsert (m : Std.HashMap DeclId Nat) (k : DeclId) (v : Nat) :
    (m.insert k v).size = if m.contains k then m.size else m.size + 1 := by
  rw [Std.HashMap.size_insert]
  rfl

attribute [local cbv_opaque] Std.HashMap.toList Std.HashMap.insert Std.HashMap.emptyWithCapacity
attribute [local cbv_eval] sizeInsert Std.HashMap.size_emptyWithCapacity
attribute [local cbv_eval] Std.HashMap.contains_emptyWithCapacity Std.HashMap.getElem?_emptyWithCapacity

def rankTable : Std.HashMap DeclId Nat := (({} : Std.HashMap DeclId Nat).insert (compatOwner "Objects") 1
  |>.insert (compatOwner "Scheme") 2 |>.insert (compatOwner "CInfScheme") 2)

theorem table : classRanks accumulated.indexed = rankTable.toList := by cbv

def orderedRanks : List (DeclId × Nat) := [(compatOwner "CInfScheme",2),(compatOwner "Scheme",2),(compatOwner "Objects",1)]

theorem sameRanks : classRank rankTable.toList = classRank orderedRanks := by
  funext k
  rw [rankQuery]
  simp only [rankTable,Std.HashMap.getElem?_insert,Std.HashMap.getElem?_empty,orderedRanks,classRank,List.find?_cons,List.find?_nil]
  cases h1 : compatOwner "CInfScheme" == k <;> cases h2 : compatOwner "Scheme" == k <;> cases h3 : compatOwner "Objects" == k <;> rfl

theorem sameEntries (env : Environment) (r s : List (DeclId × Nat))
    (same : classRank r = classRank s) : validEntry env r = validEntry env s := by
  funext e
  cases hd : e.declaration <;> simp only [validEntry,hd,validParents,same]

theorem data : Core.validDeclarations accumulated = true := by
  unfold Core.validDeclarations validEnvironment
  rw [table,sameEntries _ _ _ sameRanks]
  decide
def checkedDeclarations : Source.CheckedDeclarations headers := {
  resolved, namespaceAccepted := validated, ownersUnique := uniqueOwners, lowered := actualLowered,
  referencesValid, idsPreserved := namesPreserved, accepted := data, geometryAccepted := roles }

/-- Reassemble the independently checked result of the real declaration pass.
All computational data equal the candidate environment and all proofs belong
to these exact input headers. -/
theorem acceptedDeclarations : Source.checkDeclarations headers = .ok checkedDeclarations := by
  obtain ⟨c,passed,same⟩ := declarationsFromLower resolved actualLowered referencesValid namesPreserved data roles
  have eq : c = checkedDeclarations := by cases c; cases same; rfl
  exact passed.trans (congrArg Except.ok eq)

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.acceptedDeclarations
