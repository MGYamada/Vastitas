import DeclarationAcceptance

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def mainSpan : Span := ⟨64,125,2,1⟩
def headerMain : Surface.Function := {
  name := "main", params := [], result := .data (.named "Int"), body := .mk [] (.unit mainSpan) mainSpan, span := mainSpan }
def baseSurface : Surface.Program := {
  version := 4, file := "ExitStatus.vast", functions := [headerMain], generics := [], methods := [],
  abstractTypes := [], subtypes := [], abstractMethods := [] }
def namespaceBase : Namespace.Lowered := ⟨baseSurface,[]⟩

theorem namespaceLower : Namespace.lower idx = .ok namespaceBase := by
  unfold Namespace.lower
  rw [validated]
  rfl

def entryPkg := idx.packages[0]!
theorem entryPkgLookup : idx.byPackage[entryPkg.id.source]? = some entryPkg.lookup := by
  change (({} : Std.HashMap String Namespace.PackageLookup).insert compatPkg.id.source compatPkg.lookup |>.insert entryPkg.id.source entryPkg.lookup)[entryPkg.id.source]? = _
  exact Std.HashMap.getElem?_insert_self

theorem rootPackage : Namespace.packageAt idx idx.root = some entryPkg := by
  unfold Namespace.packageAt
  change (idx.byPackage[entryPkg.id.source]?).map Namespace.PackageLookup.source = _
  rw [entryPkgLookup]; rfl

theorem rootModule : Namespace.moduleAt idx ExitFixture.owner.scope = some entryPkg.modules[0]! := by
  let m := entryPkg.modules[0]!
  unfold Namespace.moduleAt Namespace.moduleLookupAt
  change (do let p ← idx.byPackage[entryPkg.id.source]?
             if p.source.id != entryPkg.id then none else p.modules[[]]?).map Namespace.ModuleLookup.source = _
  rw [entryPkgLookup]
  change ((({} : Std.HashMap (List String) Namespace.ModuleLookup).insert [] m.lookup)[([] : List String)]?).map Namespace.ModuleLookup.source = _
  rw [Std.HashMap.getElem?_insert_self]; rfl

def editInput : Edit.Prepared idx := ⟨namespaceBase,namespaceLower,[],[],[],ExitFixture.owner.scope,⟨[],{}⟩⟩
theorem editPrepared : Edit.prepare idx = .ok editInput := by
  unfold Edit.prepare
  have editable : idx.editable = true := rfl
  simp only [editable,pure,Except.pure,bind,Except.bind,ite_true]
  split
  · rename_i e bad; rw [namespaceLower] at bad; contradiction
  · rename_i b passed
    replace passed := Except.ok.inj (passed.symm.trans namespaceLower)
    subst b
    rw [rootPackage]
    have rootM : Namespace.moduleAt idx ⟨entryPkg.id,[]⟩ = some entryPkg.modules[0]! := rootModule
    simp only [rootM]
    rfl
def authorityPrepared : Authority.Prepared idx := ⟨editInput,[],[],[]⟩
theorem prepareAuthority : Authority.prepare idx = .ok authorityPrepared := by
  unfold Authority.prepare
  have on : idx.authority = true := rfl
  simp only [on,pure,Except.pure,bind,Except.bind,editPrepared]
  rfl

private def emptyGraph : Namespace.MembershipGraph := ⟨[],[]⟩

def assembled : Authority.Assembled idx := {
  prepared := authorityPrepared, preparedFrom := prepareAuthority, corresponds := by decide
  graph := emptyGraph, graphFrom := by rfl, memberships := by decide
  namespaces := ⟨uniqueOwners, by decide⟩, state := {}, traced := by rfl
  blockTargets := by rfl, returned := rfl, sealed := by
    change (∅ : Std.HashSet Namespace.Owner).toList.all _ = true
    rw [Std.HashSet.toList_empty]
    rfl
  authorized := by decide
  families := [], completed := by cbv, footprints := by decide, audit := baseSurface, auditFrom := by rfl }

scoped macro "useCheckedResult " cert:term : tactic => `(tactic| (
  split
  · rename_i err bad; have impossible := bad.symm.trans $cert; contradiction
  rename_i actual got
  replace got := Except.ok.inj (got.symm.trans $cert)
  subst actual))

theorem assembleWith {p : Namespace.Indexed} (a : Authority.Assembled p) : Authority.assemble p = .ok a := by
  obtain ⟨prepared, preparedFrom, corresponds, graph, graphFrom, memberships, namespaces, state,
    traced, blockTargets, returned, sealed, authorized, families, completed, footprints, audit, auditFrom⟩ := a
  unfold Authority.assemble
  useCheckedResult preparedFrom
  simp only [corresponds,dite_true]
  useCheckedResult graphFrom
  simp only [memberships,namespaces,and_self,dite_true]
  useCheckedResult traced
  simp only [returned,sealed,dite_true]
  split
  · rename_i err bad; rw [blockTargets] at bad; contradiction
  simp only [authorized,dite_true]
  useCheckedResult completed
  simp only [footprints,dite_true]
  useCheckedResult auditFrom
  rfl

theorem actualAssembly : Authority.assemble idx = .ok assembled := assembleWith assembled
end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.actualAssembly
