import NamespaceGates

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel VastitasQualification.ExitFixture
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem namespace_ok {α : Type} (p : Namespace.Indexed) (json : Json)
    (evaluate : Unit → Namespace.Result α) (cost : α → Nat)
    (u : Fin (Limits.namespaceProgramWork + 1)) (v : α)
    (price : Namespace.priceInput p json = .ok u) (accepted : evaluate () = .ok v)
    (limit : u.val + cost v ≤ Limits.namespaceProgramWork) :
    ∃ out, Namespace.checkRequest p json evaluate cost = .ok out ∧ out.value = v := by
  unfold Namespace.checkRequest
  split
  · simp_all
  · rename_i units priced
    replace priced := Except.ok.inj (priced.symm.trans price)
    subst units
    split
    · simp_all
    · rename_i actual hv
      replace hv := Except.ok.inj (hv.symm.trans accepted)
      subst actual
      simp [limit,pure,Except.pure]

theorem wire_from_checked {j : Json} {p : ResourceSource.Program} {main : Bool}
    (decoded : ResourceSource.Wire.program j = .ok p)
    (c : ResourceSource.Checked p main) (accepted : ResourceSource.check p main = .ok c)
    (u : Fin (Limits.namespaceProgramWork + 1))
    (price : Namespace.priceInput p.pureProgram.source.headers.indexed j = .ok u)
    (bound : u.val + ResourceSource.Wire.namespaceUnits c ≤ Limits.namespaceProgramWork)
    (trace : (AssemblySource.check j c.pureProgram.authority.headers.assembled.prepared.core.assembly).isOk = true)
    (edits : EditSourceFiles.check j p = .ok ())
    (definitions : ResourceSource.Wire.definitionsMatch c = true)
    (packages : ResourceSource.Wire.packageShapesMatch c = true)
    (revision : ResourceSource.Wire.RevisionMatches j c) :
    (ResourceSource.Wire.check j main).isOk = true := by
  rw [ResourceSource.Wire.check_of_decoded decoded]
  unfold ResourceSource.Wire.checkDecoded
  obtain ⟨r,hr,same⟩ := namespace_ok _ j (fun _ => ResourceSource.check p main) ResourceSource.Wire.namespaceUnits u c price accepted bound
  split
  · simp_all
  · rename_i r' hr'
    replace hr' := Except.ok.inj (hr'.symm.trans hr)
    subst r'
    cases h : AssemblySource.check j r.value.pureProgram.authority.headers.assembled.prepared.core.assembly with
    | error err =>
      rw [← same,h] at trace
      contradiction
    | ok result =>
      have hrev : ResourceSource.Wire.RevisionMatches j r.value := same ▸ revision
      have hdefs : ResourceSource.Wire.definitionsMatch r.value = true := same ▸ definitions
      have hpackages : ResourceSource.Wire.packageShapesMatch r.value = true := same ▸ packages
      simp [hdefs,hpackages,hrev,bind,Except.bind]
      split
      · rename_i _ mismatch
        rw [edits] at mismatch
        contradiction
      · rfl

theorem resourceFromPure (pure : Indexed.AuthoritySource.CheckedProgram candidate.pureProgram true)
    (accepted : Indexed.AuthoritySource.checkProgram candidate.pureProgram true = .ok pure) :
    ∃ c : ResourceSource.Checked candidate true, ResourceSource.check candidate true = .ok c ∧ c.pureProgram = pure := by
  unfold ResourceSource.check
  split
  · rename_i err bad
    rw [acceptedEnvelope] at bad
    contradiction
  · split
    · rename_i err bad
      change Indexed.AuthoritySource.checkProgram candidate.pureProgram true = .error err at bad
      rw [accepted] at bad
      contradiction
    · rename_i a actual
      change Indexed.AuthoritySource.checkProgram candidate.pureProgram true = .ok a at actual
      replace actual := Except.ok.inj (actual.symm.trans accepted)
      subst a
      exact ⟨_,rfl,rfl⟩
theorem file : AssemblySource.rootFile wire = .ok ⟨0,text⟩ := by rfl
theorem readEvents : AssemblySource.read wire = .ok [] := by rfl

theorem noEvents (j : Json) (r : AssemblySource.RootFile) (s : Span)
    (hf : AssemblySource.rootFile j = .ok r)
    (read : AssemblySource.read j = .ok []) (lex : AssemblyText.parse r.text r.offset = .ok []) :
    (AssemblySource.check j ⟨[], s⟩).isOk = true := by
  unfold AssemblySource.check
  split
  · simp_all
  · rename_i file supplied
    replace supplied := Except.ok.inj (supplied.symm.trans hf)
    subst file
    split
    · simp_all
    · simp_all
    · rename_i items scanned hi hl
      replace hi := Except.ok.inj (hi.symm.trans read)
      replace hl := Except.ok.inj (hl.symm.trans lex)
      subst items; subst scanned
      simp only [List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]
      rfl

theorem eventsChecked (parsedEvents : AssemblyText.parse text 0 = .ok []) (s : Span) : (AssemblySource.check wire ⟨[],s⟩).isOk = true :=
  noEvents _ _ _ file readEvents parsedEvents
/-- The signed literal declares no finite entries. Its compiled Core must have
the same empty finite projection, including declarations unused by main. -/
theorem literalDefinitions (c : ResourceSource.Checked candidate true)
    (finite : ResourceSource.Wire.coreFiniteEntries c.pureProgram.compiled.core.module.declarations.indexed = []) :
    ResourceSource.Wire.definitionsMatch c = true := by
  change (([] : List Indexed.Entry).isSublist _ &&
    ([] == ResourceSource.Wire.coreFiniteEntries c.pureProgram.compiled.core.module.declarations.indexed)) = true
  simp [finite]

/-- The literal contains no package cases to match against the returned Core. -/
theorem literalPackages (c : ResourceSource.Checked candidate true) :
    ResourceSource.Wire.packageShapesMatch c = true := by
  change ([] : List Indexed.Core.NamedPackage).isSublist _ = true
  simp

theorem checkedIf (lexical : AssemblyText.parse text 0 = .ok []) (c : ResourceSource.Checked candidate true)
    (accepted : ResourceSource.check candidate true = .ok c)
    (cost : 34 + ResourceSource.Wire.namespaceUnits c ≤ Limits.namespaceProgramWork)
    (events : c.pureProgram.authority.headers.assembled.prepared.core.assembly.events = [])
    (finite : ResourceSource.Wire.coreFiniteEntries c.pureProgram.compiled.core.module.declarations.indexed = []) :
    (ResourceSource.Wire.check wire true).isOk = true := by
  apply wire_from_checked decodedProgram c accepted _ price cost
  · let a := c.pureProgram.authority.headers.assembled.prepared.core.assembly
    have eqn : a = ⟨[], a.span⟩ := by
      exact congrArg (fun es => Namespace.Assembly.mk es a.span) events
    rw [show c.pureProgram.authority.headers.assembled.prepared.core.assembly = ⟨[], a.span⟩ from eqn]
    exact eventsChecked lexical _
  · exact physicalEdits
  · exact literalDefinitions c finite
  · exact literalPackages c
  · unfold ResourceSource.Wire.RevisionMatches
    change True
    trivial

theorem wireFromPure (lexical : AssemblyText.parse text 0 = .ok [])
    (pure : Indexed.AuthoritySource.CheckedProgram candidate.pureProgram true)
    (accepted : Indexed.AuthoritySource.checkProgram candidate.pureProgram true = .ok pure)
    (cost : 34 + pure.namespaceUnits ≤ Limits.namespaceProgramWork)
    (events : pure.authority.headers.assembled.prepared.core.assembly.events = [])
    (finite : ResourceSource.Wire.coreFiniteEntries pure.compiled.core.module.declarations.indexed = []) :
    (ResourceSource.Wire.check wire true).isOk = true := by
  obtain ⟨c,produced,kept⟩ := resourceFromPure pure accepted
  apply checkedIf lexical c produced
  · change 34 + (c.pureProgram.namespaceUnits + 0) ≤ _
    simpa only [kept,Nat.add_zero]
  · simpa [kept] using events
  · exact (congrArg (fun p => ResourceSource.Wire.coreFiniteEntries p.compiled.core.module.declarations.indexed) kept).trans finite

/-- This gate reads the actual protected-profile pass and preserves its budget
and original assembly obligations. An arbitrary prebuilt Core is insufficient. -/
def passReady : Bool :=
  match Indexed.AuthoritySource.checkProgram candidate.pureProgram true with
  | .error _ => false
  | .ok p => decide (34 + p.namespaceUnits ≤ Limits.namespaceProgramWork) &&
      p.authority.headers.assembled.prepared.core.assembly.events.isEmpty &&
      (ResourceSource.Wire.coreFiniteEntries p.compiled.core.module.declarations.indexed).isEmpty

theorem wire_of_parts (pass : passReady = true) (lex : AssemblyText.parse text 0 = .ok []) :
    (ResourceSource.Wire.check wire true).isOk = true := by
  unfold passReady at pass
  cases h : Indexed.AuthoritySource.checkProgram candidate.pureProgram true with
  | error e => simp [h] at pass
  | ok p =>
    obtain ⟨⟨cost,events⟩,finite⟩ :
        (34 + p.namespaceUnits ≤ Limits.namespaceProgramWork ∧
          p.authority.headers.assembled.prepared.core.assembly.events = []) ∧
        ResourceSource.Wire.coreFiniteEntries p.compiled.core.module.declarations.indexed = [] := by
      simpa [h] using pass
    exact wireFromPure lex p h cost events finite

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.wire_of_parts
