import VastitasOracle.ModuleEffects
import VastitasOracle.DeclarationSafety
import VastitasOracle.Elaboration
import VastitasOracle.ModuleSafety

namespace VastitasOracle.Elaboration
open VastitasKernel VastitasKernel.Checker.Internal

/-- Selection preserves whole checked declarations, including bodies and
annotations, rather than trusting an ID-only match after sorting. -/
theorem selectFunctions_source (functions : Array CheckedFunction) (order : List Nat) :
    Establishes (selectFunctions functions order)
      (fun sorted => ∀ function ∈ sorted, function ∈ functions.toList) := by
  induction order with
  | nil => exact establishes_pure (by simp)
  | cons index rest ih =>
    simp only [selectFunctions]
    split
    · rename_i function found
      apply establishes_bind ih
      intro sorted included
      apply establishes_pure
      intro actual member
      rcases List.mem_cons.mp member with equal | member
      · subst actual
        exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? found)
      · exact included actual member
    · exact establishes_fail _ _ _ _ _

theorem sortFunctions_source (functions : List CheckedFunction) :
    Establishes (sortFunctions functions)
      (fun sorted => sorted.length = functions.length ∧
        ∀ function ∈ sorted, function ∈ functions) := by
  unfold sortFunctions
  apply establishes_bind_any
  intro order
  apply establishes_bind (selectFunctions_source functions.toArray order)
  intro sorted included
  split
  · rename_i same
    apply establishes_pure
    exact ⟨by simpa using same, by simpa using included⟩
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _

/-- A same-length selection of distinct elements cannot omit a source member.
This proves completeness of reordering without depending on queue internals. -/
theorem selection_complete {α : Type} (source selected : List α)
    (unique : selected.Nodup) (sameLength : selected.length = source.length)
    (included : ∀ value ∈ selected, value ∈ source) :
    ∀ value ∈ source, value ∈ selected := by
  classical
  intro value member
  apply Classical.byContradiction
  intro absent
  have subset : selected ⊆ source.erase value := by
    intro other inSelected
    have different : other ≠ value := by
      intro equal
      exact absent (equal ▸ inSelected)
    exact (List.mem_erase_of_ne different).mpr (included other inSelected)
  have shorter := unique.length_le_of_subset subset
  have erased := List.length_erase_of_mem member
  have positive : 0 < source.length := List.length_pos_of_mem member
  rw [sameLength, erased] at shorter
  omega

def preparedSignatures (signatures : List Signature) : Signatures :=
  signatures.foldl (fun table signature => table.insert signature.raw.name signature) {}

/-- Evidence before uniqueness is used to show that sorting is complete. The
source traversal and body traversal remain related to their original inputs. -/
def ModuleElaborated (raw : RawModule) (module : CheckedModule) : Prop :=
  ∃ signatures source,
    List.Forall₂ VastitasKernel.Declaration.Signature raw.functions signatures ∧
    List.Forall₂ (VastitasKernel.Elaboration.Function (preparedSignatures signatures))
      signatures source ∧
    module.functions.length = source.length ∧
    (∀ function ∈ module.functions, function ∈ source) ∧
    module.mainId = (module.functions.find? (fun f => f.name == "main")).map (·.id)

theorem checkModuleImpl_corresponds (raw : RawModule) (requireMain : Bool) :
    Establishes (checkModuleImpl raw requireMain) (ModuleElaborated raw) := by
  unfold checkModuleImpl
  split
  · apply establishes_bind_any
    intro _
    apply establishes_bind_any
    intro _
    apply establishes_bind (establishes_mapM prepareSignature
      VastitasKernel.Declaration.Signature raw.functions
      (fun function _ => VastitasOracle.Declaration.prepareSignature_corresponds function))
    intro signatures declarations
    apply establishes_bind (establishes_mapM (checkFunction (preparedSignatures signatures))
      (VastitasKernel.Elaboration.Function (preparedSignatures signatures)) signatures
      (fun signature _ => checkFunction_corresponds _ signature))
    intro source functions
    apply establishes_bind (sortFunctions_source source)
    intro sorted sortedFrom
    dsimp only
    split
    · apply establishes_unreachable
      exact establishes_fail _ _ _ _ _
    · apply establishes_pure
      exact ⟨signatures, source, declarations, functions, sortedFrom.1, sortedFrom.2, rfl⟩
  · apply establishes_unreachable
    exact establishes_fail _ _ _ _ _

/-- Every decoded declaration has a generated body, and every generated body
has a decoded declaration with the same parameter/result annotations and source
syntax. Reordering cannot drop or synthesize declarations. -/
def ModuleCorresponds (raw : RawModule) (module : CheckedModule) : Prop :=
  ∃ signatures,
    List.Forall₂ VastitasKernel.Declaration.Signature raw.functions signatures ∧
    (∀ function ∈ module.functions,
      ∃ signature ∈ signatures,
        VastitasKernel.Elaboration.Function (preparedSignatures signatures) signature function) ∧
    (∀ signature ∈ signatures,
      ∃ function ∈ module.functions,
        VastitasKernel.Elaboration.Function (preparedSignatures signatures) signature function) ∧
    module.mainId = (module.functions.find? (fun f => f.name == "main")).map (·.id)

theorem module_corresponds_of_elaborated (raw : RawModule) (module : CheckedModule)
    (elaborated : ModuleElaborated raw module)
    (unique : (module.functions.map (·.id)).Nodup) : ModuleCorresponds raw module := by
  obtain ⟨signatures, source, declarations, bodies, sameLength, included, entry⟩ := elaborated
  have distinct : module.functions.Nodup :=
    List.Pairwise.of_map (fun function : CheckedFunction => function.id)
      (fun _ _ different equal => different (congrArg (·.id) equal)) unique
  have complete := selection_complete source module.functions distinct sameLength included
  refine ⟨signatures, declarations, ?_, ?_, entry⟩
  · intro function member
    exact forall₂_right_member bodies function (included function member)
  · intro signature member
    obtain ⟨function, sourceMember, relation⟩ := forall₂_left_member bodies signature member
    exact ⟨function, complete function sourceMember, relation⟩

theorem checkModule_source_correspondence (raw : RawModule) (requireMain : Bool)
    (certified : CertifiedModule)
    (accepted : checkModule raw requireMain = .ok certified) :
    ModuleCorresponds raw certified.val := by
  obtain ⟨final, elaborated, typed, _⟩ :=
    checkModule_typed_and_ordered raw requireMain certified accepted
  exact module_corresponds_of_elaborated raw certified.val
    ((checkModuleImpl_corresponds raw requireMain).run {} certified.val final elaborated) typed.1

end VastitasOracle.Elaboration
