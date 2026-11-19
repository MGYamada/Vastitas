import VastitasKernel.LLVM.UnaryTable

set_option autoImplicit false

namespace VastitasOracle.LLVMTable
open VastitasKernel VastitasKernel.Indexed VastitasKernel.LLVM

private theorem entry_sound {env : Environment} {table input output : DeclId} {range : List String}
    {name : String} {tag : TableSwitch.Tag} (h : UnaryTable.entry env table input output range name = some tag) :
    ∃ result, FiniteTables.lookupTag env table [(input, name)] = some (output, result) ∧
      range[tag.val]? = some result := by
  unfold UnaryTable.entry at h
  cases row : FiniteTables.lookupTag env table [(input, name)] with
  | none => simp [row] at h
  | some pair =>
    obtain ⟨owner, result⟩ := pair
    by_cases owned : owner = output
    · subst owner
      by_cases found : range[range.idxOf result]? = some result
      · by_cases fits : range.idxOf result < 4096
        · have eq : (⟨range.idxOf result, fits⟩ : TableSwitch.Tag) = tag := by
            simpa [row, found, fits, guard] using h
          exact ⟨result, rfl, eq ▸ found⟩
        · simp [row, found, fits, guard] at h
      · simp [row, found, guard, failure] at h
    · simp [row, owned, guard, failure] at h

/-- Each modeled in-domain result comes from the selected table and range.
The equations quantify over the full canonical byte string and foreign i32
input. The external LLVM parser, optimizer and machine code are separate. -/
theorem named_result {env : Environment} {id : DeclId} {header : TargetHeader}
    (image : UnaryTable.Image env id header) (bytes : List UInt8)
    (accepted : TableSwitch.parse bytes = some image.toModule)
    (word : UInt32) (key : String) (atIndex : image.domain[word.toNat]? = some key) :
    bytes = TableSwitch.print image.toModule ∧
    ∃ (tag : TableSwitch.Tag) (result : String),
      TableSwitch.evaluate image.toModule word = tag.val.toUInt32 ∧
      FiniteTables.lookupTag env id [(image.input, key)] = some (image.output, result) ∧
      image.range[tag.val]? = some result := by
  have bound : word.toNat < image.outputs.length := by
    rw [image.total]
    exact (List.getElem?_eq_some_iff.mp atIndex).choose
  let tag := image.outputs[word.toNat]
  have hit : image.outputs[word.toNat]? = some tag := List.getElem?_eq_getElem bound
  have correct := image.correspondence word.toNat
  rw [hit, atIndex] at correct
  obtain ⟨result, row, ordinal⟩ := entry_sound correct.symm
  refine ⟨(TableSwitch.parse_iff _ _).1 accepted, tag, result, ?_, row, ordinal⟩
  simp [TableSwitch.evaluate, UnaryTable.Image.toModule, hit]

theorem outside_domain {env : Environment} {id : DeclId} {header : TargetHeader}
    (image : UnaryTable.Image env id header) (word : UInt32) (miss : image.domain[word.toNat]? = none) :
    TableSwitch.evaluate image.toModule word = 0xFFFFFFFF := by
  simp [TableSwitch.evaluate, UnaryTable.Image.toModule, image.correspondence, miss]

end VastitasOracle.LLVMTable
