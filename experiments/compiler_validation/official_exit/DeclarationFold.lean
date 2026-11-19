import SchemeBodies
import SmoothBodies
import SharedBodies

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem everyRow : ∀ i ∈ List.range 24, matched i := by
  change ∀ i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23], matched i
  simp only [List.forall_mem_cons]
  obtain ⟨row0, row1, row2, row3, row4, row5, row6, row7, row8⟩ := schemeBodies
  obtain ⟨row9, row10, row11, row12, row13, row14, row15, row16, row17⟩ := smoothBodies
  obtain ⟨row18, row19, row20, row21, row22, row23⟩ := sharedBodies
  exact ⟨row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,fun _ h => nomatch h⟩

def walk (indices : List Nat) (env : Indexed.Core.Declarations) : Source.ResolveM Indexed.Core.Declarations :=
  indices.foldlM (fun env i =>
    let row := headers.owned[i]!
    Source.resolveBody idx {} {} row.1 row.2.span row.2.body env) env

theorem walkRows (indices : List Nat) (each : ∀ i ∈ indices, matched i)
    (env : Indexed.Core.Declarations) (rs : List Source.Reference) :
    (walk indices env).run rs = .ok (indices.foldl (fun env i => rows[i]!.insert env) env,
      indices.foldl (fun rs i => rows[i]!.record rs) rs) := by
  induction indices generalizing env rs with
  | nil => rfl
  | cons i is ih =>
    simp only [walk,List.foldlM_cons,StateT.run_bind]
    have passed := each i (by simp) env rs
    unfold step at passed
    rw [passed]
    exact ih (fun j h => each j (List.mem_cons_of_mem _ h)) _ _

theorem bodyFold : foldFrom ⟨[],[],[]⟩ [] = .ok (accumulated,bodyEdges) := by
  exact walkRows (List.range 24) everyRow ⟨[],[],[]⟩ []

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.bodyFold
