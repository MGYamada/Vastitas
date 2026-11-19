import Admission

namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

private theorem readAscii (cs : List Char) (ascii : ∀ c ∈ cs, c.utf8Size = 1) (i j : Nat) :
    String.Pos.Raw.utf8GetAux? cs ⟨i⟩ ⟨i+j⟩ = cs[j]? := by
  induction cs generalizing i j with
  | nil => simp [String.Pos.Raw.utf8GetAux?]
  | cons c cs ih =>
    have size := ascii c (by simp)
    cases j with
    | zero => simp [String.Pos.Raw.utf8GetAux?]
    | succ j =>
      have diff : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i+(j+1)⟩ := fun h => by have := congrArg String.Pos.Raw.byteIdx h; simp at this
      have step : (⟨i⟩ : String.Pos.Raw) + c = ⟨i+1⟩ := congrArg (fun n => String.Pos.Raw.mk (i+n)) size
      simp only [String.Pos.Raw.utf8GetAux?,diff,ite_false,step,List.getElem?_cons_succ]
      rw [show i+(j+1) = i+1+j by omega]
      exact ih (fun a mem => ascii a (List.mem_cons_of_mem _ mem)) (i+1) j

private theorem readTotal (cs : List Char) (i j : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux cs i j = (String.Pos.Raw.utf8GetAux? cs i j).getD default := by
  induction cs generalizing i j with
  | nil => rfl
  | cons c cs ih => simp [String.Pos.Raw.utf8GetAux,String.Pos.Raw.utf8GetAux?]; split <;> simp_all

private theorem ascii : ∀ c ∈ text.toList, c.utf8Size = 1 := by decide

theorem readAt (p : String.Pos.Raw) :
    String.Pos.Raw.get? text p = text.toList.toArray[p.byteIdx]? := by
  cases p with
  | mk i => simpa [String.Pos.Raw.get?] using readAscii text.toList ascii 0 i

theorem readChar (p : String.Pos.Raw) :
    String.Pos.Raw.get text p = (text.toList.toArray[p.byteIdx]?).getD default := by
  rw [← readAt]
  exact readTotal _ _ _

private theorem readAtLiteral (p : String.Pos.Raw) :
    String.Pos.Raw.get? physicalExitText p = text.toList.toArray[p.byteIdx]? := readAt p
private theorem readCharLiteral (p : String.Pos.Raw) :
    String.Pos.Raw.get physicalExitText p = (text.toList.toArray[p.byteIdx]?).getD default := readChar p
attribute [local cbv_eval] readAtLiteral readCharLiteral
attribute [local cbv_opaque] String.Pos.Raw.get? String.Pos.Raw.get

theorem parsedEvents : AssemblyText.parse text 0 = .ok [] := by cbv

/-- All outer checks on the concrete request compose from the exact inner
pass. The remaining equality includes the original authority and body checks. -/
theorem wire_of_pass (h : passReady = true) :
    (ResourceSource.Wire.check VastitasQualification.ExitFixture.wire true).isOk = true :=
  wire_of_parts h parsedEvents

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.wire_of_pass
