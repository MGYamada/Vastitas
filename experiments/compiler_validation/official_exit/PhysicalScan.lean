import VastitasKernel.EditSourceFiles

/-! The physical lexer and the JSON decoder replay in separate Lean processes.
The byte-index rules below use the proved ASCII property of this input. -/
namespace VastitasQualification.ExitAdmission
open Lean VastitasKernel
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

attribute [local cbv_eval] Std.HashMap.isEmpty_emptyWithCapacity Std.HashMap.keys_emptyWithCapacity

theorem keys_singleton {β : Type} (capacity k : Nat) (v : β) :
    ((Std.HashMap.emptyWithCapacity capacity : Std.HashMap Nat β).insert k v).keys = [k] := by
  let m := (Std.HashMap.emptyWithCapacity capacity : Std.HashMap Nat β).insert k v
  have len : m.keys.length = 1 := by simp [m, Std.HashMap.size_insert]
  obtain ⟨a, one⟩ := List.length_eq_one_iff.mp len
  have member : k ∈ m.keys := Std.HashMap.mem_keys.mpr Std.HashMap.mem_insert_self
  rw [one] at member
  have same : k = a := by simpa using member
  change m.keys = [k]
  exact one.trans (congrArg (fun x => [x]) same.symm)

attribute [local cbv_eval] keys_singleton Std.HashMap.getD_emptyWithCapacity

private def mainFn : Indexed.FunctionSource.Function := {
  name := "main", params := [], result := .data (.pure .int), isPublic := true
  body := .mk [] (.unary "-" (.integer "340282366920938463463374607431768211457" ⟨84,123,2,21⟩)
    ⟨83,123,2,20⟩) ⟨81,125,2,18⟩
  span := ⟨64,125,2,1⟩ }

private def rootModule : ResourceSource.Module := {
  pureModule := {
    module := { path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }
    declarations := [], functions := [mainFn] }
  functions := [] }

def candidate : ResourceSource.Program := {
  file := "ExitStatus.vast", root := flatPackageId.source, legacyGeometry := true
  packages := [{ id := flatPackageId, dependencies := [], modules := [rootModule] }] }

scoped notation "physicalExitText" => "// The executable status is the Euclidean remainder modulo 256.\nfn main() -> Int { -340282366920938463463374607431768211457 }\n"

def text := physicalExitText

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

private theorem readAt (p : String.Pos.Raw) :
    String.Pos.Raw.get? text p = text.toList.toArray[p.byteIdx]? := by
  cases p with
  | mk i => simpa [String.Pos.Raw.get?] using readAscii text.toList ascii 0 i

private theorem readChar (p : String.Pos.Raw) :
    String.Pos.Raw.get text p = (text.toList.toArray[p.byteIdx]?).getD default := by
  rw [← readAt]
  exact readTotal _ _ _

theorem readAtLiteral (p : String.Pos.Raw) :
    String.Pos.Raw.get? physicalExitText p = text.toList.toArray[p.byteIdx]? := readAt p
theorem readCharLiteral (p : String.Pos.Raw) :
    String.Pos.Raw.get physicalExitText p = (text.toList.toArray[p.byteIdx]?).getD default := readChar p
attribute [local cbv_eval] readAtLiteral readCharLiteral
attribute [local cbv_opaque] String.Pos.Raw.get? String.Pos.Raw.get

def entryFile : PhysicalSources.File := ⟨"ExitStatus.vast".toUTF8, 0, text⟩
def entryLayout : PhysicalSources.Layout := ⟨#[entryFile], 0⟩
def entrySite : AssemblyText.FiniteSite :=
  ⟨flatPackageId.source, [], true, 0, {}, ⟨64,66,2,1⟩, .singleton⟩
def entryItem : FiniteSourceFiles.Item := ⟨flatPackageId.source, [], mainFn.span, true, .singleton mainFn []⟩
def entrySites : AssemblyText.SourceChecks := {
  edits := some {}, flat := true
  finiteSites := ({} : FiniteSourceFiles.Sites).insert 64 entrySite
  singletonNames := ({} : Std.HashMap (String × List String × List String) Bool).insert
    (flatPackageId.source, [], ["main"]) false }

theorem scannedEntry : ExactModelSource.scanFiles entryLayout candidate EditSourceFiles.relevant {edits := some {}} =
    .ok entrySites := by cbv

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.scannedEntry
