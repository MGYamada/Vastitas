import VastitasPublicTest.SingletonFixtures
import VastitasKernel.LLVM.ExactLibrary
import VastitasKernel.LLVM.UnaryTable
import VastitasKernel.LLVM.ExitFunction
import VastitasKernel.LLVM.FiniteModuleRegression
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Official-kernel regressions for lexical components and complete unary switch modules. -/

namespace VastitasKernel.LLVM.Regression

private def ascii (text : String) : List UInt8 := text.toUTF8.data.toList

theorem quote_all_byte_classes :
    Bytes.quote [0, 10, 34, 92, 127, 128, 255] =
      ascii "\"\\00\\0A\\22\\5C\\7F\\80\\FF\"" := by decide

theorem quoted_bytes_roundtrip :
    Bytes.parseQuotedComplete (ascii "\"\\00\\0A\\22\\5C\\7F\\80\\FF\"") =
      some [0, 10, 34, 92, 127, 128, 255] := by decide

theorem reject_raw_text : Bytes.parseQuotedComplete (ascii "\"main\"") = none := by decide
theorem reject_lowercase_escape : Bytes.parseQuotedComplete (ascii "\"\\ff\"") = none := by decide
theorem reject_nonhex_escape : Bytes.parseQuotedComplete (ascii "\"\\G0\"") = none := by decide
theorem reject_short_escape : Bytes.parseQuotedComplete (ascii "\"\\0\"") = none := by decide
theorem reject_unclosed_string : Bytes.parseQuotedComplete (ascii "\"\\41") = none := by decide
theorem reject_trailing_bytes : Bytes.parseQuotedComplete (ascii "\"\\41\"\n") = none := by decide
theorem preserve_suffix : Bytes.parseQuoted (ascii "\"\\41\"tail") =
    some ([65], ascii "tail") := by decide
theorem reject_over_bound : Bytes.parseQuotedBounded 4 (Bytes.quote [65]) = none := by decide
theorem accept_exact_bound : Bytes.parseQuotedBounded 5 (Bytes.quote [65]) = some [65] := by decide

theorem reject_float_type : ValueType.parse (ascii "float") = none := by decide
theorem reject_unadmitted_width : ValueType.parse (ascii "i128") = none := by decide
theorem reject_void_value : ValueType.parse (ascii "void") = none := by decide
theorem reject_type_suffix : ValueType.parse (ascii "i32 ") = none := by decide
theorem reject_type_attribute : ResultType.parse (ascii "ptr noalias") = none := by decide
theorem accept_void_result : ResultType.parse (ascii "void") = some .void := by decide

theorem reject_empty_target : checkTargetText .triple [] = none := by decide
theorem reject_target_newline : checkTargetText .triple (ascii "arm64\n") = none := by decide
theorem reject_target_nul : checkTargetText .triple [65, 0] = none := by decide
theorem reject_target_quote : checkTargetText .triple [65, 34] = none := by decide
theorem reject_target_colon : checkTargetText .triple (ascii "a:b") = none := by decide

def header : TargetHeader :=
  { triple := ⟨ascii "aarch64-unknown-linux-gnu", by decide⟩
    dataLayout := ⟨ascii "e-m:e-i64:64-i128:128-n32:64-S128-Fn32", by decide⟩ }

theorem header_roundtrip : TargetHeader.parseBounded header.print = some header :=
  TargetHeader.parseBounded_print header

theorem reject_header_instruction_suffix :
    TargetHeader.parseBounded (header.print ++ ascii "ret i32 0\n") = none := by
  rw [TargetHeader.parseBounded_print_suffix]
  decide

theorem reject_header_raw_target :
    TargetHeader.parseBounded (ascii "target triple = \"aarch64\"\ntarget datalayout = \"e\"\n") =
      none := by decide

theorem reject_header_empty_fields :
    TargetHeader.parseBounded (ascii "target triple = \"\"\ntarget datalayout = \"\"\n") = none := by decide

private def image : TableSwitch.Module := ⟨header, [1, 0, 1], by decide⟩

theorem image_roundtrip : TableSwitch.parse (TableSwitch.print image) = some image :=
  (TableSwitch.parse_iff _ _).2 rfl

theorem empty_switch_returns_sentinel (i : UInt32) :
    TableSwitch.evaluate ⟨header, [], by decide⟩ i = 0xFFFFFFFF := by
  simp [TableSwitch.evaluate]

theorem image_results : [0, 1, 2, 3, 4095, 0xFFFFFFFF].map (TableSwitch.evaluate image) =
    [1, 0, 1, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF] := by decide

theorem trailing_byte_breaks_image :
    TableSwitch.parse (TableSwitch.print image ++ [10]) ≠ some image := by
  rw [ne_eq, TableSwitch.parse_iff]
  intro e
  have length := congrArg List.length e
  simp at length

theorem wrong_table_breaks_image :
    TableSwitch.parse (TableSwitch.print ⟨header, [0, 1, 1], by decide⟩) ≠ some image := by
  rw [(TableSwitch.parse_iff _ _).2 rfl]
  decide

/-- Every status has exactly two canonical uppercase hexadecimal digits. -/
theorem exit_bytes (s : UInt8) : ExitMain.parse (ExitMain.print ⟨header,s⟩) = some ⟨header,s⟩ :=
  (ExitMain.parse_iff _ _).mpr rfl

theorem exit_status_bounds :
    [0,42,255,256,-1,340282366920938463463374607431768211501,-340282366920938463463374607431768211501].map
      ExitMain.statusOf = [0,42,255,0,255,45,211] := by decide

theorem changed_exit_fails (actual expected : UInt8) (changed : actual ≠ expected) :
    ExitMain.parse (ExitMain.print ⟨header,actual⟩) ≠ some ⟨header,expected⟩ := by
  rw [exit_bytes]
  simp [changed]

section
set_option maxRecDepth 4096

theorem exit_rejects_bad_abi : ExitMain.parse
    (header.print ++ ascii "\ndefine i64 @main() {\nentry:\n  ret i64 u0x2A\n}\n") = none := by decide

theorem exit_rejects_unbounded_return : ExitMain.parse
    (header.print ++ ascii "\ndefine i32 @main() {\nentry:\n  ret i32 u0x100\n}\n") = none := by decide

theorem exit_rejects_suffix : ExitMain.parse (ExitMain.print ⟨header,42⟩ ++ [10]) = none := by decide

end

open Lean
private def qualify (wire : Json) (needsEntry : Bool) (expected : Option (Int × UInt8)) : Bool := Id.run do
  let .ok req := ResourceSource.Wire.check wire needsEntry | return false
  match ExitFunction.compile req header, expected with
  | some a, some (value, status) =>
    return a.literal.value == value && ExitMain.evaluate a.toModule == status.toUInt32 &&
      ExitMain.parse (ExitMain.print a.toModule) == some a.toModule
  | none, none => return true
  | _, _ => return false

#eval RegressionSupport.check "literal main" "checked entry in check and build modes" (Id.run do
  let big := 340282366920938463463374607431768211501
  for needsEntry in [true,false] do
    for (fixture, expected) in [("positive", some (big,45)), ("negative", some (-big,211)),
        ("modulus", some (256,0)), ("sum", none), ("extra", none)] do
      unless qualify (RegressionRequest.physical fixture) needsEntry expected do return false
  return true)

private def boxed : ExactLibrary.Code :=
  ⟨header,[.nat,.int],.int,[.apply .natIntDiv [0,1],.apply (.int .add) [2,2]],3⟩

#eval RegressionSupport.check "boxed library" "typed calls, ownership and complete bytes" (Id.run do
  unless ExactLibrary.parse boxed.print == some boxed do return false
  for forged in [{boxed with params := [.int,.nat]}, {boxed with resultType := .nat},
                 {boxed with steps := [.apply .natIntDiv [0,2]]},
                 {boxed with steps := [.apply .natIntDiv [0]]}] do
    unless (ExactLibrary.parse forged.print).isNone do return false
  let some text := String.fromUTF8? ⟨boxed.print.toArray⟩ | return false
  let drop := "  call void @vastitas_release_v1(ptr %v2)\n"
  for changed in [text.replace drop "",text.replace drop (drop ++ drop),
                  text.replace "ptr %v2, ptr %v2" "ptr %v2, ptr %v0",
                  text.replace "declare ptr" "declare noalias ptr",text ++ "\n"] do
    unless changed != text && (ExactLibrary.parse changed.toUTF8.data.toList).isNone do return false
  return true)

end VastitasKernel.LLVM.Regression
