import Lean.Elab.Term
import VastitasOracle.BinaryFunction
import VastitasOracle.CallFunction
import VastitasOracle.ExitFunction
import VastitasOracle.DispatchFunction
import VastitasKernel.LLVM.FiniteModule
import VastitasOracle.StorageProgram
import VastitasKernel.LLVM.ExactProgram
import VastitasKernel.LLVM.FiniteExecution

/-! Closed statements about the checked-in LLVM files. Each statement embeds the contents of its
file. The source replay also compares the raw files byte for byte on the fixed target of each sample. -/
namespace Vastitas.LLVMCorpus
open VastitasKernel.LLVM

set_option maxRecDepth 8192

def header : TargetHeader :=
  ⟨⟨TableSwitch.ascii "arm64-apple-darwin27.2.0", by decide⟩,
   ⟨TableSwitch.ascii "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32", by decide⟩⟩

def emptyModel : TableSwitch.Module := ⟨header, [], by decide⟩
def lookupModel : TableSwitch.Module := ⟨header, [1, 0, 1], by decide⟩
def closureUnitModel : TableSwitch.Module := ⟨header, [1, 2], by decide⟩
def compositionModel : BinaryTable.Module :=
  ⟨header, 6, 6, [
  0, 1, 2, 3, 4, 5,
  1, 0, 4, 5, 2, 3,
  2, 3, 0, 1, 5, 4,
  3, 2, 5, 4, 0, 1,
  4, 5, 1, 0, 3, 2,
  5, 4, 3, 2, 1, 0], by decide, by decide, false⟩
def assembledModel : DispatchBool.Module :=
  ⟨header, false, .argument, [.constant false], by decide, true, 42, 7⟩

def emptyBytes := TableSwitch.ascii (include_str "src" / "empty-lookup.ll")
def lookupBytes := TableSwitch.ascii (include_str "src" / "unary-table.ll")
def closureUnitBytes := TableSwitch.ascii (include_str "src" / "closure-unit.ll")
def exitBytes := TableSwitch.ascii (include_str "src" / "exit-status.ll")
def foldedBytes := TableSwitch.ascii (include_str "src" / "folded-arithmetic.ll")
def assembledBytes := TableSwitch.ascii (include_str "src" / "assembled-bool.ll")
/-- Embed raw octets directly so the kernel compares list constructors without
reducing a conversion of the whole UTF-8 string. -/
elab "corpus_bytes " file:str : term => do
  let source := System.FilePath.mk (← readThe Lean.Core.Context).fileName
  let some dir := source.parent | throwError "corpus needs a source directory"
  let bytes ← IO.FS.readBinFile (dir / file.getString)
  return Lean.toExpr bytes.data.toList

def boxedBytes := corpus_bytes "src/boxed-arithmetic.ll"

def boxedProgram : ExactProgram.Code :=
  ⟨header,#[
    ⟨[.int],.int,[],0⟩,
    ⟨[.int],.int,[.invoke 0 [0],.primitive (.apply (.int .add) [1,0])],2⟩,
    ⟨[.int,.nat],.int,[.primitive (.apply .intNatDiv [0,1])],2⟩,
    ⟨[],.int,[.primitive (.int (-340282366920938463463374607431768211457)),.invoke 1 [0],
      .primitive (.nat 3),.invoke 2 [1,2]],3⟩],3⟩

def programBytes := corpus_bytes "src/boxed-program.ll"

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem boxed_program_verified : programBytes = boxedProgram.print := by rfl

private def unselectedChoose (left right : ExactLibrary.Kind) : ExactProgram.Function :=
  ⟨[left,right],.int,[.primitive (.int 0)],2⟩

def borrowedOperator : ExactProgram.Code :=
  ⟨header,#[
    ⟨[.int,.int],.int,[.primitive (.apply (.int .add) [0,1])],2⟩,
    ⟨[],.int,[.primitive (.int 40),.primitive (.int 2),.invoke 0 [0,1]],2⟩,
    unselectedChoose .nat .nat, unselectedChoose .nat .int,
    unselectedChoose .int .nat, unselectedChoose .int .int],1⟩

def borrowedOperatorBytes := corpus_bytes "src/borrowed-operator.ll"

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem borrowed_operator_verified : borrowedOperatorBytes = borrowedOperator.print := by rfl

def uncalledOperator : ExactProgram.Code :=
  ⟨header,#[
    ⟨[],.int,[.primitive (.int 7)],0⟩,
    unselectedChoose .nat .nat, unselectedChoose .nat .int,
    unselectedChoose .int .nat, unselectedChoose .int .int,
    ⟨[.int,.int],.int,[.primitive (.apply (.int .add) [0,1])],2⟩],0⟩

def uncalledOperatorBytes := corpus_bytes "src/uncalled-operator.ll"

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem uncalled_operator_verified : uncalledOperatorBytes = uncalledOperator.print := by rfl

def boxedModel : ExactLibrary.Code :=
  ⟨header,[.nat,.int],.int,[.nat 5,.apply (.nat .sub) [0,2],.apply .natIntDiv [3,1],
    .apply (.int .add) [4,4]],5⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem boxed_arithmetic_verified : boxedBytes = boxedModel.print := by rfl

def compositionBytes := corpus_bytes "src/s3-composition.ll"
def oppositeBytes := corpus_bytes "src/opposite-s3.ll"
def isoBytes := corpus_bytes "src/finite-iso.ll"
def kleisliBytes := corpus_bytes "src/finite-kleisli.ll"
def kleisliCallbackBytes := corpus_bytes "src/kleisli-callback.ll"
def kleisliForwardBytes := corpus_bytes "src/kleisli-forward.ll"
def structuredLookupBytes := corpus_bytes "src/structured-lookup.ll"
def structuredLookupLinuxBytes := corpus_bytes "src/structured-lookup-linux-x86_64.ll"
def staticSelectionBytes := corpus_bytes "src/static-selection.ll"

open FiniteModule

private def slot (n : Nat) : String := s!"v0_{n}"
private def reg (n : Nat) : Operand := .reg (slot n)
private def ret (r : String) : Exit := .ret ⟨.word,.reg r⟩
private def constant (d : String) (n : UInt32 := 0) : Instr := .binary d .add .word (.literal 0) (.literal n)
private def both (d x y : Nat) : Instr := .binary (slot d) .band .bit (reg x) (reg y)

private def call (d : Nat) (fn : String) (args : List Nat) : Instr :=
  .call (slot d) .word fn (args.map fun n => ⟨.word,reg n⟩)
private def eq (d x y : Nat) : Instr := .compare (slot d) .eq .word (reg x) (reg y)

private def straight (name : String) (arity : Nat) (ops : List Instr) (result : Nat) : Func :=
  ⟨name,true,.word,(List.range arity).map fun n => (.word,slot n),[⟨"b0",ops,ret (slot result)⟩]⟩

namespace OppositeS3

/-- A permutation is its three images. Lexicographic order gives the public
arrow ordinals; ordinary composition applies the right permutation first. -/
private def permutations : List (List Nat) :=
  [[0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0]]

private def product (g f : List Nat) : Nat := permutations.idxOf (f.map fun i => g[i]!)

private def composeAt (n : Nat) (reversed : Bool) : List Func :=
  let name := s!"t{n}_0_2"
  let rows := permutations.flatMap fun g => permutations.map fun f =>
    if reversed then product f g else product g f
  (table name [6,6] rows).toList ++ [straight s!"f{n}" 2 [call 2 name [0,1]] 2]

def code : Code :=
  let inverse := permutations.map fun p => permutations.idxOf ([0,1,2].map fun i => p.idxOf i)
  let entry : Func := ⟨"f2",true,.word,[],[
    ⟨"b0",[constant (slot 0) 1, constant (slot 1) 2, call 2 "f0" [0,1],
      constant (slot 3) 1, constant (slot 4) 2, call 5 "f1" [3,4], constant (slot 6) 3,
      call 7 "t2_0_7" [6], constant (slot 8) 3, eq 9 2 8, constant (slot 10) 4,
      eq 11 5 10, both 12 9 11, constant (slot 13) 4, eq 14 7 13, both 15 12 14],
      .branch (reg 15) "b1" "b2"⟩,
    ⟨"b1",[constant "v1_0" 42],.jump "b3"⟩, ⟨"b2",[constant "v2_0" 7],.jump "b3"⟩,
    ⟨"b3",[.phi "v3_0" .word [(.reg "v1_0","b1"),(.reg "v2_0","b2")]],ret "v3_0"⟩]⟩
  ⟨header, composeAt 0 true ++ composeAt 1 false ++ (table "t2_0_7" [6] inverse).toList ++
    [entry, ⟨"main",false,.word,[],[⟨"start",[.call "result" .word "f2" []],ret "result"⟩]⟩]⟩

end OppositeS3

namespace Iso

private def projection (fn tableName : String) : List Func :=
  (table tableName [] [0]).toList ++ [straight fn 0 [call 0 tableName []] 0]

private def composeAt (fn tableName : String) : List Func :=
  (table tableName [1,1] [0]).toList ++ [straight fn 2 [call 2 tableName [0,1]] 2]

private def merge (name left right : String) : Instr :=
  .phi (name ++ "_0") .word [(.reg ("v" ++ left ++ "_0"),"b" ++ left),(.reg ("v" ++ right ++ "_0"),"b" ++ right)]

/-- The arrows have different endpoints but each Hom fiber here has one tag.
Composition selects two specializations and each source branch retains its own join. -/
def code : Code :=
  let entry : Func := ⟨"f4", true, .word, [], [
    ⟨"b0", [call 0 "f0" [], call 1 "f1" [], call 2 "f2" [1,0], constant (slot 3), eq 4 2 3],
      .branch (reg 4) "b1" "b5"⟩,
    ⟨"b1", [.call "v1_0" .word "f3" [⟨.word,reg 0⟩,⟨.word,reg 1⟩], constant "v1_1",
      .compare "v1_2" .eq .word (.reg "v1_0") (.reg "v1_1")], .branch (.reg "v1_2") "b2" "b3"⟩,
    ⟨"b2", [constant "v2_0" 42], .jump "b4"⟩, ⟨"b3", [constant "v3_0" 7], .jump "b4"⟩,
    ⟨"b4", [merge "v4" "2" "3"], .jump "b6"⟩, ⟨"b5", [constant "v5_0" 9], .jump "b6"⟩,
    ⟨"b6", [merge "v6" "4" "5"], ret "v6_0"⟩]⟩
  ⟨header, projection "f0" "t0_0_0" ++ projection "f1" "t1_0_0" ++ composeAt "f2" "t2_0_2" ++
    composeAt "f3" "t3_0_2" ++ [entry, ⟨"main", false, .word, [],
      [⟨"start", [.call "result" .word "f4" []], ret "result"⟩]⟩]⟩

end Iso

namespace Kleisli

/-- Each selected Hom fiber in this example has a single legal ordinal. -/
private def singleton (name : String) (arity : Nat) : List Func :=
  (table name (List.replicate arity 1) [0]).toList

private def extension (id first last : Nat) : List Func :=
  let map := s!"t{id}_0_2"
  let inner := s!"t{id}_0_4"
  let outer := s!"t{id}_0_5"
  singleton map 1 ++ singleton inner 2 ++ singleton outer 2 ++
    [straight s!"f{id}" 2 [call 2 map [first],constant (slot 3),
      call 4 inner [3,2],call 5 outer [4,last]] 5]

private def program : Func := ⟨"f5",true,.word,[],[
  ⟨"b0",[call 0 "f1" [], constant (slot 1), call 2 "f2" [0,1], constant (slot 3),
    call 4 "f3" [3,0], constant (slot 5), call 6 "f4" [5], constant (slot 7), eq 8 0 7,
    constant (slot 9), eq 10 2 9, both 11 8 10, eq 12 4 2, both 13 11 12,
    constant (slot 14), eq 15 6 14, both 16 13 15, constant (slot 17),
    call 18 "f0" [17], constant (slot 19), eq 20 18 19, both 21 16 20],.branch (reg 21) "b1" "b2"⟩,
  ⟨"b1",[constant "v1_0"],.jump "b3"⟩, ⟨"b2",[constant "v2_0" 1],.jump "b3"⟩,
  ⟨"b3",[.phi "v3_0" .word [(.reg "v1_0","b1"),(.reg "v2_0","b2")]],ret "v3_0"⟩]⟩

/-- Complete independent instruction, register, label, call and target model. -/
def code : Code := ⟨header,
  singleton "t0_0_1" 1 ++ [straight "f0" 1 [call 1 "t0_0_1" [0]] 1,
    straight "f1" 0 [constant (slot 0)] 0] ++
  extension 2 1 0 ++ extension 3 0 1 ++ singleton "t4_0_2" 2 ++
  [straight "f4" 1 [constant (slot 1),call 2 "t4_0_2" [1,0]] 2, program,
   ⟨"main",false,.word,[],[⟨"start",[.call "result" .word "f5" []],ret "result"⟩]⟩]⟩

end Kleisli

namespace KleisliCallback

/-- The selected callback returns the nonidentity arrow of C₂. The lifted
argument to bind is evaluated once, before its ordinal is passed to bind. -/
private def withAdapter (applyArrow : Func) : Code :=
  let producer := straight "f0" 0 [constant (slot 0) 1] 0
  let bindFn := straight "f1" 2 [call 2 "t1_0_2" [1], constant (slot 3) 1,
    call 4 "t1_0_4" [3,2], call 5 "t1_0_5" [4,0]] 5
  let erased := fun n => Instr.binary (slot n) .bor .bit (.literal 0) (.literal 0)
  let entry : Func := ⟨"f3", true, .word, [], [
    ⟨"b0", [erased 0, constant (slot 1) 1, erased 2, call 3 "f2" [1],
      constant (slot 4) 1, eq 5 3 4], .branch (reg 5) "b1" "b2"⟩,
    ⟨"b1", [constant "v1_0" 42], .jump "b3"⟩, ⟨"b2", [constant "v2_0" 7], .jump "b3"⟩,
    ⟨"b3", [.phi "v3_0" .word [(.reg "v1_0", "b1"), (.reg "v2_0", "b2")]], ret "v3_0"⟩]⟩
  let product := [0,1,1,0]
  ⟨header, [producer] ++ (table "t1_0_2" [2] [0,1]).toList ++
    (table "t1_0_4" [2,2] product).toList ++ (table "t1_0_5" [2,2] product).toList ++
    [bindFn, applyArrow, entry, ⟨"main", false, .word, [],
      [⟨"start", [.call "result" .word "f3" []], ret "result"⟩]⟩]⟩

def code : Code := withAdapter (straight "f2" 1 [call 1 "f0" [], call 2 "f1" [0,1]] 2)

/-- Passing the producer to the forwarding overload binds the erased Fn value
before invoking its selected target and passing its result to bind. -/
def forwarded : Code := withAdapter (straight "f2" 1
  [.binary (slot 1) .bor .bit (.literal 0) (.literal 0), call 2 "f0" [], call 3 "f1" [0,2]] 3)

end KleisliCallback

private def bit (dst : Nat) (b : Bool) : Instr :=
  .binary (slot dst) .bor .bit (.literal 0) (.literal (if b then 1 else 0))

private def boolCall (dst : Nat) (callee : String) (args : List Nat) : Instr :=
  .call (slot dst) .bit callee (args.map fun n => ⟨.bit, reg n⟩)

private def boolHelper (name : String) (params : List (Width × String)) (ops : List Instr)
    (result : Nat) : Func :=
  ⟨name, true, .bit, params, [⟨"b0", ops, .ret ⟨.bit, reg result⟩⟩]⟩

namespace StaticSelection

private def program : Func := ⟨"f5", true, .word, [], [
  ⟨"b0", [bit 0 false, bit 1 false, bit 2 false, boolCall 3 "f0" [], bit 4 true,
    boolCall 5 "f2" [4], bit 6 false, bit 7 true, boolCall 8 "f4" [7], bit 9 false,
    .compare (slot 10) .eq .bit (reg 8) (reg 9), both 11 5 10], .branch (reg 11) "b1" "b2"⟩,
  ⟨"b1", [constant "v1_0" 42], .jump "b3"⟩, ⟨"b2", [constant "v2_0" 7], .jump "b3"⟩,
  ⟨"b3", [.phi "v3_0" .word [(.reg "v1_0", "b1"), (.reg "v2_0", "b2")]], ret "v3_0"⟩]⟩

/-- The two invoke specializations call the selected method and lifted lambda respectively.
The last helper retains the unselected method. -/
def code : Code :=
  let param : List (Width × String) := [(.bit, slot 0)]
  ⟨header, [boolHelper "f0" [] [bit 0 false] 0, boolHelper "f1" param [] 0,
    boolHelper "f2" param [boolCall 1 "f1" [0]] 1, boolHelper "f3" param [bit 1 false] 1,
    boolHelper "f4" param [boolCall 1 "f3" [0]] 1, program, boolHelper "f6" param [bit 1 false] 1,
    ⟨"main", false, .word, [], [⟨"start", [.call "result" .word "f5" []], ret "result"⟩]⟩]⟩

end StaticSelection

namespace StructuredLookup

private def digits : Func :=
  let arms := (List.range 12).map fun n => (n.toUInt32, s!"case{n}")
  let leaves := arms.map fun (n,label) => Block.mk label [] (.ret ⟨.word,.literal n⟩)
  ⟨"t0_0_3", true, .word, [(.word,"x"),(.word,"y"),(.word,"axis2")], [
    ⟨"start", [.compare "rowOK" .ult .word (.reg "x") (.literal 2),
      .compare "colOK" .ult .word (.reg "y") (.literal 3),
      .binary "both" .band .bit (.reg "rowOK") (.reg "colOK"),
      .compare "ok2" .ult .word (.reg "axis2") (.literal 2),
      .binary "inside2" .band .bit (.reg "both") (.reg "ok2")],
      .branch (.reg "inside2") "lookup" "miss"⟩,
    ⟨"lookup", [.binary "base" .mul .word (.reg "x") (.literal 3),
      .binary "index" .add .word (.reg "base") (.reg "y"),
      .binary "base2" .mul .word (.reg "index") (.literal 2),
      .binary "index2" .add .word (.reg "base2") (.reg "axis2")],
      .switch (.reg "index2") "miss" arms⟩] ++ leaves ++
    [⟨"miss", [], .ret ⟨.word,.literal 0xffffffff⟩⟩]⟩

private def expected : Func := ⟨"t2_0_4", true, .word, [], [
  ⟨"start", [], .switch (.literal 0) "miss" [(0,"case0")]⟩,
  ⟨"case0", [], .ret ⟨.word,.literal 9⟩⟩, ⟨"miss", [], .ret ⟨.word,.literal 0xffffffff⟩⟩]⟩

private def negate (d x : Nat) : Instr := .compare (slot d) .eq .bit (reg x) (.literal 0)

private def program : Func := ⟨"f2", true, .word, [], [
  ⟨"b0", [constant (slot 0) 1, constant (slot 1) 1, constant (slot 2) 1,
    call 3 "f0" [0,1,2], call 4 "t2_0_4" [], eq 5 3 4, bit 6 true,
    boolCall 7 "f1" [6,5], bit 8 true, bit 9 false, boolCall 10 "f1" [8,9],
    negate 11 10, both 12 7 11], .branch (reg 12) "b1" "b2"⟩,
  ⟨"b1", [constant "v1_0" 42], .jump "b3"⟩, ⟨"b2", [constant "v2_0" 7], .jump "b3"⟩,
  ⟨"b3", [.phi "v3_0" .word [(.reg "v1_0", "b1"), (.reg "v2_0", "b2")]], ret "v3_0"⟩]⟩

def code : Code :=
  let params : List (Width × String) := [(.bit,slot 0),(.bit,slot 1)]
  ⟨header, [digits, straight "f0" 3 [call 3 "t0_0_3" [0,1,2]] 3,
    boolHelper "f1" params [negate 2 0,.binary (slot 3) .bor .bit (reg 2) (reg 1)] 3,
    expected, program, boolHelper "f3" params [negate 2 0,negate 3 1,both 4 2 3] 4,
    ⟨"main", false, .word, [], [⟨"start", [.call "result" .word "f2" []], ret "result"⟩]⟩]⟩

/-- The same function model printed with LLVM 23.1.4's x86-64 Linux target. -/
def linuxCode : Code := { code with header :=
  ⟨⟨TableSwitch.ascii "x86_64-unknown-linux-gnu", by decide⟩,
   ⟨TableSwitch.ascii "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128", by decide⟩⟩ }

end StructuredLookup

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem structured_lookup_verified : structuredLookupBytes = StructuredLookup.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem structured_lookup_linux_verified : structuredLookupLinuxBytes = StructuredLookup.linuxCode.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem static_selection_verified : staticSelectionBytes = StaticSelection.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem finite_iso_verified : isoBytes = Iso.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem opposite_s3_verified : oppositeBytes = OppositeS3.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem finite_kleisli_verified : kleisliBytes = Kleisli.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem kleisli_callback_verified : kleisliCallbackBytes = KleisliCallback.code.print := rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 3000000 in
theorem kleisli_forward_verified : kleisliForwardBytes = KleisliCallback.forwarded.print := rfl

private theorem parse_printed {bytes : List UInt8} {code : FiniteModule.Code} {model : FiniteModule.Module}
    (printed : bytes = code.print) (certified : FiniteModule.certify code = some model) :
    FiniteModule.parse bytes = some model := by
  unfold FiniteModule.certify at certified
  split at certified <;> try contradiction
  split at certified <;> try contradiction
  cases certified
  exact (FiniteModule.parse_iff _ _).mpr printed

/-- Successful structural certification of this concrete code gives canonical
parser acceptance of precisely the retained bytes. -/
theorem finite_kleisli_parse {model : FiniteModule.Module}
    (certified : FiniteModule.certify Kleisli.code = some model) :
    FiniteModule.parse kleisliBytes = some model :=
  parse_printed finite_kleisli_verified certified

def callBytes := TableSwitch.ascii (include_str "src" / "static-call.ll")

theorem empty_lookup_verified : TableSwitch.parse emptyBytes = some emptyModel :=
  (TableSwitch.parse_iff _ _).mpr rfl

theorem unary_table_verified : TableSwitch.parse lookupBytes = some lookupModel :=
  (TableSwitch.parse_iff _ _).mpr rfl

theorem closure_unit_verified : TableSwitch.parse closureUnitBytes = some closureUnitModel :=
  (TableSwitch.parse_iff _ _).mpr rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem s3_composition_verified : BinaryTable.parse compositionBytes = some compositionModel :=
  (BinaryTable.parse_iff _ _).mpr rfl

theorem static_call_verified : ForwardCall.parse callBytes = some ⟨lookupModel⟩ :=
  (ForwardCall.parse_iff _ _).mpr rfl

theorem exit_status_verified : ExitMain.parse exitBytes = some ⟨header, 255⟩ :=
  (ExitMain.parse_iff _ _).mpr rfl

theorem folded_arithmetic_verified : ExitMain.parse foldedBytes = some ⟨header, 10⟩ :=
  (ExitMain.parse_iff _ _).mpr rfl

theorem assembled_bool_verified : DispatchBool.parse assembledBytes = some assembledModel :=
  (DispatchBool.parse_iff _ _).mpr rfl

private def forExit {bytes model} (_ : ExitMain.parse bytes = some model) : ByteArray :=
  ⟨bytes.toArray⟩

private def forLookup {bytes model} (_ : TableSwitch.parse bytes = some model) : ByteArray :=
  ⟨bytes.toArray⟩

private def forCall {bytes model} (_ : ForwardCall.parse bytes = some model) : ByteArray :=
  ⟨bytes.toArray⟩

private def forBinary {bytes model} (_ : BinaryTable.parse bytes = some model) : ByteArray :=
  ⟨bytes.toArray⟩

private def forDispatch {bytes model} (_ : DispatchBool.parse bytes = some model) : ByteArray :=
  ⟨bytes.toArray⟩

private def forProgram {bytes : List UInt8} {code : ExactProgram.Code}
    (_ : bytes = code.print) : ByteArray := ⟨bytes.toArray⟩

private def forExact {bytes : List UInt8} {code : ExactLibrary.Code}
    (_ : bytes = code.print) : ByteArray := ⟨bytes.toArray⟩

/-- Two coordinate buffers and a standard chart with one complex or real
element in each row. Reconstruct the payloads and the checked copy from the
source fixture independently of its printed module. -/
def affineIdentity (complex : Bool) : StorageModule.Code :=
  let tag := if complex then 1 else 0
  let view := [0,2,1,2,0]
  let first := [tag,9223372036854775808,if complex then 1 else 0]
  let second := if complex then [tag,0,9218868437227405378] else [tag,9218868437227405378,0]
  ⟨header,[⟨.allocate,[0,tag,2]⟩, ⟨.allocate,[1,tag,2]⟩,
    ⟨.store,[0] ++ view ++ [0,0] ++ first⟩, ⟨.store,[0] ++ view ++ [1,0] ++ second⟩,
    ⟨.copy,[0] ++ view ++ [1] ++ view⟩, ⟨.expect,[1] ++ view ++ [0,0] ++ first⟩,
    ⟨.expect,[1] ++ view ++ [1,0] ++ second⟩, ⟨.drop,[1]⟩, ⟨.drop,[0]⟩],0⟩

def realIdentityBytes := corpus_bytes "src/float-identity.ll"
def complexIdentityBytes := corpus_bytes "src/float-complex-identity.ll"

set_option maxRecDepth 65536 in
theorem real_identity_verified : realIdentityBytes = (affineIdentity false).print := rfl
set_option maxRecDepth 65536 in
theorem complex_identity_verified : complexIdentityBytes = (affineIdentity true).print := rfl

/-- Independent schedule for the 1×1 coefficient example. With inputs 2 and
3, the overwrite computes 3. The subsequent accumulation reads alpha from
allocation 3 and computes 4 * 2 * 3 + 2 * 3 = 30. -/
def gemmCoefficients : StorageModule.Code :=
  let atCell := fun (id : Nat) => [id, 0, 1, 1, 1, 0]
  let fill := fun id bits => VastitasKernel.MidIR.StorageEffects.Call.mk .fill (atCell id ++ [0, bits, 0])
  let expect := fun bits => VastitasKernel.MidIR.StorageEffects.Call.mk .expect (atCell 2 ++ [0, 0, 0, bits, 0])
  let matrices := [0] ++ atCell 0 ++ [0] ++ atCell 1 ++ [0] ++ atCell 2
  let unit := 2^52
  let two := 1024 * unit
  let three := two + 2^51
  let half := 1022 * unit
  let thirty := 1027 * unit + 7 * 2^49
  ⟨header, ([0,1,2,3].map fun id => ⟨.allocate, [id,0,1]⟩) ++
    [fill 0 two, fill 1 three, fill 3 (1025 * unit),
     ⟨.gemm, matrices ++ [0, 1,0,half,0,0,0, 0,0,0,0,0,0]⟩, expect three,
     ⟨.gemm, matrices ++ [1, 2,0,0,0,3,0, 1,0,two,0,0,0]⟩, expect thirty] ++
    ([3,2,1,0].map fun id => ⟨.drop, [id]⟩), 0⟩

def gemmCoefficientBytes := corpus_bytes "src/gemm-coefficients.ll"

set_option maxRecDepth 65536 in
theorem gemm_coefficients_verified : gemmCoefficientBytes = gemmCoefficients.print := rfl

private def forStorage {bytes : List UInt8} {code : StorageModule.Code}
    (_ : bytes = code.print) : ByteArray := ⟨bytes.toArray⟩

private def forCode {bytes : List UInt8} {code : FiniteModule.Code}
    (_ : bytes = code.print) : ByteArray := ⟨bytes.toArray⟩

/-- Each registry entry obtains its bytes from its own closed proof. -/
def checkedFiles : List (String × ByteArray) :=
  [("exit-status.ll", forExit exit_status_verified),
   ("folded-arithmetic.ll", forExit folded_arithmetic_verified),
   ("boxed-program.ll", forProgram boxed_program_verified),
   ("borrowed-operator.ll", forProgram borrowed_operator_verified),
   ("uncalled-operator.ll", forProgram uncalled_operator_verified),
   ("boxed-arithmetic.ll", forExact boxed_arithmetic_verified),
   ("assembled-bool.ll", forDispatch assembled_bool_verified),
   ("empty-lookup.ll", forLookup empty_lookup_verified),
   ("unary-table.ll", forLookup unary_table_verified),
   ("closure-unit.ll", forLookup closure_unit_verified),
   ("gemm-coefficients.ll", forStorage gemm_coefficients_verified),
   ("float-identity.ll", forStorage real_identity_verified),
   ("float-complex-identity.ll", forStorage complex_identity_verified),
   ("opposite-s3.ll", forCode opposite_s3_verified),
   ("finite-iso.ll", forCode finite_iso_verified),
   ("finite-kleisli.ll", forCode finite_kleisli_verified),
   ("kleisli-callback.ll", forCode kleisli_callback_verified),
   ("kleisli-forward.ll", forCode kleisli_forward_verified),
   ("structured-lookup.ll", forCode structured_lookup_verified),
   ("structured-lookup-linux-x86_64.ll", forCode structured_lookup_linux_verified),
   ("static-selection.ll", forCode static_selection_verified),
   ("s3-composition.ll", forBinary s3_composition_verified),
   ("static-call.ll", forCall static_call_verified)]

end Vastitas.LLVMCorpus

private def checkEntry (file : String) (bytes : List UInt8)
    (code : VastitasKernel.LLVM.FiniteModule.Code) (status : UInt32) : IO Unit := do
  let some parsed := VastitasKernel.LLVM.FiniteModule.parse bytes
    | throw (IO.userError s!"{file}: the complete module did not parse and validate")
  unless decide (parsed.code = code) && parsed.code.entryStatus == some status do
    throw (IO.userError s!"{file}: mismatched parsed code or hosted status")

def main (args : List String) : IO Unit := do
  let root :: expected := args | throw (IO.userError "expected corpus directory and filenames")
  let files := Vastitas.LLVMCorpus.checkedFiles
  let borrowed := Vastitas.LLVMCorpus.borrowedOperator
  unless VastitasKernel.LLVM.ExactProgram.parse Vastitas.LLVMCorpus.borrowedOperatorBytes == some borrowed &&
      borrowed.entryValue == some 42 do
    throw (IO.userError "borrowed-operator.ll: different method bodies, call target or integer result")
  let uncalled := Vastitas.LLVMCorpus.uncalledOperator
  unless VastitasKernel.LLVM.ExactProgram.parse Vastitas.LLVMCorpus.uncalledOperatorBytes == some uncalled &&
      uncalled.entryValue == some 7 do
    throw (IO.userError "uncalled-operator.ll: wrong retained functions or entry result")
  let program := Vastitas.LLVMCorpus.boxedProgram
  let moduleText := String.fromUTF8! ⟨Vastitas.LLVMCorpus.programBytes.toArray⟩
  unless VastitasKernel.LLVM.ExactProgram.parse moduleText.toUTF8.data.toList == some program do
    throw (IO.userError "boxed-program.ll: wrong module")
  unless program.entryValue == some ((-2 * (2^128 + 1) : Int) / 3) do
    throw (IO.userError "boxed-program.ll: wrong integer before exit-status projection")
  for (before,after) in [("call ptr @vq_f2(ptr %v1, ptr %v2)", "call ptr @vq_f2(ptr %v2, ptr %v1)"),
      ("  call void @vastitas_retain_v1(ptr %v0)\n", ""), ("  call void @vastitas_initialize_v1()\n",""),
      ("@vq_f2(ptr %v1, ptr %v2)", "@vq_f3(ptr %v1, ptr %v2)")] do
    let changed := moduleText.replace before after
    unless changed != moduleText && (VastitasKernel.LLVM.ExactProgram.parse changed.toUTF8.data.toList).isNone do
      throw (IO.userError "boxed-program.ll: accepted a damaged call, startup or ownership instruction")
  unless VastitasKernel.LLVM.ExactLibrary.parse Vastitas.LLVMCorpus.boxedBytes == some Vastitas.LLVMCorpus.boxedModel do
    throw (IO.userError "boxed-arithmetic.ll: different typed call graph or ownership schedule")
  checkEntry "opposite-s3.ll" Vastitas.LLVMCorpus.oppositeBytes Vastitas.LLVMCorpus.OppositeS3.code 42
  checkEntry "finite-iso.ll" Vastitas.LLVMCorpus.isoBytes Vastitas.LLVMCorpus.Iso.code 42
  checkEntry "finite-kleisli.ll" Vastitas.LLVMCorpus.kleisliBytes Vastitas.LLVMCorpus.Kleisli.code 0
  checkEntry "kleisli-callback.ll" Vastitas.LLVMCorpus.kleisliCallbackBytes Vastitas.LLVMCorpus.KleisliCallback.code 42
  checkEntry "kleisli-forward.ll" Vastitas.LLVMCorpus.kleisliForwardBytes Vastitas.LLVMCorpus.KleisliCallback.forwarded 42
  checkEntry "structured-lookup.ll" Vastitas.LLVMCorpus.structuredLookupBytes Vastitas.LLVMCorpus.StructuredLookup.code 42
  checkEntry "structured-lookup-linux-x86_64.ll" Vastitas.LLVMCorpus.structuredLookupLinuxBytes
    Vastitas.LLVMCorpus.StructuredLookup.linuxCode 42
  checkEntry "static-selection.ll" Vastitas.LLVMCorpus.staticSelectionBytes Vastitas.LLVMCorpus.StaticSelection.code 42
  for (code,bytes) in [(Vastitas.LLVMCorpus.affineIdentity false, Vastitas.LLVMCorpus.realIdentityBytes),
      (Vastitas.LLVMCorpus.affineIdentity true, Vastitas.LLVMCorpus.complexIdentityBytes),
      (Vastitas.LLVMCorpus.gemmCoefficients, Vastitas.LLVMCorpus.gemmCoefficientBytes)] do
    let some parsed := VastitasKernel.LLVM.StorageModule.parse bytes
      | throw (IO.userError "storage entry: cannot parse the complete entry")
    unless decide (parsed = code) &&
        decide (parsed.run (some ()) (fun s _ => (s,true)) = (code.calls,.success 0)) &&
        decide (parsed.run (some ()) (fun s _ => (s,false)) = (code.calls.take 1,.failed)) &&
        decide (parsed.run none (fun (s : Unit) _ => (s,true)) = ([],.unavailable)) do
      throw (IO.userError "storage entry: different call order or arena exit")
  unless expected.mergeSort == (files.map Prod.fst).mergeSort do
    throw (IO.userError "source fixtures and registered LLVM byte theorems differ")
  for (name, certified) in files do
    let stored ← IO.FS.readBinFile (System.FilePath.mk root / name)
    unless stored == certified do
      throw (IO.userError s!"{name}: stored bytes differ from this file's proved bytes")
