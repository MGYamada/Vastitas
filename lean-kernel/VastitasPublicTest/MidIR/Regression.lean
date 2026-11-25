import VastitasPublicTest.SingletonFixtures
import VastitasKernel.MidIR.PackageLink
import VastitasKernel.RegressionRequest
import VastitasKernel.RegressionSupport

set_option autoImplicit false

namespace VastitasKernel.MidIR.Regression
open Indexed
private def owner (n : String) : DeclId := ⟨⟨⟨"/mid", "mid", "1"⟩, []⟩, n⟩
private def bit : FiniteSort := .carrier (owner "Bit")
private def other : FiniteSort := .carrier (owner "Other")
private def env : Environment :=
  [⟨owner "Bit", .finiteCarrier ["off", "on"]⟩, ⟨owner "Other", .finiteCarrier ["off", "on"]⟩]
private def check := RegressionSupport.check "finite MidIR regression"

#eval check "finite declaration replay compares rows, carrier order and nominal owners in final Core" (Id.run do
  let tag (n : String) : Source.FiniteTag := ⟨n, {}⟩
  let carrier : Source.Declaration := ⟨"Bit", .finiteCarrier [tag "off", tag "on"], true, {}⟩
  let point : Source.Declaration := ⟨"point", .finiteTable [] ⟨["Bit"], {}⟩ [⟨[], tag "on", {}⟩], true, {}⟩
  let module : Source.Module := ⟨{ (default : Namespace.Module) with path := [], isPublic := true }, [point, carrier], []⟩
  let id := (owner "point").scope.package
  let program : Source.Program := ⟨"main.vast", id.source, [⟨id, [], [module], none⟩], false, false, false⟩
  let matchesCore := ResourceSource.Wire.finiteEntriesMatch program.indexed program.owned
  let table (result : String) : Entry := ⟨owner "point", .finiteTable [] (owner "Bit") [([], result)]⟩
  let bits : Entry := ⟨owner "Bit", .finiteCarrier ["off", "on"]⟩
  return matchesCore [table "on", bits] && !matchesCore [table "off", bits] &&
    !matchesCore [table "on", ⟨owner "Bit", .finiteCarrier ["on", "off"]⟩] &&
    !matchesCore [⟨owner "unrelated", (table "on").declaration⟩, bits] && !matchesCore [bits] &&
    !matchesCore [table "on", bits, ⟨owner "Extra", .finiteCarrier ["other"]⟩] &&
    !ResourceSource.Wire.finiteEntriesMatch program.indexed [] [bits])

#guard ExactFold.literalComparison .ne (.ascribe (.pure .nat) (.natural (2^128))) (.natural 0) == some true
#guard ExactFold.literalComparison .eq (.natural (2^128)) (.natural (2^128)) == some true
#guard (ExactFold.literalComparison .eq (.integer 0) (.natural 0)).isNone
#guard (ExactFold.literalComparison .ne (.ascribe (.pure .int) (.natural 0)) (.integer 1)).isNone
#guard (ExactFold.literalComparison .eq (.variable 0 ⟨.pure .int, none⟩) (.integer 0)).isNone

private def fn (blocks : Array (Block .optimization)) : Function .optimization :=
  ⟨⟨owner "flip"⟩, 0, ⟨0, []⟩, #[.finite bit], .finite bit, blocks⟩
private def graph : Array (Block .optimization) := #[
  ⟨#[.finite bit], #[⟨.finiteTag bit "on", []⟩, ⟨.compare .eq (.finite bit), [⟨0,0⟩, ⟨0,1⟩]⟩],
    .branch ⟨0,2⟩ ⟨1, ⟨0⟩, []⟩ ⟨2, ⟨0⟩, []⟩⟩,
  ⟨#[], #[⟨.finiteTag bit "off", []⟩], .jump ⟨3, ⟨1⟩, [⟨1,0⟩]⟩⟩,
  ⟨#[], #[], .jump ⟨3, ⟨2⟩, [⟨0,1⟩]⟩⟩,
  ⟨#[.finite bit], #[], .ret ⟨3⟩ ⟨3,0⟩⟩]

private def update (i : Nat) (f : Block .optimization → Block .optimization) :=
  fn (graph.modify i f)
#eval check "both tag phases validate" ((fn graph).execute env).isSome
#eval check "membership of a symbolic tag" (!(validFunction env (update 1 fun b =>
  { b with ops := #[⟨.finiteTag bit "bad", []⟩] })))
#eval check "ordinal range" (!(Opcode.valid env (.finiteOrdinal bit 2)))
#eval check "same labels in two nominal carriers" (!(validFunction env (update 1 fun b =>
  { b with ops := #[⟨.finiteTag other "off", []⟩] })))
#eval check "a join may not use a definition from a sibling" (!(validFunction env (update 3 fun b =>
  { b with term := .ret ⟨3⟩ ⟨1,0⟩ })))
#eval check "same-block self-use" (!(validFunction env (update 0 fun b =>
  { b with ops := b.ops.set! 1 ⟨.compare .eq (.finite bit), [⟨0,1⟩, ⟨0,2⟩]⟩ })))
#eval check "every incoming edge supplies the join parameter" (!(validFunction env (update 2 fun b =>
  { b with term := .jump ⟨3, ⟨2⟩, []⟩ })))
#eval check "unreachable block" (!(validFunction env (update 0 fun b =>
  { b with term := .jump ⟨1, ⟨0⟩, []⟩ })))
#eval check "absent destination" (!(validFunction env (update 1 fun b =>
  { b with term := .jump ⟨9, ⟨1⟩, []⟩ })))
#eval check "backedge" (!(validFunction env (update 1 fun b =>
  { b with term := .jump ⟨1, ⟨1⟩, []⟩ })))
#eval check "sibling token" (!(validFunction env (update 2 fun b =>
  { b with term := .jump ⟨3, ⟨1⟩, [⟨0,1⟩]⟩ })))
#eval check "stale token at return" (!(validFunction env (update 3 fun b =>
  { b with term := .ret ⟨0⟩ ⟨3,0⟩ })))

#eval check "distinct specializations may share a family; duplicate keys, symbols and stale entries fail" (Id.run do
  let first := fn graph
  let second := { first with coreId := 1, specialization := ⟨1, []⟩ }
  let m := Module.mk .null env #[first, second] none
  let distinct := { second with id := ⟨owner "other"⟩ }
  return m.execute.isSome &&
    ({ m with functions := #[first, { second with specialization := first.specialization }] }).execute.isNone &&
    ({ m with functions := #[first, { distinct with specialization := first.specialization }] }).execute.isNone &&
    ({ m with functions := #[first, { second with coreId := first.coreId }] }).execute.isNone &&
    ({ m with functions := #[first, distinct] }).execute.isSome &&
    ({ m with functions := #[first], entry := some 0 }).execute.isNone)

#eval check "module resolves direct calls by owner, key, symbol and exact nominal ABI" (Id.run do
  let leaf := { fn graph with specialization := ⟨0,[.concrete 7]⟩ }
  let caller (target : CallTarget) : Function .optimization :=
    { leaf with
      coreId := 1, specialization := ⟨1,[]⟩, id := ⟨owner "forward"⟩
      blocks := #[⟨#[.finite bit], #[⟨.call target,[⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩] }
  let module (target : CallTarget) := Module.mk .null env #[leaf,caller target] none
  let target := leaf.target
  let probe := {leaf with specialization := ⟨0,[.probe 7]⟩}
  return (module target).execute.isSome &&
    (module {target with symbol := 1}).execute.isNone &&
    (module {target with family := ⟨owner "wrong"⟩}).execute.isNone &&
    (module {target with key := ⟨9,[]⟩}).execute.isNone &&
    (module {target with key := ⟨0,[.concrete 8]⟩}).execute.isNone &&
    (Module.mk .null env #[probe, caller probe.target] none).execute.isNone &&
    (module {target with params := [.finite other]}).execute.isNone &&
    (module {target with result := .finite other}).execute.isNone &&
    ({module target with functions := #[caller target,leaf]}).execute.isNone)

#eval check "Unit and Bool stay distinct before their shared internal i1 ABI" (Id.run do
  let unit := { (fn graph) with
    params := #[]
    result := .unit
    blocks := #[⟨#[], #[⟨.unit, []⟩], .ret ⟨0⟩ ⟨0,0⟩⟩] }
  let badReturn := {unit with result := .bool}
  let withOp (op : Op .optimization) := {unit with blocks := unit.blocks.modify 0 fun b =>
    {b with ops := b.ops.push op}}
  let v : Ref := ⟨0,0⟩
  return (unit.execute env).isSome && (badReturn.execute env).isNone &&
    ([⟨.boolAnd,[v,v]⟩, ⟨.boolOr,[v,v]⟩, ⟨.boolNot,[v]⟩].all fun op => ((withOp op).execute env).isNone))
#eval check "Boolean opcodes reject the wrong operand count" (Id.run do
  let invalid (op : Op .optimization) := validFunction env (update 0 fun b =>
    {b with ops := b.ops.push op})
  let v : Ref := ⟨0,2⟩
  return !invalid ⟨.boolOr,[v]⟩ && !invalid ⟨.boolNot,[v,v]⟩)

private def tagResult : Core.Result := ⟨.finite bit, none⟩
private def boolResult : Core.Result := ⟨.pure .bool, none⟩
private def body : Core.Term :=
  .letE 12 (.finiteTag bit "on")
    (.branch (.binary .eq (.variable 9 tagResult) (.variable 12 tagResult) boolResult)
      (.scope (.finiteTag bit "off")) (.variable 12 tagResult) tagResult)
private def core (body : Core.Term) : Core.Function :=
  ⟨0, owner "flip", [⟨9, tagResult⟩], .finite bit, body, {}⟩
#eval check "accepted indexed Core lowers to four typed blocks" (Id.run do
  let f := core body
  let m : Core.Module := ⟨⟨env, [], []⟩, [f], none⟩
  let .ok checked := Core.Typing.checkModule m false | return false
  let some source := checked.module.functions.head? | return false
  let some out := lowerFunction env ⟨0, []⟩ source | return false
  return out.blocks.size == 4 && (out.execute env).isSome)
#eval check "unsupported call in a dead branch rejects the function" (
  (lowerFunction env ⟨0, []⟩ (core (.branch (.boolean false)
    (.call 42 [] [] tagResult) (.finiteTag bit "on") tagResult))).isNone)

#eval check "omission of a root, dependency call or nonwinning sibling rejects the link witness" (Id.run do
  let foreign : DeclId := ⟨⟨⟨"/dep","dep","1"⟩,[]⟩,"select"⟩
  let left := {core (.finiteTag bit "off") with id := 0, definition := foreign}
  let right := {left with id := 1, body := .finiteTag bit "on"}
  let entry := {core (.call 1 [.finiteTag bit "off"] [] tagResult) with id := 2, definition := owner "main"}
  let m : Core.Module := ⟨⟨env, [], []⟩, [left,right,entry], some 2⟩
  return PackageLink.rootCovered m "/mid" #[0,1,2] && !PackageLink.rootCovered m "/mid" #[0,1] &&
    PackageLink.closed m #[0,1,2] && !PackageLink.closed m #[0,2] &&
    PackageLink.familiesCovered m #[0,1,2] && !PackageLink.familiesCovered m #[1,2])

#eval check "finite literal actuals lower at direct calls and both Bool operands are typed" (Id.run do
  let target : CallTarget := ⟨⟨owner "select"⟩,0,⟨0,[]⟩,[.finite bit],.finite bit⟩
  let term := Core.Term.call 0 [.finiteTag bit "on"] [] tagResult
  let some f := lowerFunction env ⟨1,[]⟩ {core term with id := 1} #[target] | return false
  let yes := Core.Term.binary .and (.boolean true) (.boolean false) boolResult
  let bad := Core.Term.binary .and (.finiteTag bit "on") (.boolean true) boolResult
  return f.blocks[0]?.any (fun b => b.ops.toList.map (·.code.tag) == ["finite.tag.v1","static.call.v1"]) &&
    (lowerFunction env ⟨2,[]⟩ {core yes with returnType := .pure .bool}).isSome &&
    (lowerFunction env ⟨2,[]⟩ {core bad with returnType := .pure .bool}).isNone)

open Lean
private def request (value : Bool) : Json :=
  RegressionRequest.physical (if value then "choiceTrue" else "choiceFalse")

#eval check "same-identity functions with different bodies retain different checked revisions" (Id.run do
  let .ok a := ResourceSource.Wire.check (request true) false | return false
  let .ok b := ResourceSource.Wire.check (request false) false | return false
  let some ma := lowerChecked a | return false
  let some mb := lowerChecked b | return false
  let some ea := ma.execute | return false
  let some f := ea.functions[0]? | return false
  return ma.revision != mb.revision && ma.revision == ea.revision &&
    ma.functions.size == 1 && f.id.owner.name == "choice" &&
    f.specialization.definition == 0 && f.specialization.targets.isEmpty)

end VastitasKernel.MidIR.Regression
