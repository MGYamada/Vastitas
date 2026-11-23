import VastitasOracle.MidIR
import VastitasKernel.MidIR.Lower
import VastitasKernel.IndexedSemantics
import VastitasKernel.IndexedTypeAudit
import VastitasKernel.RegressionSupport

set_option autoImplicit false

namespace VastitasOracle.MidIR.Regression
open VastitasKernel.Indexed
open VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics

private def owner (n : String) : DeclId := ⟨⟨⟨"/mid", "mid", "1"⟩, []⟩, n⟩
private def carrier : FiniteSort := .carrier (owner "Color")
private def env : Environment := [⟨owner "Color", .finiteCarrier ["blue", "green", "red"]⟩]
private def color : Result := ⟨.finite carrier, none⟩
private def bool : Result := ⟨.pure .bool, none⟩
private def tag (name : String) : Term := .finiteTag carrier name

/-- Two nested diamonds exercise captures from dominating blocks, a phi used
as a later operand, and both outcomes of a nominal comparison. -/
private def choose : Core.Function :=
  { id := 0, definition := owner "choose", parameters := [⟨1, color⟩, ⟨2, bool⟩],
    returnType := color.type,
    body := .letE 3 (.branch (.variable 2 bool) (.variable 1 color) (tag "green") color)
      (.branch (.binary .ne (.variable 3 color) (tag "red") bool)
        (.branch (.variable 2 bool) (tag "blue") (.variable 3 color) color)
        (tag "red") color) }

#eval VastitasKernel.RegressionSupport.check "MidIR observation regression"
    "all six Core inputs agree in both MidIR phases" (Id.run do
  let m : Core.Module := ⟨⟨env, [], []⟩, [choose], none⟩
  let .ok checked := Typing.checkModule m false | return false
  let some source := checked.module.functions.head? | return false
  let some opt := VastitasKernel.MidIR.lowerFunction env ⟨0, []⟩ source | return false
  let some executable := opt.execute env | return false
  for name in ["blue", "green", "red"] do
    for b in [true, false] do
      let args := [Value.finiteTag carrier name, .boolean b]
      let some ctx := bindArguments source.parameters args | return false
      let expected := eval checked.module 16 ctx source.body
      if expected.isNone || run env opt args != expected || run env executable args != expected then
        return false
  return true)

/- Lowering the operand of int(...) may change the active block. Read the
post-join Nat, including a value too large for a machine integer. -/
#eval VastitasKernel.RegressionSupport.check "MidIR Nat conversion"
    "both branch values reach the conversion; forged Bool, duplicate and non-dominating operands fail" (Id.run do
  let nat : Result := ⟨.pure .nat, none⟩
  let large := 2^128 + 43
  let body := Term.natToInt (.branch (.variable 1 bool) (.natural large) (.natural 0) nat)
  let source : Core.Function := ⟨0, owner "convert", [⟨1, bool⟩], .pure .int, body, {}⟩
  let m : Core.Module := ⟨⟨env, [], []⟩, [source], none⟩
  let .ok checked := Typing.checkModule m false | return false
  let [f] := checked.module.functions | return false
  let some opt := VastitasKernel.MidIR.lowerFunction env ⟨0, []⟩ f | return false
  let some exe := opt.execute env | return false
  let some join := opt.blocks[3]? | return false
  let #[op] := join.ops | return false
  unless join.params == #[.nat] && op.code.tag == "nat_to_int.v1" && op.args == [⟨3,0⟩] do return false
  for b in [true, false] do
    let args := [Value.boolean b]
    let some values := bindArguments f.parameters args | return false
    let expected := some (Value.integer (if b then Int.ofNat large else 0))
    unless eval checked.module 8 values body == expected && run env opt args == expected &&
      run env exe args == expected do return false
  for args in [[], [⟨0,0⟩], [⟨3,0⟩, ⟨3,0⟩], [⟨1,0⟩]] do
    let forged := {opt with blocks := opt.blocks.set! 3 {join with ops := #[{op with args}]}}
    if (forged.execute env).isSome then return false
  return true)

/- Both pair operands introduce a join. The second projection must read
the pair constructed from those two SSA results, in their original order. -/
#eval VastitasKernel.RegressionSupport.check "MidIR pair operands"
    "distinct joins preserve field order, signed heap values and pair element types" (Id.run do
  let int : Result := ⟨.pure .int, none⟩
  let large : Int := 2^128 + 43
  let branch := fun symbol x y => Term.branch (.variable symbol bool) (.integer x) (.integer y) int
  for first in [true, false] do
    let pair := Term.pair .int (branch 1 (-large) 7) (branch 2 19 large)
    let source : Core.Function := ⟨0, owner "field", [⟨1,bool⟩, ⟨2,bool⟩], .pure .int, .project .int first pair, {}⟩
    let m : Core.Module := ⟨⟨env, [], []⟩, [source], none⟩
    let .ok checked := Typing.checkModule m false | return false
    let some opt := VastitasKernel.MidIR.lowerFunction env ⟨0,[]⟩ source | return false
    let some exe := opt.execute env | return false
    let some join := opt.blocks[6]? | return false
    let #[make, read] := join.ops | return false
    unless make.code.tag == "int_pair.v1" && make.args == [⟨3,0⟩, ⟨6,0⟩] &&
        read.args == [⟨6,1⟩] && read.code.tag == (if first then "int_pair_first.v1" else "int_pair_second.v1") do
      return false
    for a in [true, false] do
      for b in [true, false] do
        let args := [Value.boolean a, .boolean b]
        let some values := bindArguments source.parameters args | return false
        let expected := some (Value.integer (if first then (if a then -large else 7) else (if b then 19 else large)))
        unless eval checked.module 12 values source.body == expected && run env opt args == expected &&
            run env exe args == expected do return false
    for bad in [#[{make with args := [⟨3,0⟩]}, read],
        #[make, {read with code := .exactOp (.project .nat first)}],
        #[make, {read with args := [⟨6,0⟩]}]] do
      if ({opt with blocks := opt.blocks.set! 6 {join with ops := bad}}.execute env).isSome then return false
  return true)

#eval VastitasKernel.RegressionSupport.check "MidIR unary operators"
    "a negated guard and signed literals reach boxed negation through their join" (Id.run do
  let int : Result := ⟨.pure .int, none⟩
  let large : Int := 2^128 + 43
  let signed := Term.unary .neg (.integer large) int
  let cond := Term.unary .not (.variable 1 bool) bool
  let body := Term.unary .neg (.branch cond signed (.integer 7) int) int
  let f : Core.Function := ⟨0, owner "negate", [⟨1, bool⟩], int.type, body, {}⟩
  let m : Core.Module := ⟨⟨env, [], []⟩, [f], none⟩
  let .ok checked := Typing.checkModule m false | return false
  let some opt := VastitasKernel.MidIR.lowerFunction env ⟨0, []⟩ f | return false
  let some exe := opt.execute env | return false
  let some entry := opt.blocks[0]? | return false
  let some yes := opt.blocks[1]? | return false
  let some join := opt.blocks[3]? | return false
  let #[guardOp] := entry.ops | return false
  let #[folded] := yes.ops | return false
  let #[neg] := join.ops | return false
  unless guardOp.code == .boolNot && folded.code == .integer (-large) && folded.args.isEmpty &&
      neg.code == .exactOp .neg && neg.args == [⟨3,0⟩] do return false
  for b in [true, false] do
    let args := [Value.boolean b]
    let some values := bindArguments f.parameters args | return false
    let expected := some (Value.integer (if b then -7 else large))
    unless eval checked.module 8 values body == expected && run env opt args == expected &&
        run env exe args == expected do return false
  for bad in [{neg with code := .boolNot}, {neg with args := []}, {neg with args := [⟨3,0⟩, ⟨3,0⟩]}] do
    if ({opt with blocks := opt.blocks.set! 3 {join with ops := #[bad]}}.execute env).isSome then return false
  let unsupported := {f with body := .unary .neg (.natural 1) int}
  if (Typing.checkModule {m with functions := [unsupported]} false).isOk then return false
  return true)

/- Argument order remains observable even when both formal types are the
same nominal carrier. Run the exact checked Core and both linked phases. -/
#eval VastitasKernel.RegressionSupport.check "MidIR static call regression"
    "a two-argument call forwards the chosen operand order" (Id.run do
  let pick : Core.Function := ⟨0, owner "first", [⟨10,color⟩,⟨11,color⟩], color.type,
    .variable 10 color, {}⟩
  for swap in [false, true] do
    let args : List Core.Term := if swap then [.variable 21 color,.variable 20 color]
      else [.variable 20 color,.variable 21 color]
    let caller : Core.Function := ⟨1, owner "call", [⟨20,color⟩,⟨21,color⟩], color.type,
      .call 0 args [] color, {}⟩
    let core : Core.Module := ⟨⟨env,[],[]⟩,[pick,caller],none⟩
    let .ok checked := Typing.checkModule core false | return false
    let [leaf,forward] := checked.module.functions | return false
    let some first := VastitasKernel.MidIR.lowerFunction env ⟨0,[]⟩ leaf | return false
    let some call := VastitasKernel.MidIR.lowerFunction env ⟨1,[]⟩ forward #[first.target] | return false
    let opt := VastitasKernel.MidIR.Module.mk .null env #[first,call] none
    let some exe := opt.execute | return false
    let values := [Value.finiteTag carrier "red", Value.finiteTag carrier "green"]
    let expected := some (Value.finiteTag carrier (if swap then "green" else "red"))
    let some ctx := bindArguments forward.parameters values | return false
    if eval checked.module 8 ctx forward.body != expected ||
        invoke opt 2 call.target values != expected || invoke exe 2 call.target values != expected ||
        (invoke exe 1 call.target values).isSome then return false
  return true)

/- One family can own several method specializations, but a dense symbol
number cannot authorize a duplicate key or let a call substitute its sibling. -/
#eval VastitasKernel.RegressionSupport.check "MidIR method identity"
    "distinct specializations share an owner; duplicate keys and redirected calls fail" (Id.run do
  let first : VastitasKernel.MidIR.Function .optimization :=
    ⟨⟨owner "pick"⟩,0,⟨4,[]⟩,#[.bool],.bool,#[⟨#[.bool],#[],.ret ⟨0⟩ ⟨0,0⟩⟩]⟩
  let second := { first with coreId := 1, specialization := ⟨3,[]⟩ }
  let module := VastitasKernel.MidIR.Module.mk .null [] #[first,second] none
  unless VastitasKernel.MidIR.validSymbols module do return false
  let duplicate := { second with specialization := first.specialization }
  if VastitasKernel.MidIR.validSymbols { module with functions := #[first,duplicate] } then return false
  let forged := { first.target with symbol := second.coreId }
  let caller := { first with
    id := ⟨owner "caller"⟩, coreId := 2, specialization := ⟨0,[]⟩
    blocks := #[⟨#[.bool],#[⟨.call forged,[⟨0,0⟩]⟩],.ret ⟨0⟩ ⟨0,1⟩⟩] }
  return !(VastitasKernel.MidIR.validSymbols { module with functions := #[first,second,caller] }))

end VastitasOracle.MidIR.Regression
