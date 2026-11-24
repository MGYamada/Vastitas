import VastitasKernel.LLVM.FiniteModule
import VastitasKernel.LLVM.FiniteExecution

set_option autoImplicit false
namespace VastitasKernel.LLVM.FiniteModule.Regression

private def header : TargetHeader :=
  ⟨⟨[120],by decide⟩,⟨[101],by decide⟩⟩

private def jump (b target : String) : Block := ⟨b,[],.jump target⟩
private def ret (n : UInt32) : Exit := .ret ⟨.word,.literal n⟩
private def app (blocks : List Block) : Code := ⟨header,[⟨"main",false,.word,[],blocks⟩]⟩
private def choice (x : UInt32) (y n : String) : Block := ⟨"start",[],.branch (.literal x) y n⟩
private def join (ys : List String) : Block := ⟨"out",[.phi "v" .word (ys.map (fun y => (.literal 1,y)))],.ret ⟨.word,.reg "v"⟩⟩
private def diamond := [choice 1 "a" "b", jump "a" "out", jump "b" "out"]

#guard (parse (app (diamond ++ [join ["a","b"]])).print).isSome
#guard (parse ((app (diamond ++ [join ["a","b"]])).print ++ [32])).isNone
#guard (parse (app [choice 1 "out" "out",join ["start"]]).print).isNone
#guard (parse (app (diamond ++ [join ["a"]])).print).isNone
#guard (parse (app (diamond ++ [join ["a","a"]])).print).isNone
#guard (parse (app [choice 2 "a" "b",⟨"a",[],ret 1⟩,⟨"b",[],ret 0⟩]).print).isNone
#guard (parse (app [⟨"42",[],ret 1⟩]).print).isNone
#guard (parse (app [⟨"start",[.binary "start" .add .word (.literal 0) (.literal 1)],ret 1⟩]).print).isNone
#guard (parse (app [⟨"start",[.call "r" .word "missing" []],.ret ⟨.word,.reg "r"⟩⟩]).print).isNone
#guard (parse (app [
  choice 1 "a" "b",⟨"a",[.binary "v" .add .word (.literal 0) (.literal 1)],.jump "out"⟩,
  jump "b" "out",⟨"out",[],.ret ⟨.word,.reg "v"⟩⟩]).print).isNone

/-- The predecessors send opposite Boolean slots and different word slots to
the same three-parameter join. All five input registers dominate both arms. -/
private def joinedArguments (flag a b : UInt32) : Option UInt32 := do
  let owner : Indexed.DeclId := ⟨⟨⟨"/join", "test", "1"⟩, []⟩, "Color"⟩
  let tag : Indexed.FiniteSort := .carrier owner
  let env : Indexed.Environment := [⟨owner, .finiteCarrier ["zero","left","right"]⟩]
  let params : Array MidIR.Ty := #[.bool,.bool,.bool,.finite tag,.finite tag]
  let f : MidIR.Function .optimization := ⟨⟨{owner with name := "pick"}⟩, 0, ⟨0,[]⟩, params, .finite tag, #[
    ⟨params, #[], .branch ⟨0,0⟩ ⟨1,⟨0⟩,[]⟩ ⟨2,⟨0⟩,[]⟩⟩,
    ⟨#[], #[], .jump ⟨3,⟨1⟩,[⟨0,1⟩,⟨0,2⟩,⟨0,3⟩]⟩⟩,
    ⟨#[], #[], .jump ⟨3,⟨2⟩,[⟨0,2⟩,⟨0,1⟩,⟨0,4⟩]⟩⟩,
    ⟨#[.bool,.bool,.finite tag], #[⟨.boolNot,[⟨3,1⟩]⟩,⟨.boolAnd,[⟨3,0⟩,⟨3,3⟩]⟩],
      .branch ⟨3,4⟩ ⟨4,⟨3⟩,[]⟩ ⟨5,⟨3⟩,[]⟩⟩,
    ⟨#[], #[], .ret ⟨4⟩ ⟨3,2⟩⟩,
    ⟨#[], #[⟨.finiteTag tag "zero",[]⟩], .ret ⟨5⟩ ⟨5,0⟩⟩]⟩
  let exe ← f.execute env
  let image ← translateFn env 1 exe
  let host := app [⟨"start",[],ret 0⟩]
  let model ← parse ({host with functions := image.body 0 :: host.functions}).print
  model.code.invoke "f0" [(.bit,flag),(.bit,a),(.bit,b),(.word,1),(.word,2)] 64

#guard joinedArguments 1 1 0 == some 1
#guard joinedArguments 0 1 0 == some 0
#guard joinedArguments 1 0 1 == some 0
#guard joinedArguments 0 0 1 == some 2

private def rectangular (dims rows : List Nat) (digits : List UInt32) : Option UInt32 := do
  let helper ← table "lookupTable" dims rows
  let f := (app [⟨"start",[],ret 0⟩]).functions
  let m ← certify ⟨header,helper :: f⟩
  m.code.invoke "lookupTable" (digits.map (fun x => (.word,x))) 64

#guard rectangular [2,3] [1,4,0,5,3,2] [0,1] == some 4
#guard rectangular [2,3] [1,4,0,5,3,2] [1,0] == some 5
#guard rectangular [2,3] [1,4,0,5,3,2] [1,2] == some 2
#guard rectangular [2,3] [1,4,0,5,3,2] [0,3] == some 0xffffffff
#guard rectangular [2,3] [1,4,0,5,3,2] [0xffffffff,0] == some 0xffffffff
#guard rectangular [0,3] [] [0,0] == some 0xffffffff
#guard rectangular [2,0] [] [0,0] == some 0xffffffff
#guard rectangular [3] [1,0,2] [1] == some 0
#guard rectangular [0] [] [0] == some 0xffffffff

#guard rectangular [] [9] [] == some 9
#guard (rectangular [] [9] [0]).isNone
#guard (table "badTable" [] []).isNone
#guard (table "badTable" (List.replicate 7 1) [1]).isNone
#guard ((List.range 12).all fun i =>
  rectangular [2,3,2] (List.range 12) [(i/6).toUInt32,((i/2)%3).toUInt32,(i%2).toUInt32] == some i.toUInt32)
#guard ([[2,0,0], [0,3,0], [0,0,2], [0xffffffff,0,0], [0,0xffffffff,0], [0,0,0xffffffff]].all fun digits =>
  rectangular [2,3,2] (List.range 12) digits == some 0xffffffff)
#guard rectangular [2,0,3] [] [1,0,2] == some 0xffffffff
#guard rectangular [2,3,0] [] [1,2,0] == some 0xffffffff
#guard rectangular [2,1,1,1,1,2] [8,5,3,2] [1,0,0,0,0,1] == some 2
#guard rectangular [2,1,1,1,1,2] [8,5,3,2] [0,0,0,1,0,0] == some 0xffffffff

end VastitasKernel.LLVM.FiniteModule.Regression
