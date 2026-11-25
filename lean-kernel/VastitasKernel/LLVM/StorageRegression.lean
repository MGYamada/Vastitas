import VastitasKernel.LLVM.StorageModule

namespace VastitasKernel.LLVM.StorageRegression
open Storage MidIR.StorageEffects StorageModule

private def src : Block .optimization := block [Action.allocate 17 .f32 2, .drop 17]
private def alloc : Call := ⟨.allocate,[0, 2, 2], []⟩
private def drop : Call := ⟨.drop,[0], []⟩
private def exe : Block .execution := block [alloc, drop]

#guard (verify src exe).isSome
#guard (verify src [⟨0,alloc,1⟩,⟨0,drop,1⟩]).isNone
#guard (verify src (block [drop,alloc])).isNone
#guard !(Call.mk .allocate [2^32,0,1] []).valid
#guard !(Call.mk .allocate [0,4,1] []).valid
#guard !(Call.mk .fill [0,0,1,1,1,0,2,2^32,0] []).valid
#guard !(Call.mk .fill [0,0,1,1,1,0,0,0,1] []).valid
#guard (verify src (block [⟨.allocate,[0,0,2], []⟩,drop])).isNone
#guard (verify src (block [alloc,⟨.drop,[17], []⟩])).isNone
#guard (verify (block [.allocate 17 .f32 2, .drop 17, .drop 17]) exe).isNone

private def one : Layout := ⟨0, 1, 1, 1, false⟩
private def matrixOps (element : Scalar) : List Native.Instruction :=
  [.allocate 0 element 1, .allocate 1 element 1, .allocate 2 element 1,
   .gemm 0 one false 1 one false 2 one .overwrite .nativeFast]
private def matrixCall (tag : Nat) : Call :=
  ⟨.gemm, [tag, 0, 0,1,1,1,0, 0, 1, 0,1,1,1,0, 0, 2, 0,1,1,1,0, 0] ++ List.replicate 12 0, []⟩

#guard [(.f64,0),(.complexF64,1),(.f32,2),(.complexF32,3)].all fun (s,tag) =>
  ((resolveCalls (matrixOps s)).bind List.getLast?) == some (matrixCall tag) && (matrixCall tag).valid
#guard !(Call.mk .gemm ((matrixCall 2).arguments.set 20 1) []).valid
#guard !(Call.mk .gemm ((matrixCall 2).arguments.set 22 1) []).valid
#guard !(Call.mk .gemm ((matrixCall 0).arguments.set 28 1) []).valid
#guard (resolveCalls ([.allocate 0 .f32 1, .allocate 1 .f64 1, .allocate 2 .f32 1] ++
  (matrixOps .f32).drop 3)).isNone
#guard (resolveCalls ((matrixOps .complexF32).take 3 ++ [.drop 0] ++ (matrixOps .complexF32).drop 3)).isNone

private def sourceView : Layout := ⟨8, 2, 12, 3, false⟩
private def packedView : Layout := ⟨16, 8, 3, 9, false⟩
private def pack : Call := ⟨.pack3, [4,8,2,12,3,0, 7,16,8,3,9,0, 2,3,4], []⟩
private def regroup : Call := ⟨.regroup3, pack.arguments ++ [21,42], []⟩

#guard resolveInstruction {} (.pack3 4 sourceView 7 packedView 2 3 4) == some pack
#guard resolveInstruction {} (.regroup3 4 sourceView 7 packedView [2,3,4] ⟨[0,1,2],1⟩ ⟨[0,2,1],2⟩) == some regroup
#guard pack.valid && regroup.valid
#guard !(Call.mk .pack3 (pack.arguments.set 5 1) []).valid
#guard !(Call.mk .pack3 (pack.arguments.set 11 1) []).valid
#guard !(Call.mk .pack3 (pack.arguments.set 3 6) []).valid
#guard !(Call.mk .pack3 [4,0,0,0,1,0, 7,0,0,0,1,0, 0,0,2^31] []).valid
#guard (Call.mk .pack3 [4,0,0,0,1,0, 7,0,0,0,1,0, 0,0,2^31-1] []).valid
#guard !(Call.mk .regroup3 (regroup.arguments.set 15 0) []).valid
#guard !(Call.mk .regroup3 (regroup.arguments.set 16 54) []).valid
#guard !(Call.mk .regroup3 (regroup.arguments.set 16 21) []).valid
#guard (resolveInstruction {} (.regroup3 4 sourceView 7 packedView [2,3] ⟨[0,1,2],1⟩ ⟨[0,2,1],2⟩)).isNone
#guard (resolveInstruction {} (.regroup3 4 sourceView 7 packedView [2,3,4] ⟨[0,1,2,0],1⟩ ⟨[0,2,1],2⟩)).isNone

private def header : TargetHeader :=
  ⟨⟨"x86_64-unknown-linux-gnu".toUTF8.data.toList, by decide⟩,
   ⟨"e-p:64:64".toUTF8.data.toList, by decide⟩⟩
private def model : Code := ⟨header,[alloc, drop],42⟩
private def printed := (String.fromUTF8? ⟨model.print.toArray⟩).get!
private def modified (old new : String) := (printed.replace old new).toUTF8.data.toList

#guard parse model.print == some model
private def packingModel : Code := ⟨header, [pack, regroup], 0⟩
#guard parse packingModel.print == some packingModel
#guard (parse ({ packingModel with calls := [⟨.regroup3, regroup.arguments.set 16 0, []⟩] }).print).isNone
#guard (parse (modified "br i1 %ok0, label %next1" "br i1 %ok0, label %next2")).isNone
#guard (parse (modified "call void @vstorage_delete(ptr %arena)" "")).isNone
#guard (parse (modified "call i32" "tail call i32")).isNone
#guard (parse (model.print ++ [32])).isNone
#guard (parse (modified "ret i32 42" "ret i32 43")) != some model

private def weights : Diagonal := ⟨false, [0xc000000000000000]⟩
private def targetWeight : Diagonal := ⟨true, [0x4008000000000000]⟩
private def adjoint : Call := ⟨.diagonalAdjoint, [2,0,0,1,1,1,0,1,0,1,1,1,0,1], [weights,targetWeight]⟩
private def adjointModel : Code := ⟨header, [adjoint, adjoint], 0⟩
private def adjointText := String.fromUTF8! ⟨adjointModel.print.toArray⟩
private def edit (before after : String) := (adjointText.replace before after).toUTF8.data.toList
#guard adjoint.valid && parse adjointModel.print == some adjointModel
#guard (adjointText.splitOn " = private constant [").length == 3
#guard (parse (edit "ptr @vq_diag1" "ptr @vq_diag2")).isNone
#guard (parse (edit "ptr @vq_diag1, i64 8" "ptr @vq_diag1, i64 4")).isNone
#guard (parse (edit "i64 8, i64 1)" "i64 8, i64 2)")).isNone
#guard (parse (edit "\\C0" "\\c0")).isNone
#guard (parse (edit "private constant" "private global")).isNone
#guard (parse (edit "\\C0" "\\40")) != some adjointModel
#guard !({adjoint with diagonals := [weights]}).valid
#guard !({adjoint with diagonals := [⟨false, []⟩, targetWeight]}).valid
#guard !({drop with diagonals := [weights]}).valid
#guard let tooLarge : Diagonal := ⟨true, [(diagonalBits (2^24+1)).get!]⟩
  !({adjoint with diagonals := [weights, tooLarge]}).valid &&
    ({adjoint with arguments := adjoint.arguments.set 0 0, diagonals := [weights, tooLarge]}).valid
#guard [(.f64,0),(.complexF64,1),(.f32,2),(.complexF32,3)].all fun (scalar,tag) =>
  let op := resolveInstruction (Std.HashMap.ofList [(0, scalar),(1, scalar)])
    (.diagonalScale 0 one 1 one weights true .nativeFast)
  op == some ⟨.diagonalScale, adjoint.arguments.set 0 tag, [weights]⟩ &&
    op.any Call.valid
#guard (resolveInstruction (Std.HashMap.ofList [(0,.f32),(1,.f64)])
  (.diagonalAdjoint 0 one 1 one weights targetWeight true .nativeFast)).isNone
#guard (DiagonalConstant.readLine 0 (DiagonalConstant.line 0 [])) == some []
#guard (DiagonalConstant.readLine 1 (DiagonalConstant.line 0 weights.entries)).isNone
#guard let entries := (List.range 4096).map Nat.toUInt64
  DiagonalConstant.readLine 0 (DiagonalConstant.line 0 entries) == some entries

end VastitasKernel.LLVM.StorageRegression
