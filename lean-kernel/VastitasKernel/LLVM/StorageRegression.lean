import VastitasKernel.LLVM.StorageModule

namespace VastitasKernel.LLVM.StorageRegression
open Storage MidIR.StorageEffects StorageModule

private def src : Block .optimization := block [Action.allocate 17 .f32 2, .drop 17]
private def alloc : Call := ⟨.allocate,[0, 2, 2]⟩
private def drop : Call := ⟨.drop,[0]⟩
private def exe : Block .execution := block [alloc, drop]

#guard (verify src exe).isSome
#guard (verify src [⟨0,alloc,1⟩,⟨0,drop,1⟩]).isNone
#guard (verify src (block [drop,alloc])).isNone
#guard !(Call.mk .allocate [2^32,0,1]).valid
#guard !(Call.mk .allocate [0,4,1]).valid
#guard !(Call.mk .fill [0,0,1,1,1,0,2,2^32,0]).valid
#guard !(Call.mk .fill [0,0,1,1,1,0,0,0,1]).valid
#guard (verify src (block [⟨.allocate,[0,0,2]⟩,drop])).isNone
#guard (verify src (block [alloc,⟨.drop,[17]⟩])).isNone
#guard (verify (block [.allocate 17 .f32 2, .drop 17, .drop 17]) exe).isNone

private def header : TargetHeader :=
  ⟨⟨"x86_64-unknown-linux-gnu".toUTF8.data.toList, by decide⟩,
   ⟨"e-p:64:64".toUTF8.data.toList, by decide⟩⟩
private def model : Code := ⟨header,[alloc, drop],42⟩
private def printed := (String.fromUTF8? ⟨model.print.toArray⟩).get!
private def modified (old new : String) := (printed.replace old new).toUTF8.data.toList

#guard parse model.print == some model
#guard (parse (modified "br i1 %ok0, label %next1" "br i1 %ok0, label %next2")).isNone
#guard (parse (modified "call void @vstorage_delete(ptr %arena)" "")).isNone
#guard (parse (modified "call i32" "tail call i32")).isNone
#guard (parse (model.print ++ [32])).isNone
#guard (parse (modified "ret i32 42" "ret i32 43")) != some model

end VastitasKernel.LLVM.StorageRegression
