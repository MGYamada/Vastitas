import VastitasKernel.LLVM.Syntax

set_option autoImplicit false

/-! The hosted, pure LLVM instruction grammar for finite SSA modules. Identifiers
in the model exclude the LLVM percent and at-sign sigils. -/
namespace VastitasKernel.LLVM.FiniteModule

inductive Width where
  | bit | word
  deriving Repr, DecidableEq, BEq

inductive Operand where
  | reg (name : String)
  | literal (value : UInt32)
  deriving Repr, DecidableEq, BEq

structure Arg where
  ty : Width
  value : Operand
  deriving Repr, DecidableEq, BEq

inductive Binary where
  | band | bor | add | mul
  deriving Repr, DecidableEq, BEq

inductive Predicate where
  | eq | ne | ult
  deriving Repr, DecidableEq, BEq

inductive Instr where
  | binary (dst : String) (kind : Binary) (ty : Width) (a b : Operand)
  | compare (dst : String) (kind : Predicate) (ty : Width) (a b : Operand)
  | call (dst : String) (ty : Width) (callee : String) (args : List Arg)
  | phi (dst : String) (ty : Width) (incoming : List (Operand × String))
  deriving Repr, DecidableEq, BEq

inductive Exit where
  | ret (arg : Arg)
  | jump (label : String)
  | branch (condition : Operand) (yes no : String)
  | switch (value : Operand) (miss : String) (cases : List (UInt32 × String))
  deriving Repr, DecidableEq, BEq

structure Block where
  label : String
  ops : List Instr
  exit : Exit
  deriving Repr, DecidableEq, BEq

structure Func where
  name : String
  internal : Bool
  result : Width
  params : List (Width × String)
  blocks : List Block
  deriving Repr, DecidableEq, BEq

structure Code where
  header : TargetHeader
  functions : List Func
  deriving DecidableEq

end VastitasKernel.LLVM.FiniteModule
