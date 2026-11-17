import VastitasKernel.IndexedCore

/-! The observations of the entry point (#836). `let name = show!(expr);` at
the top level of the body of `fn main` binds the value of `expr`, and the
native program writes `expr = value` and a line feed to standard error when
it binds it. Core stays pure: an observation is metadata of the entry point,
the position of a top-level `let` of `main` and the text written before the
value. The text is the source text of `expr`; it is presentation only and
never affects acceptance. Native code generation alone sequences the writes
(`Codegen.entryPoint`). -/
namespace VastitasKernel.Indexed.Core

structure Observation where
  /-- The position of a `let` among the top-level statements of the body of `main`. -/
  statement : Nat
  /-- The text written before ` = value`. -/
  label : String
  deriving Repr, Inhabited, DecidableEq, BEq

namespace Observation

/-- `show!` writes a value of type `Int`, `Nat`, `Bool`, `Unit` or `Pair`, and
of no other type. -/
def displayable : DataType → Bool
  | .pure _ => true
  | _ => false

/-- The positions of the observations increase strictly: each statement is
observed at most once, in the order of the statements. -/
def ordered : List Observation → Bool
  | first :: second :: rest => first.statement < second.statement && ordered (second :: rest)
  | _ => true

/-- One top-level statement of an elaborated block. -/
inductive Step where
  | letE (symbol : Nat) (value : Term)
  | unpack (witness : Nat) (fields : List Nat) (package : Term)
  deriving Repr, Inhabited

/-- The first `count` top-level statements of the elaborated body of a block,
and the term after them. Elaboration writes the block `{ s₀; …; sₙ; e }` as
`scope` around one `letE` or `unpack` for each statement, around the rest of
the block (`FunctionSource.Compiler.statementsThen`), and keeps that spine
through reverse compilation. The result `e` can begin with `letE` too, so the
count comes from the source statements. -/
def statements : Nat → Term → Option (List Step × Term)
  | 0, rest => some ([], rest)
  | count + 1, .letE symbol value body =>
    (statements count body).map fun (steps, rest) => (.letE symbol value :: steps, rest)
  | count + 1, .unpack witness fields package body =>
    (statements count body).map fun (steps, rest) => (.unpack witness fields package :: steps, rest)
  | _ + 1, _ => none

/-- The number of top-level statements that code generation binds for
`observations`: up to the last observed one. -/
def extent (observations : List Observation) : Nat :=
  observations.foldl (fun count observation => max count (observation.statement + 1)) 0

end Observation

end VastitasKernel.Indexed.Core
