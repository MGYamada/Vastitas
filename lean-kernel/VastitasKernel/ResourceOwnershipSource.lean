import VastitasKernel.ResourceLiteralText
import VastitasKernel.ResourceStatementSource

set_option autoImplicit false

/-! Match resource owners, loans and layouts against the statements that create,
transfer and release them in each physical function. Loan legality and byte
initialization are checked by the storage checker. -/
namespace VastitasKernel.ResourceOwnershipSource
open AssemblyText ResourceSource SourceText ResourceStatementSource

private def accessName : Storage.Access → String
  | .read => "read" | .write => "write" | .readWrite => "read_write"

private def extent : RuntimeExtent → ExactLexeme
  | .literal n => .dimension n
  | .slot name => .ident name

private def layoutFields (offset : Option Nat) (rows columns leading : ExactLexeme)
    (transposed : Bool) : List ExactLexeme :=
  [.ident (if offset.isSome then "layout" else "runtime_layout"), .punctuation '('] ++
  ((offset.toList.map ExactLexeme.dimension ++ [rows, columns, leading, .ident (toString transposed)]).intersperse
    (.punctuation ',')) ++ [.punctuation ')']

private def allocation (keyword owner : String) (scalar : Storage.Scalar) (elements : ExactLexeme) : List ExactLexeme :=
  [.ident keyword, .ident owner, .punctuation ':'] ++ ExactModelSource.storageRepresentation scalar ++
  [.punctuation '[', elements, .punctuation ']']

private def borrow (keyword name owner : String) (access : Storage.Access) (layout : List ExactLexeme) : List ExactLexeme :=
  [.ident keyword, .ident name, .punctuation '=', .ident (accessName access), .punctuation '(', .ident owner] ++
  layout ++ [.punctuation ')']

private def unary (keyword name : String) : List ExactLexeme :=
  [.ident keyword, .punctuation '(', .ident name, .punctuation ')']

def spelling? : Statement → Option (List ExactLexeme × Span)
  | .action (.allocate owner scalar elements) s => some (allocation "allocate" owner scalar (.dimension elements), s)
  | .runtime (.allocate owner scalar elements l) s =>
    some (allocation "runtime_allocate" owner scalar (extent elements) ++
      layoutFields none (extent l.rows) (extent l.columns) (extent l.leading) l.transposed, s)
  | .action (.borrow name owner l access) s =>
    some (borrow "borrow" name owner access (.punctuation ',' ::
      layoutFields (some l.offset) (.dimension l.rows) (.dimension l.columns) (.dimension l.leading) l.transposed), s)
  | .numerical (.borrowOwned name owner access) s => some (borrow "borrow" name owner access [], s)
  | .runtime (.borrow name owner access) s => some (borrow "runtime_borrow" name owner access [], s)
  | .action (.move src dst) s => some ([.ident "move", .ident src, .arrow, .ident dst], s)
  | .runtime (.move src dst) s => some ([.ident "runtime_move", .ident src, .arrow, .ident dst], s)
  | .action (.release name) s => some (unary "release" name, s)
  | .runtime (.release name) s => some (unary "runtime_release" name, s)
  | .action (.drop name) s => some (unary "drop" name, s)
  | .runtime (.drop name) s => some (unary "runtime_drop" name, s)
  | .action (.transpose name) s => some (unary "transpose" name, s)
  | .action (.copy src dst) s =>
    some ([.ident "copy", .punctuation '(', .ident src, .punctuation ',', .ident dst, .punctuation ')'], s)
  | _ => none

def replay (f : File) (before : Cursor) (fields : List ExactLexeme) (span : Span) : Except Diagnostic Token :=
  runStatement (do
    for field in fields do
      match field with
      | .dimension n => consume fun file cursor => ResourceLiteralText.expectNat file cursor n
      | _ => token field) f before span

abbrev items := ResourceStatementSource.items spelling?
abbrev Corresponds := ResourceStatementSource.Corresponds replay
abbrev check := ResourceStatementSource.check replay

end VastitasKernel.ResourceOwnershipSource
