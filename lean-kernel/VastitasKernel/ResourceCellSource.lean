import VastitasKernel.ResourceStatementSource
import VastitasKernel.ResourceLiteralText

set_option autoImplicit false

/-! Match every static or runtime literal cell operation after storage checking,
including statements in uncalled functions and both arms of resource branches. -/
namespace VastitasKernel.ResourceCellSource
open AssemblyText ResourceSource SourceText ResourceStatementSource

structure Cell where
  operation : String
  loan : String
  coordinates : Option (Nat × Nat)
  literal : Storage.Literal

def cell? : Statement → Option (Cell × Span)
  | .action (.fill loan v) s => some (⟨"fill", loan, none, v⟩, s)
  | .action (.store loan r c v) s => some (⟨"store", loan, some (r,c), v⟩, s)
  | .action (.expect loan r c v) s => some (⟨"expect", loan, some (r,c), v⟩, s)
  | .runtime (.fill loan v) s => some (⟨"runtime_fill", loan, none, v⟩, s)
  | .runtime (.expect loan r c v) s => some (⟨"runtime_expect", loan, some (r,c), v⟩, s)
  | _ => none

def replay (f : File) (before : Cursor) (cell : Cell) (span : Span) : Except Diagnostic Token := do
  let parser : Parser Unit := do
    token (.ident cell.operation)
    token (.punctuation '(')
    token (.ident cell.loan)
    token (.punctuation ',')
    if let some (r,c) := cell.coordinates then
      consume fun f p => ResourceLiteralText.expectNat f p r
      token (.punctuation ',')
      consume fun f p => ResourceLiteralText.expectNat f p c
      token (.punctuation ',')
    consume fun f p => ResourceLiteralText.check f p cell.literal
    token (.punctuation ')')
  runStatement parser f before span

abbrev items := ResourceStatementSource.items cell?
abbrev Corresponds := ResourceStatementSource.Corresponds replay
abbrev check := ResourceStatementSource.check replay

theorem check_sound {layout sites cells} (h : check layout sites cells = .ok ()) :
    Finite.sameCounts sites.keys (cells.map (·.span.start)) = true ∧
    ∀ i ∈ cells, Corresponds layout sites i := ResourceStatementSource.check_sound h

end VastitasKernel.ResourceCellSource
