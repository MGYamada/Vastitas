@[export shifted_matrix_entry]
def shiftedEntry (matrix : (Int × Int) × (Int × Int)) (secondRow secondCol : Bool) : Int :=
  let row := if secondRow then matrix.2 else matrix.1
  let entry := if secondCol then row.2 else row.1
  if secondRow == secondCol then entry - 2 else entry

def main (args : List String) : IO Unit := do
  let offDiagonal := args.head?.bind String.toInt? |>.getD 1
  let transpose := args.length > 1
  IO.println (shiftedEntry ((2, offDiagonal), (0, 2)) transpose (!transpose))
