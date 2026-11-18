/- Represent a permutation by its three point images. Composition computes
those images instead of reading the 36 rows in the Vastitas source. -/
def permutations : List (List Nat) :=
  [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]

def compose (row col : Nat) : Option Nat := do
  let g ← permutations[row]?
  let f ← permutations[col]?
  permutations.idxOf? (← f.mapM (fun i => g[i]?))

def main : IO Unit := do
  let ordinals := [0,1,2,3,4,5,6,7,4294967295]
  for g in ordinals do
    for f in ordinals do IO.println ((compose g f).getD 4294967295)
