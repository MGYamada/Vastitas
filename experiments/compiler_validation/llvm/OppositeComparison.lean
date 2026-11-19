/-! Independent calculation for the opposite S3 executable. A permutation
acts on three points. The group operations here use its images directly. -/
namespace OppositeComparison

abbrev Perm := List Nat

def permutations : List Perm := [[0,1,2], [0,2,1], [1,0,2], [1,2,0], [2,0,1], [2,1,0]]

@[noinline] def compose (after before : Perm) : Perm := before.map fun i => after[i]!
@[noinline] def inverse (p : Perm) : Perm := [0,1,2].map fun i => p.idxOf i
@[noinline] def opposite (after before : Perm) : Perm := compose before after

def status : UInt32 :=
  let g := [0,2,1]
  let f := [1,0,2]
  let reversed := opposite g f
  let twice := opposite f g
  let laws := permutations.all fun h => permutations.all fun k =>
    inverse (compose h k) == compose (inverse k) (inverse h)
  if reversed == [1,2,0] && twice == [2,0,1] && inverse reversed == twice && laws then 42 else 7

end OppositeComparison

def main : IO UInt32 := pure OppositeComparison.status
