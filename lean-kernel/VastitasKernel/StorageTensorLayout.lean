import VastitasKernel.StorageLayout

/-! Bounded physical axis grouping, with no nominal basis or factor ownership. -/
namespace VastitasKernel.Storage.Tensor

structure Grouping where
  order : List Nat
  split : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def Grouping.Valid (grouping : Grouping) (rank : Nat) : Prop :=
  grouping.order.Perm (List.range rank) ∧ 0 < grouping.split ∧ grouping.split < rank
instance (grouping : Grouping) (rank : Nat) : Decidable (grouping.Valid rank) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Grouping.extent (dimensions axes : List Nat) : Nat :=
  (axes.map fun axis => (dimensions[axis]?).getD 0).foldl (· * ·) 1

def Grouping.rows (grouping : Grouping) (dimensions : List Nat) : Nat :=
  Grouping.extent dimensions (grouping.order.take grouping.split)

def Grouping.columns (grouping : Grouping) (dimensions : List Nat) : Nat :=
  Grouping.extent dimensions (grouping.order.drop grouping.split)

/-- Rank-three native code: three base-three axis digits and a one/two split.
Native preflight independently decodes and validates it. -/
def Grouping.code (grouping : Grouping) : Nat :=
  (grouping.order[0]?).getD 0 + 3 * (grouping.order[1]?).getD 0 +
    9 * (grouping.order[2]?).getD 0 + 27 * (grouping.split - 1)

def Grouping.flatten (dimensions indices order : List Nat) : Nat :=
  order.foldr (fun axis next => (indices[axis]?).getD 0 + (dimensions[axis]?).getD 0 * next) 0

def Grouping.coordinate (grouping : Grouping) (dimensions indices : List Nat) : Nat × Nat :=
  (Grouping.flatten dimensions indices (grouping.order.take grouping.split),
    Grouping.flatten dimensions indices (grouping.order.drop grouping.split))

end VastitasKernel.Storage.Tensor
