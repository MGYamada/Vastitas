/-! Runtime for the declaration-driven finite descriptor profile. Canonical
declarations, coefficient markers and nominal identities are checked before
erasure. Descriptor equality never establishes static identity. This implements
only descriptors, origins and identity composites, not arbitrary geometry.
There are deliberately no compiler, oracle or mathlib imports. -/
namespace VastitasKernel.IndexedRuntime

structure Object where
  dimension : Nat
  deriving Repr, DecidableEq

def descriptor (dimension : Nat) : Object := ⟨dimension⟩

/-- A declared canonical base has the zero-dimensional descriptor. Its
declaration identity and marker remain distinct in checked Core. -/
def baseObject : Object := descriptor 0

structure Point where
  target : Object
  source : Object
  deriving Repr, DecidableEq

def origin (object base : Object) : Point := ⟨object, base⟩

structure Morphism where
  source : Object
  target : Object
  deriving Repr, DecidableEq

def identity (object : Object) : Morphism := ⟨object, object⟩

def compose (after before : Morphism) : Morphism := ⟨before.source, after.target⟩

def apply (map : Morphism) (point : Point) : Point := ⟨map.target, point.source⟩

end VastitasKernel.IndexedRuntime
