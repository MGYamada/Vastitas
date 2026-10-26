/-!
The small runtime linked into generated Stage 0 programs.

Nominal object identities and dependent endpoint types are checked before
lowering. They have no observable integer representation at runtime. These
descriptors are not an implementation of arbitrary schemes, smooth algebras,
or all their points: Stage 0 admits affine descriptors, their origin, identity
morphisms, and composites of identity morphisms only.
-/
namespace VastitasKernel.Runtime

inductive Setting where
  | ordinary
  | smooth
  deriving Repr, DecidableEq

inductive Base where
  | qq
  | cinfReal
  deriving Repr, DecidableEq

def Base.setting : Base → Setting
  | .qq => .ordinary
  | .cinfReal => .smooth

structure Object where
  setting : Setting
  base : Base
  dimension : Nat
  deriving Repr, DecidableEq

def affine (base : Base) (dimension : Nat) : Object :=
  { setting := base.setting, base, dimension }

/-- The geometric base object, not its coefficient ring as a scalar value. -/
def baseObject (base : Base) : Object := affine base 0

structure Point where
  target : Object
  source : Object
  deriving Repr, DecidableEq

def origin (object : Object) : Point :=
  { target := object, source := baseObject object.base }

structure Morphism where
  source : Object
  target : Object
  deriving Repr, DecidableEq

def idMap (object : Object) : Morphism :=
  { source := object, target := object }

/-- Compose `g` after `f`; the checker has established the middle endpoint. -/
def composeMap (g f : Morphism) : Morphism :=
  { source := f.source, target := g.target }

/-- Apply an admitted map; the checker has established `p.target = f.source`. -/
def applyMap (f : Morphism) (p : Point) : Point :=
  { target := f.target, source := p.source }

structure Pointed where
  scheme : Object
  point : Point
  deriving Repr, DecidableEq

end VastitasKernel.Runtime
