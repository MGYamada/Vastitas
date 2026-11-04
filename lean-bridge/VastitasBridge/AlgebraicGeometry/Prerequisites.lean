module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Mathlib prerequisites of the implementation correspondence

The correspondence files import the non-module kernel and Oracle sources, so they cannot be
modules themselves. They import Mathlib through this module instead of directly.
-/
