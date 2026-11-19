import VastitasOracle.FiniteMapTotal

/-! Identities and composition on the Hom fibers of a checked finite graph.
Taking the opposite changes the indices and the order of one lookup. The
original graph, arrow tags, identity table and composable pairs are shared. -/
namespace VastitasOracle.FiniteCategoryExecution
open VastitasKernel VastitasKernel.Indexed Indexed.FiniteCategories

variable {p : Source.Program} (checked : Source.CheckedDeclarations p)
variable {m : FiniteHom.Model checked.resolved.declarations.indexed owner}

private theorem graph_laws (m : FiniteHom.Model checked.resolved.declarations.indexed owner) :
    (∀ x ∈ m.data.objects, m.data.identityAt x = true) ∧
    (∀ f ∈ m.data.arrows, m.data.units f = true) ∧
    (∀ g ∈ m.data.arrows, ∀ f ∈ m.data.arrows, m.data.composable g f = true →
      m.data.ends g f = true ∧ ∀ h ∈ m.data.arrows, m.data.composable h g = true →
        m.data.assoc h g f = true) := by
  obtain ⟨_, found, laws⟩ := FiniteCategories.checked_category checked (lookup_member m.declared)
  rw [m.selected] at found
  cases found
  exact laws

abbrev Object (m : FiniteHom.Model env owner) := { x : String // x ∈ m.data.objects }

private theorem identity_exists (x : Object m) :
    ∃ f : FiniteHom.Hom m x.val x.val, FiniteHom.identity? m x.val = some f ∧
      m.data.identity[[x.val]]? = some f.tag := by
  have tables := FiniteMapTotal.graph_tables m.selected
  obtain ⟨tag, mem, row⟩ := FiniteMapTotal.mapping_total m.accepted tables.2.2 tables.1 tables.2.1 x.property
  change m.data.identity[[x.val]]? = some tag at row
  have ends := (graph_laws checked m).1 x.val x.property
  have e : m.data.src[[tag]]? = some x.val ∧ m.data.dst[[tag]]? = some x.val := by
    simpa [Graph.identityAt, row] using ends
  exact ⟨⟨tag, mem, e.1, e.2⟩, by simp [FiniteHom.identity?, FiniteHom.fromTag?, x.property, row, mem, e, guard], row⟩

def identity (x : Object m) : FiniteHom.Hom m x.val x.val :=
  (FiniteHom.identity? m x.val).get (by obtain ⟨_, h, _⟩ := identity_exists checked x; simp [h])

theorem identity_row (x : Object m) : m.data.identity[[x.val]]? = some (identity checked x).tag := by
  obtain ⟨f, h, row⟩ := identity_exists checked x
  have actual : FiniteHom.identity? m x.val = some (identity checked x) := (Option.some_get _).symm
  exact Option.some.inj (actual.symm.trans h) ▸ row

private theorem tag_ext {m : FiniteHom.Model env owner} {f g : FiniteHom.Hom m x y} (same : f.tag = g.tag) : f = g := by
  cases f; cases g; cases same; rfl

theorem composable {m : FiniteHom.Model env owner} (g : FiniteHom.Hom m y z) (f : FiniteHom.Hom m x y) :
    m.data.composable g.tag f.tag = true := by
  simp [Endpoints.composable, g.src, f.dst]

theorem compose_units {x y : Object m} (f : FiniteHom.Hom m x.val y.val) :
    compose checked (identity checked y) f = f ∧ compose checked f (identity checked x) = f := by
  have eq := FiniteCategories.unit_equations ((graph_laws checked m).2.1 f.tag f.member)
    f.src f.dst (identity_row checked y) (identity_row checked x)
  exact ⟨tag_ext (Option.some.inj ((compose_uses_selected_row checked _ _).symm.trans eq.1)),
    tag_ext (Option.some.inj ((compose_uses_selected_row checked _ _).symm.trans eq.2))⟩

theorem compose_assoc (h : FiniteHom.Hom m z w) (g : FiniteHom.Hom m y z) (f : FiniteHom.Hom m x y) :
    compose checked (compose checked h g) f = compose checked h (compose checked g f) := by
  have law := ((graph_laws checked m).2.2 g.tag g.member f.tag f.member (composable g f)).2
    h.tag h.member (composable h g)
  obtain ⟨_, left, right⟩ := FiniteCategories.associative_equation law
    (compose_uses_selected_row checked g f) (compose_uses_selected_row checked h g)
  exact tag_ext (Option.some.inj ((compose_uses_selected_row checked _ _).symm.trans
    (right.trans (left.symm.trans (compose_uses_selected_row checked _ _)))))

namespace Opposite

abbrev Hom (m : FiniteHom.Model env owner) (x y : String) := FiniteHom.Hom m y x

def compose (g : Hom m y z) (f : Hom m x y) : Hom m x z := FiniteCategoryExecution.compose checked f g

/-- An opposite composition reads one row of the selected base graph. -/
theorem compose_row (g : Hom m y z) (f : Hom m x y) :
    m.data.composition[[f.tag, g.tag]]? = some (compose checked g f).tag :=
  compose_uses_selected_row checked f g

theorem units {x y : Object m} (f : Hom m x.val y.val) :
    compose checked (identity checked y) f = f ∧ compose checked f (identity checked x) = f :=
  (compose_units checked f).symm

theorem assoc (h : Hom m z w) (g : Hom m y z) (f : Hom m x y) :
    compose checked (compose checked h g) f = compose checked h (compose checked g f) :=
  (compose_assoc checked f g h).symm

end Opposite
end VastitasOracle.FiniteCategoryExecution

namespace VastitasOracle.FiniteOpposite
open VastitasKernel VastitasKernel.Indexed
open Indexed.FiniteCategories

/-- Reversing twice restores the same graph and the same stored tables. -/
theorem involution (g : Graph) : g.opposite.opposite = g := by
  obtain ⟨e, i, c⟩ := g
  cases c <;> rfl

theorem reversed_row (g : Graph) (after before : String) :
    g.opposite.composition[[after, before]]? = g.composition[[before, after]]? := by
  obtain ⟨e, i, c⟩ := g
  cases c <;> rfl

theorem reversed_composable (g : Graph) (after before : String) :
    g.opposite.composable before after = g.composable after before := by
  change ((g.dst[[before]]?).isSome && g.dst[[before]]? == g.src[[after]]?) = _
  cases hs : g.src[[after]]? <;> cases ht : g.dst[[before]]? <;>
    simp [Endpoints.composable, hs, ht, Bool.beq_comm]

/-- On the same Hom tags whose categorical laws are transported above,
a lookup in the executable opposite graph returns the mathematical composite. -/
theorem hom_composition {p : Source.Program} (checked : Source.CheckedDeclarations p)
    {m : FiniteHom.Model checked.resolved.declarations.indexed owner}
    (g : FiniteCategoryExecution.Opposite.Hom m y z) (f : FiniteCategoryExecution.Opposite.Hom m x y) :
    m.data.opposite.composition[[g.tag, f.tag]]? =
      some (FiniteCategoryExecution.Opposite.compose checked g f).tag :=
  (reversed_row _ _ _).trans (FiniteCategoryExecution.Opposite.compose_row checked g f)

/-- One application of a named Opposite to a base declaration reuses exactly
that graph and its two swapped endpoint table IDs. -/
theorem selected_view {read : Read} (named : read viewId = some (.finiteOpposite schema base))
    (declared : read base = some (.finiteCategory schema fields))
    (selected : graph read schema fields = some g) :
    categoryView read viewId = some (orientedFields fields true, g.opposite) := by
  have steps (n : Nat) : describe read (n + 2) viewId = some (schema, fields, true) := by
    simp [describe, named, declared, guard]
  have budget : Limits.namespaceResolution + 1 = (Limits.namespaceResolution - 1) + 2 := by decide
  simp [categoryView, budget, steps, selected]

/-- In an ordinary covariant functor on the opposite graph, reversing the two
source factors determines the order of the mapped composition in the target.
Both diagram paths return an actual tag. -/
theorem map_reverses {base : Graph} {functor : Indexed.FiniteFunctors.Model} (law : FiniteFunctors.Preserves functor) (source : functor.source = base.opposite)
    (gmem : g ∈ base.arrows) (fmem : f ∈ base.arrows) (pair : base.composable g f = true) :
    FiniteFunctors.Commutes ((base.composition[[g, f]]?).bind (Indexed.FiniteFunctors.image functor.arrows))
      (functor.mappedComposition f g) := by
  have law' := law.composition f (source ▸ fmem) g (source ▸ gmem)
    (by rw [source, reversed_composable]; exact pair)
  rwa [source, reversed_row] at law'

/-- The source graph is recovered from the same checked model used for the
functor's identity, endpoint and composition equations. -/
theorem model_source {read : Read} {maps : FunctorFields DeclId} (selected : Indexed.FiniteFunctors.model read schema maps = some m)
    (domain : categoryView read maps.source = some (fields, g)) : m.source = g := by
  unfold Indexed.FiniteFunctors.model at selected
  cases shape : read schema <;> simp [shape] at selected
  split at selected <;> try contradiction
  simp [domain, Option.bind_eq_some_iff] at selected
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := selected
  rfl

/-- The actual finite lookup plan on a named opposite uses the reversed row of
the selected base graph. Its nominal site retains the view, even when two
different declarations share the same graph. -/
theorem plan_reverses {env : Environment} (named : lookup env owner = some (.finiteOpposite schema base))
    (direct : view env base = some (.finiteCategory schema fields))
    (selected : graph (view env) schema fields = some g)
    (plan : FiniteLookup.Plan env ⟨table, some owner, [after,before], output⟩)
    (evaluated : plan.atKey [h,f] = some tag) : g.composition[[f,h]]? = some tag := by
  have found : view env owner = some (.finiteOpposite schema base) := by simp [view, named]
  have oriented := selected_view found direct selected
  have core : FiniteSort.selected env owner = some (orientedFields fields true, g.opposite) := by
    simpa [FiniteSort.selected, named] using oriented
  simpa only [reversed_row] using FiniteCategoryExecution.plan_atKey_selected core plan evaluated

end VastitasOracle.FiniteOpposite
