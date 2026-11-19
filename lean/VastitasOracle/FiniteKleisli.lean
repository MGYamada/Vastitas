import VastitasOracle.KleisliTriple
import VastitasOracle.FiniteMapTotal
import VastitasOracle.FiniteMonadSelection
import VastitasOracle.ResourceSource

/-! Interpret the selected finite tables as total, endpoint-indexed arrows.
Every tag used here is recovered from a successful lookup on the checked
environment. Proof witnesses used to obtain those tags are erased. -/
namespace VastitasOracle.FiniteKleisli
open VastitasKernel VastitasKernel.Indexed
open Indexed.FiniteCategories (Graph view)
open Indexed.FiniteFunctors (image)
open Indexed.FiniteMonads (Model)
open VastitasOracle.FiniteCategoryExecution (lookup_member lookup_of_view)
open VastitasOracle.FiniteMapTotal (graph_tables mapping_total)

variable {p : Source.Program} {m : Model} {s : MonadFields DeclId}
abbrev Obj (m : Model) := { x : String // x ∈ m.category.objects }

structure Context (checked : Source.CheckedDeclarations p) (s : MonadFields DeclId) (m : Model) where
  selected : FiniteMonads.Selection (view checked.resolved.declarations.indexed) s m
  diagrams : FiniteMonads.Diagrams m

variable {checked : Source.CheckedDeclarations p} (c : Context checked s m)

def category : FiniteHom.Model checked.resolved.declarations.indexed s.category :=
  ⟨((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed,
    c.selected.categorySchema, c.selected.categoryFields, lookup_of_view c.selected.categoryFound,
    m.category, c.selected.categoryModel⟩

abbrev Hom (x y : Obj m) := FiniteHom.Hom (category c) x.1 y.1

private theorem commutes_eq {u v} (e : FiniteFunctors.Commutes u v) : u = v :=
  let ⟨_,l,r⟩ := e; l.trans r.symm

include c in
private theorem functor_laws : FiniteFunctors.Preserves
    ⟨m.category, m.category, m.objects, m.arrows⟩ := by
  obtain ⟨t, found, laws⟩ := FiniteFunctors.checked_functor checked
    (lookup_member (lookup_of_view c.selected.functorFound))
  rw [c.selected.functorModel] at found
  cases found
  exact laws

include c in
private theorem eta_laws : FiniteNatTrans.Natural
    ⟨m.category, m.category, m.identityObjects, m.objects, m.identityArrows, m.arrows, m.unit⟩ := by
  obtain ⟨t, found, laws⟩ := FiniteNatTrans.checked_transformation checked
    (lookup_member (lookup_of_view c.selected.unitFound))
  rw [c.selected.unitModel] at found
  cases found
  exact laws

include c in
private theorem mu_laws : FiniteNatTrans.Natural
    ⟨m.category, m.category, m.squareObjects, m.objects, m.squareArrows, m.arrows, m.multiplication⟩ := by
  obtain ⟨t, found, laws⟩ := FiniteNatTrans.checked_transformation checked
    (lookup_member (lookup_of_view c.selected.multiplicationFound))
  rw [c.selected.multiplicationModel] at found
  cases found
  exact laws

include c in
private theorem category_laws :
    (∀ x ∈ m.category.objects, m.category.identityAt x = true) ∧
    (∀ f ∈ m.category.arrows, m.category.units f = true) ∧
    (∀ g ∈ m.category.arrows, ∀ f ∈ m.category.arrows, m.category.composable g f = true →
      m.category.ends g f = true ∧ ∀ h ∈ m.category.arrows, m.category.composable h g = true →
        m.category.assoc h g f = true) := by
  obtain ⟨g, found, laws⟩ := FiniteCategories.checked_category checked
    (lookup_member (lookup_of_view c.selected.categoryFound))
  rw [c.selected.categoryModel] at found
  cases found
  exact laws

/-- A chosen tag together with the exact finite operation that returned it. -/
private structure Output (tags : List String) (answer : Option String) where
  value : String
  member : value ∈ tags
  row : answer = some value

private def output {tags : List String} {answer : Option String}
    (total : ∃ y ∈ tags, answer = some y) : Output tags answer :=
  let y := answer.get (by obtain ⟨y, _, h⟩ := total; simp [h])
  have row : answer = some y := (Option.some_get _).symm
  ⟨y, by obtain ⟨z, hz, h⟩ := total; rw [row] at h; exact Option.some.inj h ▸ hz, row⟩

private def objectAt (x : Obj m) : Output m.category.objects (image m.objects x.1) :=
  let ranges := graph_tables c.selected.categoryModel
  output (mapping_total (category c).accepted c.selected.objectsMap ranges.1 ranges.1 x.2)

def T (x : Obj m) : Obj m := ⟨(objectAt c x).value, (objectAt c x).member⟩

theorem T_row (x : Obj m) : image m.objects x.1 = some (T c x).1 := (objectAt c x).row

private def idAt (x : Obj m) : Output m.category.arrows (image m.category.identity x.1) :=
  let ranges := graph_tables c.selected.categoryModel
  output (mapping_total (category c).accepted ranges.2.2 ranges.1 ranges.2.1 x.2)

def identity (x : Obj m) : Hom c x x :=
  let o := idAt c x
  have row : m.category.identity[[x.1]]? = some o.value := o.row
  have ends := (category_laws c).1 x.1 x.2
  have endpoints : m.category.src[[o.value]]? = some x.1 ∧ m.category.dst[[o.value]]? = some x.1 := by
    simpa [Graph.identityAt, row] using ends
  ⟨o.value, o.member, endpoints.1, endpoints.2⟩

theorem identity_row (x : Obj m) : image m.category.identity x.1 = some (identity c x).tag := (idAt c x).row

def comp {x y z : Obj m} (g : Hom c y z) (f : Hom c x y) : Hom c x z :=
  FiniteCategoryExecution.compose checked g f

theorem comp_row {x y z : Obj m} (g : Hom c y z) (f : Hom c x y) :
    m.category.composition[[g.tag, f.tag]]? = some (comp c g f).tag :=
  FiniteCategoryExecution.compose_uses_selected_row checked g f

private def arrowAt {x y : Obj m} (f : Hom c x y) : Output m.category.arrows (image m.arrows f.tag) :=
  let ranges := graph_tables c.selected.categoryModel
  output (mapping_total (category c).accepted c.selected.arrowsMap ranges.2.1 ranges.2.1 f.member)

def map {x y : Obj m} (f : Hom c x y) : Hom c (T c x) (T c y) :=
  let a := arrowAt c f
  have h := (functor_laws c).endpoints f.tag f.member
  have src : image m.category.src f.tag = some x.1 := f.src
  have dst : image m.category.dst f.tag = some y.1 := f.dst
  have s := commutes_eq h.1
  have d := commutes_eq h.2
  ⟨a.value, a.member, by
    change image m.category.src a.value = some (T c x).1
    simpa only [src, a.row, T_row c x, Option.bind_some] using s.symm,
    by
    change image m.category.dst a.value = some (T c y).1
    simpa only [dst, a.row, T_row c y, Option.bind_some] using d.symm⟩

theorem map_row {x y : Obj m} (f : Hom c x y) :
    image m.arrows f.tag = some (map c f).tag := (arrowAt c f).row

private def unitAt (x : Obj m) : Output m.category.arrows (image m.unit x.1) :=
  let ranges := graph_tables c.selected.categoryModel
  output (mapping_total (category c).accepted c.selected.unitMap ranges.1 ranges.2.1 x.2)

def eta (x : Obj m) : Hom c x (T c x) :=
  let a := unitAt c x
  have h := (eta_laws c).endpoints x.1 x.2
  have s := commutes_eq h.1
  have d := commutes_eq h.2
  ⟨a.value, a.member, by
    change image m.category.src a.value = some x.1
    simpa only [a.row, c.diagrams.identityObjects x.1 x.2, Option.bind_some] using s,
    by
    change image m.category.dst a.value = some (T c x).1
    simpa only [a.row, T_row c x, Option.bind_some] using d⟩

theorem eta_row (x : Obj m) : image m.unit x.1 = some (eta c x).tag := (unitAt c x).row

private def multiplicationAt (x : Obj m) : Output m.category.arrows (image m.multiplication x.1) :=
  let ranges := graph_tables c.selected.categoryModel
  output (mapping_total (category c).accepted c.selected.multiplicationMap ranges.1 ranges.2.1 x.2)

def mu (x : Obj m) : Hom c (T c (T c x)) (T c x) :=
  let a := multiplicationAt c x
  have h := (mu_laws c).endpoints x.1 x.2
  have s := commutes_eq h.1
  have d := commutes_eq h.2
  have square := commutes_eq (c.diagrams.squareObjects x.1 x.2)
  ⟨a.value, a.member, by
    change image m.category.src a.value = some (T c (T c x)).1
    simpa only [a.row, square, T_row c x, T_row c (T c x), Option.bind_some] using s,
    by
    change image m.category.dst a.value = some (T c x).1
    simpa only [a.row, T_row c x, Option.bind_some] using d⟩

theorem mu_row (x : Obj m) : image m.multiplication x.1 = some (mu c x).tag := (multiplicationAt c x).row

def data : Kleisli.Data (Obj m) (Hom c) := ⟨identity c, comp c, T c, map c, eta c, mu c⟩

private theorem tag_ext {x y : Obj m} {f g : Hom c x y} (same : f.tag = g.tag) : f = g := by
  cases f; cases g; cases same; rfl

private theorem composable {x y z : Obj m} (g : Hom c y z) (f : Hom c x y) :
    m.category.composable g.tag f.tag = true := by
  have src : m.category.src[[g.tag]]? = some y.1 := g.src
  have dst : m.category.dst[[f.tag]]? = some y.1 := f.dst
  simp [Indexed.FiniteCategories.Endpoints.composable, src, dst]

/-- The category, functor and transformation laws of this interpretation
come from the actual declared graphs. Both unit laws and multiplication
associativity come from the independently checked Monad, with no second
enumeration of Kleisli arrows or triples. -/
theorem lawful : Kleisli.Laws (data c) := by
  constructor <;> dsimp only [data]
  · intro x y f
    apply tag_ext c
    have eq := FiniteCategories.unit_equations ((category_laws c).2.1 f.tag f.member)
      f.src f.dst (identity_row c y) (identity_row c x)
    exact Option.some.inj ((comp_row c (identity c y) f).symm.trans eq.1)
  · intro x y f
    apply tag_ext c
    have eq := FiniteCategories.unit_equations ((category_laws c).2.1 f.tag f.member)
      f.src f.dst (identity_row c y) (identity_row c x)
    exact Option.some.inj ((comp_row c f (identity c x)).symm.trans eq.2)
  · intro w x y z h g f
    apply tag_ext c
    have assoc := ((category_laws c).2.2 g.tag g.member f.tag f.member
      (composable c g f)).2 h.tag h.member (composable c h g)
    obtain ⟨_, left, right⟩ := FiniteCategories.associative_equation assoc (comp_row c g f) (comp_row c h g)
    exact Option.some.inj ((comp_row c (comp c h g) f).symm.trans
      (right.trans (left.symm.trans (comp_row c h (comp c g f)))))
  · intro x
    apply tag_ext c
    have eq := commutes_eq ((functor_laws c).identity x.1 x.2)
    simpa only [identity_row c x, T_row c x, Option.bind_some, map_row c (identity c x),
      identity_row c (T c x), Option.some.injEq] using eq
  · intro x y z g f
    apply tag_ext c
    have eq := commutes_eq ((functor_laws c).composition g.tag g.member f.tag f.member (composable c g f))
    simpa only [Indexed.FiniteFunctors.Model.mappedComposition, comp_row c g f, map_row c g,
      map_row c f, Option.bind_eq_bind, Option.bind_some, map_row c (comp c g f), comp_row c (map c g) (map c f),
      Option.some.injEq] using eq
  · intro x y f
    apply tag_ext c
    have src : image m.category.src f.tag = some x.1 := f.src
    have dst : image m.category.dst f.tag = some y.1 := f.dst
    have eq := commutes_eq ((eta_laws c).naturality f.tag f.member)
    simpa only [Indexed.FiniteNatTrans.Model.left, Indexed.FiniteNatTrans.Model.right,
      src, dst, Option.bind_eq_bind, Option.bind_some, eta_row c x, eta_row c y, c.diagrams.identityArrows f.tag f.member,
      map_row c f, comp_row c (eta c y) f, comp_row c (map c f) (eta c x), Option.some.injEq] using eq.symm
  · intro x y f
    apply tag_ext c
    have src : image m.category.src f.tag = some x.1 := f.src
    have dst : image m.category.dst f.tag = some y.1 := f.dst
    have eq := commutes_eq ((mu_laws c).naturality f.tag f.member)
    have square := commutes_eq (c.diagrams.squareArrows f.tag f.member)
    simpa only [Indexed.FiniteNatTrans.Model.left, Indexed.FiniteNatTrans.Model.right, src, dst,
      square, Option.bind_eq_bind, Option.bind_some, mu_row c x, mu_row c y, map_row c f, map_row c (map c f),
      comp_row c (mu c y) (map c (map c f)), comp_row c (map c f) (mu c x), Option.some.injEq] using eq.symm
  · intro x
    apply tag_ext c
    have eq := commutes_eq (c.diagrams.unit x.1 x.2).1
    simpa only [Indexed.FiniteMonads.compose, mu_row c x, T_row c x, Option.bind_eq_bind, Option.bind_some,
      eta_row c (T c x), comp_row c (mu c x) (eta c (T c x)), identity_row c (T c x),
      Option.some.injEq] using eq
  · intro x
    apply tag_ext c
    have eq := commutes_eq (c.diagrams.unit x.1 x.2).2
    simpa only [Indexed.FiniteMonads.compose, mu_row c x, T_row c x, Option.bind_eq_bind, Option.bind_some, eta_row c x,
      map_row c (eta c x), comp_row c (mu c x) (map c (eta c x)), identity_row c (T c x),
      Option.some.injEq] using eq
  · intro x
    apply tag_ext c
    have eq := commutes_eq (c.diagrams.associativity x.1 x.2)
    simpa only [Indexed.FiniteMonads.compose, mu_row c x, T_row c x, Option.bind_eq_bind, Option.bind_some, mu_row c (T c x),
      map_row c (mu c x), comp_row c (mu c x) (mu c (T c x)), comp_row c (mu c x) (map c (mu c x)),
      Option.some.injEq] using eq

/-- The finite bind reads the selected arrow map and multiplication component
and performs the two declared compositions in that order. -/
theorem bind_row {w x y : Obj m} (p : Hom c w (T c x)) (f : Hom c x (T c y)) :
    (do
      let mu ← image m.multiplication y.1
      let mapped ← image m.arrows f.tag
      let ext ← m.category.composition[[mu, mapped]]?
      m.category.composition[[ext, p.tag]]?) =
      some (Kleisli.bind (data c) p f).tag := by
  simp only [mu_row c y, map_row c f, Option.bind_eq_bind, Option.bind_some,
    comp_row c (mu c y) (map c f), comp_row c (comp c (mu c y) (map c f)) p,
    Kleisli.bind, Kleisli.extend, data]

structure Equations (c : Context checked s m) : Prop where
  rightUnit : ∀ {w x : Obj m} (p : Hom c w (T c x)), Kleisli.bind (data c) p (Kleisli.unit (data c) x) = p
  leftUnit : ∀ {x y : Obj m} (f : Hom c x (T c y)), Kleisli.bind (data c) (Kleisli.unit (data c) x) f = f
  assoc : ∀ {w x y z : Obj m} (p : Hom c w (T c x)) (f : Hom c x (T c y)) (g : Hom c y (T c z)),
    Kleisli.bind (data c) (Kleisli.bind (data c) p f) g = Kleisli.bind (data c) p (Kleisli.bind (data c) f g)

theorem equations : Equations c :=
  ⟨Kleisli.bind_unit (data c) (lawful c), Kleisli.unit_bind (data c) (lawful c),
    Kleisli.bind_assoc (data c) (lawful c)⟩


/-- The accepted declarations yield a total typed Kleisli operation on this
particular category, using exactly the named T, eta and mu. No extra
well-formedness or independent law test is a premise. -/
theorem checked_kleisli (checked : Source.CheckedDeclarations p)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈ checked.resolved.declarations.indexed) :
    ∃ m, Indexed.FiniteMonads.model (view checked.resolved.declarations.indexed) schema fields = some m ∧
      ∃ c : Context checked fields m, Kleisli.Laws (data c) ∧ Equations c := by
  obtain ⟨m, found, diagrams⟩ := FiniteMonads.checked_monad checked member
  obtain ⟨selection⟩ := FiniteMonads.selection_of_model found
  let c : Context checked fields m := ⟨selection, diagrams⟩
  exact ⟨m, found, c, lawful c, equations c⟩

/-- On the exact public request, even an unused Monad supplies the same
row-backed interpretation and both Kleisli unit laws and associativity. -/
theorem public_kleisli {json : Lean.Json} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let checked := input.checked.pureProgram.authority.headers.declarations
    ResourceSource.Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteMonads.model (view checked.resolved.declarations.indexed) schema fields = some m ∧
        ∃ c : Context checked fields m, Kleisli.Laws (data c) ∧ Equations c :=
  ⟨input.revisionMatches, checked_kleisli _ member⟩

/-- The triple of this named, checked finite Monad uses the same object
action, unit components, and endpoint-indexed extension. -/
def triple : Kleisli.Triple (Obj m) (Hom c) := Kleisli.Triple.fromMonad (data c)

theorem triple_lawful : Kleisli.Triple.Laws (triple c) :=
  Kleisli.Triple.fromMonad_lawful (data c) (lawful c)

theorem triple_roundtrip : (triple c).toMonad = data c :=
  Kleisli.Triple.monad_roundtrip (data c) (lawful c)

/-- The extension of f uses its selected arrow image followed by the selected
multiplication component at the target object. -/
theorem extension_row {x y : Obj m} (f : Hom c x (T c y)) :
    (do let mapped ← image m.arrows f.tag
        let mult ← image m.multiplication y.1
        m.category.composition[[mult,mapped]]?) = some ((triple c).extend f).tag := by
  simp only [map_row c f, mu_row c y, Option.bind_eq_bind, Option.bind_some,
    comp_row c (mu c y) (map c f), triple, Kleisli.Triple.fromMonad, Kleisli.extend, data]

/-- Recovery reads the very object, unit, multiplication, and arrow-map rows
selected by this finite declaration, including different structures on one T. -/
structure TripleRows (c : Context checked s m) : Prop where
  object : ∀ x : Obj m, image m.objects x.1 = some ((triple c).T x).1
  unit : ∀ x : Obj m, image m.unit x.1 = some ((triple c).eta x).tag
  multiplication : ∀ x : Obj m, image m.multiplication x.1 = some ((triple c).multiplication x).tag
  action : ∀ {x y : Obj m} (f : Hom c x y), image m.arrows f.tag = some ((triple c).action f).tag
  extension : ∀ {x y : Obj m} (f : Hom c x (T c y)),
    (do let mapped ← image m.arrows f.tag
        let mult ← image m.multiplication y.1
        m.category.composition[[mult,mapped]]?) = some ((triple c).extend f).tag

theorem triple_rows : TripleRows c := by
  refine ⟨T_row c, eta_row c, ?_, ?_, extension_row c⟩
  · intro x
    change image m.multiplication x.1 = some ((Kleisli.Triple.fromMonad (data c)).multiplication x).tag
    rw [Kleisli.Triple.recover_multiplication (data c) (lawful c)]
    exact mu_row c x
  · intro x y f
    change image m.arrows f.tag = some ((Kleisli.Triple.fromMonad (data c)).action f).tag
    rw [Kleisli.Triple.recover_action (data c) (lawful c)]
    exact map_row c f

theorem public_triple {json : Lean.Json} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let checked := input.checked.pureProgram.authority.headers.declarations
    ResourceSource.Wire.RevisionMatches json input.checked ∧
      ∃ m, Indexed.FiniteMonads.model (view checked.resolved.declarations.indexed) schema fields = some m ∧
        ∃ c : Context checked fields m, Kleisli.Triple.Laws (triple c) ∧
          (triple c).toMonad = data c ∧ TripleRows c := by
  obtain ⟨revision,m,found,c,_,_⟩ := public_kleisli input member
  exact ⟨revision,m,found,c,triple_lawful c,triple_roundtrip c,triple_rows c⟩

end VastitasOracle.FiniteKleisli
