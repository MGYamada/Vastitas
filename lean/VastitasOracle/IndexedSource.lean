import VastitasKernel.IndexedSourceChecker
import VastitasOracle.Namespaces

/-! Exact-input declaration acceptance through the real namespace resolver.
These statements do not yet certify source function elaboration, scalar/edit
composition, a public wire decoder, runtime evaluation or native refinement. -/
namespace VastitasOracle.IndexedSource
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source

/-- All checked evidence is indexed by the same unresolved input. A different
frontend-selected environment cannot be substituted into the certificate. -/
theorem checked_declarations (program : Source.Program) (checked : CheckedDeclarations program) :
    Namespace.validate program.indexed = .ok () ∧
    Namespace.UniqueOwners program.indexed ∧
    lower program = .ok checked.resolved ∧
    ReferencesValid program.indexed checked.resolved ∧
    checked.resolved.declarations.ids = program.declarationIds ∧
    checked.resolved.declarations.Valid :=
  ⟨checked.namespaceAccepted, checked.ownersUnique, checked.lowered,
    checked.referencesValid, checked.idsPreserved,
    Core.Typing.validDeclarations_iff _ |>.mp checked.accepted⟩

theorem reference_resolves (program : Source.Program) (checked : CheckedDeclarations program)
    (reference : Source.Reference) (member : reference ∈ checked.resolved.references) :
    reference.scope ∈ program.toNamespace.scopes ∧ reference.target.kind = .indexedDeclaration ∧
    Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span =
      .ok reference.target := by
  obtain ⟨scope, kind, found⟩ := checked.referencesValid reference member
  refine ⟨scope, kind, ?_⟩
  cases equation : Namespace.resolve program.indexed reference.scope reference.path.path reference.path.span with
  | error _ => simp [equation, Except.toOption] at found
  | ok target =>
    simp [equation, Except.toOption] at found
    subst target
    rfl

theorem owned_origin (program : Source.Program) (owner : DeclId) (declaration : Source.Declaration)
    (member : (owner, declaration) ∈ program.owned) :
    ∃ pkg ∈ program.packages, ∃ m ∈ pkg.modules,
      declaration ∈ m.declarations ∧ owner = ⟨⟨pkg.id, m.module.path⟩, declaration.name⟩ := by
  simp only [Source.Program.owned, List.mem_flatMap, List.mem_map] at member
  obtain ⟨pkg, pkgMember, m, moduleMember, d, declarationMember, equation⟩ := member
  cases equation
  exact ⟨pkg, pkgMember, m, moduleMember, declarationMember, rfl⟩

theorem declared_id_origin (program : Source.Program) (owner : DeclId)
    (member : owner ∈ program.declarationIds) :
    ∃ declaration, (owner, declaration) ∈ program.owned := by
  simp only [Source.Program.declarationIds, List.mem_flatMap, List.mem_map, List.mem_filter] at member
  obtain ⟨_, _, entry, ⟨entryMember, _⟩, same⟩ := member
  subst owner
  exact ⟨entry.2, entryMember⟩

/-- Canonical IDs in every output table originate in the actual enclosing
package/module, including private and unused declarations. Imports grant no
ability to substitute an alias owner. -/
theorem checked_id_origin (program : Source.Program) (checked : CheckedDeclarations program)
    (owner : DeclId) (member : owner ∈ checked.resolved.declarations.ids) :
    ∃ pkg ∈ program.packages, ∃ m ∈ pkg.modules, ∃ declaration ∈ m.declarations,
      owner = ⟨⟨pkg.id, m.module.path⟩, declaration.name⟩ := by
  rw [checked.idsPreserved] at member
  obtain ⟨declaration, found⟩ := declared_id_origin program owner member
  obtain ⟨pkg, hp, m, hm, hd, same⟩ := owned_origin program owner declaration found
  exact ⟨pkg, hp, m, hm, declaration, hd, same⟩

theorem checked_primitive_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (primitive : Core.NamedPrimitive) (member : primitive ∈ checked.resolved.declarations.primitives) :
    primitive.binding.Valid checked.resolved.declarations.indexed :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).primitives primitive member

theorem checked_package_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (package : Core.NamedPackage) (member : package ∈ checked.resolved.declarations.packages) :
    package.Valid checked.resolved.declarations.indexed :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).packages package member

/-- Numerical representation contracts are checked in the same complete
environment as every original declaration, not in a second profile registry. -/
theorem checked_implementation_contract (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker : DeclId) (representation : Indexed.Representation) (capabilities : List Capability)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈ checked.resolved.declarations.indexed) :
    isMarker checked.resolved.declarations.indexed marker = true ∧ capabilities.Nodup ∧
      representation.Valid checked.resolved.declarations.indexed marker capabilities :=
  (Core.Typing.validDeclarations_iff _ |>.mp checked.accepted).indexed.declarations _ member

theorem checked_linear_base (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker base : DeclId) (coefficient : CoefficientKind) (capabilities : List Capability)
    (member : ⟨id, .implementation marker (.linearDescriptor base coefficient) capabilities⟩ ∈
      checked.resolved.declarations.indexed) :
    capabilities = [] ∧ ∃ baseMarker setting baseCoefficient,
      scalarBaseProfile checked.resolved.declarations.indexed base = some (baseMarker, setting, baseCoefficient) ∧
      (match setting with
      | .scheme => coefficient = baseCoefficient ∧ marker = baseMarker
      | .smooth => baseCoefficient = .real ∧
          (match coefficient with | .real => marker = baseMarker | .complex => marker ≠ baseMarker)) := by
  have valid := (checked_implementation_contract program checked id marker _ capabilities member).2.2
  refine ⟨valid.1, ?_⟩
  have compatible := valid.2.2
  cases found : scalarBaseProfile checked.resolved.declarations.indexed base with
  | none => simp only [found] at compatible
  | some profile =>
    rcases profile with ⟨baseMarker, setting, baseCoefficient⟩
    refine ⟨baseMarker, setting, baseCoefficient, rfl, ?_⟩
    simp only [found] at compatible
    cases setting <;> cases coefficient <;> exact compatible

theorem checked_smooth_complex_base (program : Source.Program) (checked : CheckedDeclarations program)
    (id marker base baseMarker : DeclId) (baseCoefficient : CoefficientKind) (capabilities : List Capability)
    (member : ⟨id, .implementation marker (.linearDescriptor base .complex) capabilities⟩ ∈
      checked.resolved.declarations.indexed)
    (baseProfile : scalarBaseProfile checked.resolved.declarations.indexed base =
      some (baseMarker, .smooth, baseCoefficient)) :
    baseCoefficient = .real ∧ marker ≠ baseMarker := by
  have valid := (checked_implementation_contract program checked id marker _ capabilities member).2.2.2.2
  simpa only [baseProfile] using valid

theorem checked_coefficient_unique (program : Source.Program) (checked : CheckedDeclarations program)
    (id otherId marker : DeclId) (representation other : Indexed.Representation)
    (capabilities otherCapabilities : List Capability) (kind otherKind : CoefficientKind)
    (member : ⟨id, .implementation marker representation capabilities⟩ ∈ checked.resolved.declarations.indexed)
    (otherMember : ⟨otherId, .implementation marker other otherCapabilities⟩ ∈ checked.resolved.declarations.indexed)
    (coefficient : representation.coefficient = some kind)
    (otherCoefficient : other.coefficient = some otherKind) : kind = otherKind := by
  have valid := (checked_implementation_contract program checked id marker representation capabilities member).2.2
  have consistent : coefficientConsistent checked.resolved.declarations.indexed marker kind = true := by
    cases representation <;> simp only [Indexed.Representation.coefficient, Option.some.injEq] at coefficient <;>
      try contradiction
    all_goals subst kind; first | exact valid.2.1 | exact valid.2
  have compatible := List.all_eq_true.mp consistent _ otherMember
  change (marker != marker || other.coefficient.all (· == kind)) = true at compatible
  have same : otherKind = kind := by simpa [otherCoefficient] using compatible
  exact same.symm

/-- No scalar base or linear profile can acquire the old affine constructor
merely by declaring a primitive with a familiar spelling. -/
theorem checked_descriptor_is_affine (program : Source.Program) (checked : CheckedDeclarations program)
    (id implementation : DeclId)
    (member : ⟨id, .descriptor implementation⟩ ∈ checked.resolved.declarations.primitives) :
    affineImplementation checked.resolved.declarations.indexed implementation = true :=
  (checked_primitive_contract program checked _ member).1

end VastitasOracle.IndexedSource

namespace VastitasOracle.FiniteTables
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source Indexed.FiniteTables

private theorem row_determined {rows : List (List String × String)}
    (unique : (rows.map Prod.fst).Nodup) (a : (key, left) ∈ rows) (b : (key, right) ∈ rows) :
    left = right := by
  induction rows with
  | nil => simp at a
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp a with ah | am <;> rcases List.mem_cons.mp b with bh | bm
    · exact congrArg Prod.snd (ah.trans bh.symm)
    · have same : key = head.1 := congrArg Prod.fst ah
      exact (unique.1 (List.mem_map.mpr ⟨(key, right), bm, same⟩)).elim
    · have same : key = head.1 := congrArg Prod.fst bh
      exact (unique.1 (List.mem_map.mpr ⟨(key, left), am, same⟩)).elim
    · exact ih unique.2 am bm

/-- Each key of the finite Cartesian product has exactly one row, and
its value belongs to the resolved output carrier. -/
theorem rows_total {domain : List (List String)} {output : List String}
    {rows : List (List String × String)} (accepted : validRows domain output rows = true)
    (key : List String) (admitted : key ∈ domain) :
    ∃ value, (key, value) ∈ rows ∧ value ∈ output ∧
      ∀ other, (key, other) ∈ rows → other = value := by
  simp only [validRows, Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨_, unique⟩, counts⟩, values⟩ := accepted
  have present := Finite.sameCounts_member counts key admitted
  obtain ⟨⟨k, v⟩, member, same⟩ := List.mem_map.mp present
  change k = key at same
  subst k
  exact ⟨v, member, by simpa using List.all_eq_true.mp values _ member,
    fun _ other => row_determined ((Finite.distinct_iff _).mp unique) other member⟩

/-- This is the checker used on the actual declarations returned by
source elaboration, including independent validation of the entire Core
environment and the nominal signature of the table. -/
theorem checked_table (program : Source.Program) (checked : CheckedDeclarations program)
    (member : ⟨owner, .finiteTable inputs output rows⟩ ∈ checked.resolved.declarations.indexed) :
    validTable checked.resolved.declarations.indexed inputs output rows = true :=
  ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member

/-- Lookup on a well-formed key returns a tag of the nominal output carrier.
The input carrier IDs must match position by position; the membership premise
is in the Cartesian product computed from those carriers. -/
theorem lookup_total {env : Environment} {table : DeclId} {inputs : List DeclId} {output : DeclId}
    {rows : List (List String × String)} {domains : List (List String)} {range : List String}
    {product : List (List String)} {args : List (DeclId × String)}
    (found : lookup env table = some (.finiteTable inputs output rows))
    (accepted : validTable env inputs output rows = true)
    (fromInputs : inputs.mapM (carrier env) = some domains) (toOutput : carrier env output = some range)
    (bounded : keys domains = some product) (typed : inputs = args.map Prod.fst)
    (admitted : args.map Prod.snd ∈ product) :
    ∃ tag ∈ range, lookupTag env table args = some (output, tag) := by
  by_cases large : (inputs.length > maxInputs || rows.length > limit) = true
  · simp [validTable, large] at accepted
  simp only [validTable, large, fromInputs, toOutput, bounded, Id.run, pure] at accepted
  obtain ⟨v, member, inRange, unique⟩ := rows_total accepted _ admitted
  have present : (rows.find? (fun row => row.1 == args.map Prod.snd)).isSome :=
    List.find?_isSome.mpr ⟨(_, v), member, by simp⟩
  generalize h : rows.find? (fun row => row.1 == args.map Prod.snd) = result at present
  cases result with
  | none => contradiction
  | some row =>
    obtain ⟨key, value⟩ := row
    have yes := List.find?_some (p := fun row : List String × String => row.1 == args.map Prod.snd) h
    have k : key = args.map Prod.snd := beq_iff_eq.mp yes
    subst key
    have same := unique value (List.mem_of_find?_eq_some h)
    subst value
    exact ⟨v, inRange, by simp [lookupTag, found, typed, h, guard]⟩

end VastitasOracle.FiniteTables

namespace VastitasOracle.FiniteCategories
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source Indexed.FiniteCategories

theorem composable_pair {e : Endpoints} (checked : e.pairs = some pairs) :
    [g, f] ∈ pairs ↔ g ∈ e.arrows ∧ f ∈ e.arrows ∧ e.composable g f = true := by
  by_cases bound : (e.arrows.length ≤ Indexed.FiniteTables.limit && e.arrows.length ^ 2 ≤ Limits.elaborationWork) = true
  · by_cases count : (e.arrows.map fun f => e.arrows.countP (e.composable · f)).sum ≤ Indexed.FiniteTables.limit
    · simp [Endpoints.pairs, bound, count, guard] at checked
      subst pairs
      simp [List.mem_flatMap, List.mem_filter, and_assoc, and_left_comm, and_comm]
    · simp [Endpoints.pairs, bound, count, guard] at checked
      cases checked
  · simp [Endpoints.pairs, bound, guard] at checked
    cases checked

/-- In a checked named instance the law checks range over *all* composable
pairs and triples, in the declared after/before order. -/
theorem checked_category {p : Source.Program} (checked : CheckedDeclarations p)
    (member : ⟨owner, .finiteCategory schema fields⟩ ∈ checked.resolved.declarations.indexed) :
    ∃ g, graph (view checked.resolved.declarations.indexed) schema fields = some g ∧
      (∀ x ∈ g.objects, g.identityAt x = true) ∧
      (∀ f ∈ g.arrows, g.units f = true) ∧
      (∀ m ∈ g.arrows, ∀ f ∈ g.arrows, g.composable m f = true → g.ends m f = true ∧
        ∀ h ∈ g.arrows, g.composable h m = true → g.assoc h m f = true) := by
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member
  change valid _ _ _ = true at good
  unfold valid at good
  cases found : graph (view checked.resolved.declarations.indexed) schema fields with
  | none => simp [found] at good
  | some g =>
    simp only [found, Option.any_some] at good
    unfold laws at good
    cases pairs : g.toEndpoints.pairs with
    | none => simp [pairs] at good
    | some keys =>
      simp only [pairs, Id.run, pure] at good
      split at good <;> try contradiction
      simp only [Graph.validAt, Bool.and_eq_true, List.all_eq_true] at good
      refine ⟨g, rfl, good.1.1, good.1.2, ?_⟩
      intro m hm f hf mf
      have row := good.2 [m,f] ((composable_pair pairs).mpr ⟨hm, hf, mf⟩)
      simp only [Bool.and_eq_true, List.all_eq_true] at row
      refine ⟨row.1, ?_⟩
      intro h hh composable
      simp only [Endpoints.composable, Bool.and_eq_true, beq_iff_eq] at composable
      have same := composable.2
      simpa [same] using row.2 h hh

/-- The two unit equalities concern actual returned tags, not an optional
comparison in which two failed lookups could be equal. -/
theorem unit_equations {g : Graph} (law : g.units f = true)
    (src : g.src[[f]]? = some x) (dst : g.dst[[f]]? = some y)
    (left : g.identity[[y]]? = some iy) (right : g.identity[[x]]? = some ix) :
    g.composition[[iy, f]]? = some f ∧ g.composition[[f, ix]]? = some f := by
  simpa [Graph.units, src, dst, left, right] using law

theorem associative_equation {g : Graph} (law : g.assoc h m f = true)
    (first : g.composition[[m, f]]? = some a) (second : g.composition[[h, m]]? = some b) :
    ∃ tag, g.composition[[h, a]]? = some tag ∧ g.composition[[b, f]]? = some tag := by
  cases found : g.composition[[h, a]]? with
  | none => simp [Graph.assoc, first, second, found] at law
  | some tag => exact ⟨tag, rfl, by simpa [Graph.assoc, first, second, found] using law⟩

/-- Composition in the selected instance returns a real row in the specified
Hom fiber. Its direction is fixed by the two typed arguments. There is no
conversion of a raw arrow tag that bypasses endpoint checking. -/
theorem checked_composition_endpoints {p : Source.Program} (checked : CheckedDeclarations p)
    (member : ⟨owner, .finiteCategory schema fields⟩ ∈ checked.resolved.declarations.indexed)
    (selected : graph (view checked.resolved.declarations.indexed) schema fields = some g)
    (after : m ∈ g.arrows) (before : f ∈ g.arrows)
    (mx : g.src[[m]]? = some y) (mz : g.dst[[m]]? = some z)
    (fx : g.src[[f]]? = some x) (fy : g.dst[[f]]? = some y) :
    ∃ tag, g.composition[[m, f]]? = some tag ∧
      g.src[[tag]]? = some x ∧ g.dst[[tag]]? = some z := by
  obtain ⟨g', found, _, _, hs⟩ := checked_category checked member
  rw [selected] at found
  cases found
  have composable : g.composable m f = true := by simp [Endpoints.composable, mx, fy]
  have law := (hs m after f before composable).1
  cases row : g.composition[[m, f]]? with
  | none => simp [Graph.ends, row] at law
  | some tag => exact ⟨tag, rfl, by simpa [Graph.ends, row, fx, mz, beq_iff_eq] using law⟩

end VastitasOracle.FiniteCategories

namespace VastitasOracle.FiniteFunctors
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source
open Indexed.FiniteCategories Indexed.FiniteFunctors

/-- The two paths in a functor diagram compute the same actual tag. -/
def Commutes (left right : Option String) : Prop :=
  ∃ tag, left = some tag ∧ right = some tag

theorem agrees_iff (left right : Option String) : agrees left right = true ↔ Commutes left right := by
  cases left <;> cases right <;> simp [agrees, Commutes]
  exact eq_comm

/-- Covariance as three equations, interpreted over the actual finite maps. -/
structure Preserves (m : Model) : Prop where
  endpoints : ∀ f ∈ m.source.arrows,
    Commutes ((image m.source.src f).bind (image m.objects)) ((image m.arrows f).bind (image m.target.src)) ∧
    Commutes ((image m.source.dst f).bind (image m.objects)) ((image m.arrows f).bind (image m.target.dst))
  identity : ∀ x ∈ m.source.objects,
    Commutes ((image m.source.identity x).bind (image m.arrows))
      ((image m.objects x).bind (image m.target.identity))
  composition : ∀ g ∈ m.source.arrows, ∀ f ∈ m.source.arrows, m.source.composable g f = true →
    Commutes ((m.source.composition[[g, f]]?).bind (image m.arrows)) (m.mappedComposition g f)

/-- Every accepted named functor preserves both endpoints, identities and
composition. Composition ranges over all and only the composable source
pairs, in after/before order. Each equation asserts successful evaluation
of both paths in the selected nominal maps and category tables. -/
theorem checked_functor {p : Source.Program} (checked : CheckedDeclarations p)
    (member : ⟨owner, .finiteFunctor schema maps⟩ ∈ checked.resolved.declarations.indexed) :
    ∃ m, model (view checked.resolved.declarations.indexed) schema maps = some m ∧
      Preserves m := by
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member
  change Indexed.FiniteFunctors.valid _ _ _ = true at good
  unfold Indexed.FiniteFunctors.valid at good
  cases found : model (view checked.resolved.declarations.indexed) schema maps with
  | none => simp [found] at good
  | some m =>
    simp only [found, Option.any_some, Indexed.FiniteFunctors.laws, Bool.and_eq_true] at good
    obtain ⟨_, allPairs⟩ := good
    cases pairs : m.source.toEndpoints.pairs with
    | none => simp [pairs] at allPairs
    | some keys =>
      simp only [pairs, Option.any_some, Model.preserves, Bool.and_eq_true, List.all_eq_true] at allPairs
      refine ⟨m, rfl, ?_, ?_, ?_⟩
      · intro f hf
        simpa only [Model.endpointsAt, Model.endpointAt, Bool.and_eq_true, agrees_iff] using allPairs.1.2 f hf
      · intro x hx
        exact (agrees_iff _ _).mp (allPairs.1.1 x hx)
      · intro g hg f hf composable
        exact (agrees_iff _ _).mp (allPairs.2 [g,f]
          ((VastitasOracle.FiniteCategories.composable_pair pairs).mpr ⟨hg, hf, composable⟩))

end VastitasOracle.FiniteFunctors

namespace VastitasOracle.FiniteNatTrans
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source
open Indexed.FiniteNatTrans
open Indexed.FiniteFunctors (image)
open VastitasOracle.FiniteFunctors (Commutes agrees_iff)

/-- Every component has the prescribed source and target. For each arrow,
the codomain composition table returns the same actual tag for both paths
around the naturality square. -/
structure Natural (m : Model) : Prop where
  endpoints : ∀ x ∈ m.domain.objects,
    Commutes ((image m.components x).bind (image m.codomain.src)) (image m.sourceObjects x) ∧
    Commutes ((image m.components x).bind (image m.codomain.dst)) (image m.targetObjects x)
  naturality : ∀ f ∈ m.domain.arrows, Commutes (m.left f) (m.right f)

theorem checked_transformation {p : Source.Program} (checked : CheckedDeclarations p)
    (member : ⟨owner, .finiteNatTrans schema fields⟩ ∈ checked.resolved.declarations.indexed) :
    ∃ m, model (Indexed.FiniteCategories.view checked.resolved.declarations.indexed) schema fields = some m ∧
      Natural m := by
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member
  change valid _ _ _ = true at good
  unfold valid at good
  cases found : model (Indexed.FiniteCategories.view checked.resolved.declarations.indexed) schema fields with
  | none => simp [found] at good
  | some m =>
    simp only [found, Option.any_some, laws, Bool.and_eq_true, List.all_eq_true] at good
    refine ⟨m, rfl, ?_, ?_⟩
    · intro x hx
      simpa only [Model.endpointsAt, Bool.and_eq_true, agrees_iff] using good.1.2 x hx
    · intro f hf
      exact (agrees_iff _ _).mp (good.2 f hf)

end VastitasOracle.FiniteNatTrans

namespace VastitasOracle.FiniteMonads
open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Source
open Indexed.FiniteMonads
open Indexed.FiniteFunctors (image)
open VastitasOracle.FiniteFunctors (Commutes agrees_iff)

/-- Extensional identities of the sources of eta and mu, followed by the two
unit diagrams and the associativity diagram for the same selected data. -/
structure Diagrams (m : Model) : Prop where
  identityObjects : ∀ x ∈ m.category.objects, image m.identityObjects x = some x
  identityArrows : ∀ f ∈ m.category.arrows, image m.identityArrows f = some f
  squareObjects : ∀ x ∈ m.category.objects, Commutes (image m.squareObjects x) ((image m.objects x).bind (image m.objects))
  squareArrows : ∀ f ∈ m.category.arrows, Commutes (image m.squareArrows f) ((image m.arrows f).bind (image m.arrows))
  unit : ∀ x ∈ m.category.objects,
    let tx := image m.objects x
    let mu := image m.multiplication x
    let id := tx.bind (image m.category.identity)
    Commutes (compose m mu (tx.bind (image m.unit))) id ∧
      Commutes (compose m mu ((image m.unit x).bind (image m.arrows))) id
  associativity : ∀ x ∈ m.category.objects,
    let mu := image m.multiplication x
    Commutes (compose m mu ((image m.objects x).bind (image m.multiplication)))
      (compose m mu (mu.bind (image m.arrows)))

theorem checked_monad {p : Source.Program} (checked : CheckedDeclarations p)
    (member : ⟨owner, .finiteMonad schema fields⟩ ∈ checked.resolved.declarations.indexed) :
    ∃ m, model (Indexed.FiniteCategories.view checked.resolved.declarations.indexed) schema fields = some m ∧
      Diagrams m := by
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member
  change valid _ _ _ = true at good
  unfold valid at good
  cases found : model (Indexed.FiniteCategories.view checked.resolved.declarations.indexed) schema fields with
  | none => simp [found] at good
  | some m =>
    simp only [found, Option.any_some, laws, Bool.and_eq_true, List.all_eq_true] at good
    refine ⟨m, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact beq_iff_eq.mp (good.1.2 x hx).1.1.1
    · intro f hf
      exact beq_iff_eq.mp (good.2 f hf).1
    · intro x hx
      exact (agrees_iff _ _).mp (good.1.2 x hx).1.1.2
    · intro f hf
      exact (agrees_iff _ _).mp (good.2 f hf).2
    · intro x hx
      simpa only [Model.unitAt, Bool.and_eq_true, agrees_iff] using (good.1.2 x hx).1.2
    · intro x hx
      exact (agrees_iff _ _).mp (good.1.2 x hx).2

end VastitasOracle.FiniteMonads
