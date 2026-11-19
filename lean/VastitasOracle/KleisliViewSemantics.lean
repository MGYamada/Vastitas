import VastitasOracle.KleisliSelection
import VastitasOracle.FiniteKleisli

/-! A public category or triple view derives its operations and their laws
from the one named Monad recorded by the declaration checker. -/
namespace VastitasOracle.KleisliViewSemantics

open VastitasKernel VastitasKernel.Indexed
open FiniteKleisli (Context Obj T category data triple)

variable {p : Source.Program} {checked : Source.CheckedDeclarations p}
    {fields : MonadFields DeclId} {model : Indexed.FiniteMonads.Model}

/-- The finite Core Hom on these endpoints accepts the tag exactly when it
constructs an arrow from X to T(Y) in the selected underlying category. -/
theorem core_hom_iff (c : Context checked fields model) (x y : Obj model) (tag : String) :
    Core.Typing.HasType checked.resolved.declarations functions ctx
      (.finiteTag (.hom fields.category x.1 (T c y).1) tag) ↔
      (FiniteHom.fromTag? (category c) x.1 (T c y).1 tag).isSome = true :=
  FiniteCategoryExecution.core_literal_typed_iff x.2 (T c y).2

/-- Both kinds share this exact interpretation. In particular the extension,
unit, action and multiplication are the rows of the originally selected Monad. -/
structure Interpretation (c : Context checked fields model) : Prop where
  monadLaws : Kleisli.Laws (data c)
  equations : FiniteKleisli.Equations c
  tripleLaws : Kleisli.Triple.Laws (triple c)
  roundtrip : (triple c).toMonad = data c
  rows : FiniteKleisli.TripleRows c
  hom : ∀ (x y : Obj model) (tag : String),
    Core.Typing.HasType checked.resolved.declarations {} []
      (.finiteTag (.hom fields.category x.1 (T c y).1) tag) ↔
      (FiniteHom.fromTag? (category c) x.1 (T c y).1 tag).isSome = true

/-- A wire-accepted named view selects its actual Monad and cannot introduce
different laws or tables, even if it is never used by an executable body. -/
theorem public_view {json : Lean.Json} (input : ResourceSource.Wire.CheckedInput json requireMain)
    (member : ⟨owner, .finiteKleisli kind schema monad⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let checked := input.checked.pureProgram.authority.headers.declarations
    let env := checked.resolved.declarations.indexed
    ResourceSource.Wire.RevisionMatches json input.checked ∧
      KleisliViews.selected (FiniteCategories.view env) kind owner = some monad ∧
      ∃ base fields, ⟨schema, .kleisliSchema kind base⟩ ∈ env ∧ ⟨base, .monadSchema⟩ ∈ env ∧
        ⟨monad, .finiteMonad base fields⟩ ∈ env ∧
        ∃ m, Indexed.FiniteMonads.model (FiniteCategories.view env) base fields = some m ∧
          ∃ c : Context checked fields m, Interpretation c := by
  let checked := input.checked.pureProgram.authority.headers.declarations
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed
  obtain ⟨selected, base, fields, schemaMem, baseMem, monadMem⟩ := KleisliSelection.of_member good member
  obtain ⟨rev, m, found, c, laws, roundtrip, rows⟩ := FiniteKleisli.public_triple input monadMem
  exact ⟨rev, selected, base, fields, schemaMem, baseMem, monadMem, m, found, c,
    FiniteKleisli.lawful c, FiniteKleisli.equations c, laws, roundtrip, rows, core_hom_iff c⟩

open Indexed.Source

private theorem literal_endpoint {p : Namespace.Indexed} {scope : Namespace.Scope} {env : Environment}
    {g : FiniteCategories.Graph} {car tag : String} {span : Span}
    (h : (homEndpoint p scope ⟨[car,tag],span⟩ env g).run r = .ok (t,s)) : t = tag := by
  unfold homEndpoint at h
  conv at h => lhs; whnf
  by_cases n : car = "objects" <;> simp [n] at h <;> (
    conv at h => lhs; whnf
    split at h <;> try contradiction
    next pair hit =>
      rcases pair with ⟨id,rs⟩
      by_cases valid : id = g.objectId ∧ tag ∈ g.objects <;> simp [valid] at h <;> cases h
      rfl)

/-- Successful elaboration of the concrete source type Hom<K, A::x, B::y>
uses the resolved category C of K's selected Monad, the source tag x, and
the exact image T(y). The four names are ordinary source identifiers;
the internal marker for nested type arguments is excluded. -/
theorem concrete_hom {program : Namespace.Indexed} {env : Core.Declarations} {scope : Namespace.Scope}
    {cat : Path} {sourceCarrier targetCarrier xTag yTag : String} {xSpan ySpan : Span} {ctx : TypeContext} {m : Indexed.FiniteMonads.Model}
    (sourceCarrierLiteral : sourceCarrier ≠ "T<>") (targetCarrierLiteral : targetCarrier ≠ "T<>")
    (xLiteral : xTag ≠ "T<>") (yLiteral : yTag ≠ "T<>")
    (ordinary : projectedMonadCategory? program scope env.indexed cat = none)
    (owner : (resolveId program scope cat).run refs = .ok (viewOwner, namedRefs))
    (view : KleisliViews.selected (FiniteCategories.view env.indexed) .category viewOwner = some monad)
    (found : FiniteSort.monad? env.indexed monad = some (fields, m))
    (lowered : (elaborateDataType program env scope ctx
      (.finiteHom cat ⟨[sourceCarrier, xTag], xSpan⟩ ⟨[targetCarrier, yTag], ySpan⟩) geom).run refs =
      .ok (result, newRefs)) :
    ∃ ty, FiniteFunctors.image m.objects yTag = some ty ∧ result = .finite (.hom fields.category xTag ty) := by
  unfold elaborateDataType at lowered
  conv at lowered => lhs; whnf
  split at lowered <;> try contradiction
  next pair categoryFound =>
    conv at categoryFound => lhs; whnf
    rw [ordinary] at categoryFound
    change resolveId program scope cat refs = .ok (viewOwner, namedRefs) at owner
    conv at categoryFound => lhs; whnf
    rw [owner] at categoryFound
    simp only [view, found] at categoryFound
    cases categoryFound
    conv at lowered => lhs; whnf
    split at lowered <;> try contradiction
    next outcome xFound =>
      rcases outcome with ⟨x, state⟩
      conv at xFound => lhs; whnf
      have sourceCarrier' : (sourceCarrier != "T<>") = true := bne_iff_ne.mpr sourceCarrierLiteral
      have x' : (xTag != "T<>") = true := bne_iff_ne.mpr xLiteral
      simp [sourceCarrier', x', List.span.loop] at xFound
      have hx := literal_endpoint xFound
      subst x
      conv at lowered => lhs; whnf
      split at lowered <;> try contradiction
      next outcome yFound =>
        rcases outcome with ⟨y, state'⟩
        conv at yFound => lhs; whnf
        have targetCarrier' : (targetCarrier != "T<>") = true := bne_iff_ne.mpr targetCarrierLiteral
        have y' : (yTag != "T<>") = true := bne_iff_ne.mpr yLiteral
        simp [targetCarrier', y', List.span.loop] at yFound
        have hy := literal_endpoint yFound
        subst y
        conv at lowered => lhs; whnf
        cases image : FiniteFunctors.image m.objects yTag with
        | none =>
          rw [image] at lowered
          contradiction
        | some ty =>
          rw [image] at lowered
          cases lowered
          exact ⟨ty, rfl, rfl⟩

end VastitasOracle.KleisliViewSemantics
