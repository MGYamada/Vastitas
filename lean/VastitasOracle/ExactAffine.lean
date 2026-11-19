import VastitasKernel.ResourceProtocol
import VastitasOracle.ExactComplexField
import VastitasOracle.IndexedSource

set_option autoImplicit false

/-! Exact standard-chart points for a named affine declaration. The selected
meadow supplies a commutative-ring reduct. The mathematical carrier and the
executable coordinates on that carrier have distinct types. -/
namespace VastitasOracle.ExactAffine
open VastitasKernel VastitasKernel.Indexed VastitasKernel.ResourceSource
open VastitasOracle.ExactComplex

def Carrier : ExactModelProfile → Type
  | .cauchy _ => RR
  | .pairs .. => CC

noncomputable def meadow : (profile : ExactModelProfile) → Meadow (Carrier profile)
  | .cauchy _ => realModel
  | .pairs .. => complexModel

/-- A field witness for the same model is available independently of affine selection. -/
theorem isField (profile : ExactModelProfile) : (meadow profile).IsField := by
  cases profile with
  | cauchy => exact real_isField
  | pairs => exact complex_isField

def Coordinate : ExactModelProfile → Type
  | .cauchy _ => Rat
  | .pairs .. => QQi

def embed : (profile : ExactModelProfile) → Coordinate profile → Carrier profile
  | .cauchy _ => ofRat
  | .pairs .. => QQi.embed

/-- Equality of all represented points in the mathematical standard chart
reflects equality of the source coordinates, including the zero-dimensional chart. -/
theorem chart_injective {profile : ExactModelProfile} {n : Nat} {a b : Fin n → Coordinate profile}
    (same : (fun i => embed profile (a i)) = (fun i => embed profile (b i))) : a = b := by
  funext i
  have h := congrFun same i
  cases profile with
  | cauchy => exact ofRat_injective h
  | pairs => exact QQi.embed_injective h

/-- Selection records the whole chain of nominal carrier and model declarations. -/
theorem paired_selection {named : DeclId → Option (ExactConstruction DeclId)}
    {model carrier realModel realCarrier : DeclId}
    (selected : (named model).bind (·.model? named) = some (.pairs carrier realModel realCarrier)) :
    named model = some (.complexMeadow carrier realModel) ∧
    named carrier = some (.complexPairs realCarrier) ∧
    named realCarrier = some .cauchyQQ ∧ named realModel = some (.realMeadow realCarrier) := by
  cases found : named model with
  | none => simp [found] at selected
  | some construction =>
    simp only [found, Option.bind_some] at selected
    cases construction <;> simp only [ExactConstruction.model?] at selected
    all_goals try contradiction
    case realMeadow c =>
      by_cases h : named c == some .cauchyQQ <;> simp [h, guard] at selected <;> cases selected
    case complexMeadow c r =>
      cases hc : named c with
      | none => simp [hc] at selected
      | some k =>
        cases k <;> simp only [hc] at selected
        all_goals try contradiction
        rename_i rc
        by_cases h : (named rc == some .cauchyQQ && named r == some (.realMeadow rc)) = true
        · simp [h, guard] at selected
          obtain ⟨rfl, rfl, rfl⟩ := selected
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨rfl, hc, h⟩
        · simp [h, guard] at selected
          cases selected

/-- The exact object ID is a member of the declarations of this accepted
revision. A numerical representation cannot satisfy the selected model lookup. -/
theorem public_standard_chart {json : Lean.Json} {main : Bool} (input : Wire.CheckedInput json main)
    {object model : DeclId} {dimension : Nat} {coords : List String}
    (member : ⟨object, .exactGeometry (.affine model dimension coords)⟩ ∈
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed) :
    let named := exactView input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    Wire.RevisionMatches json input.checked ∧ Wire.exactSources json input.input = .ok () ∧
    dimension ≤ Limits.algebraGenerators ∧
    dimension = coords.length ∧ coords.Nodup ∧
    ∃ profile, (named model).bind (·.model? named) = some profile ∧
      ∀ a b : Fin dimension → Coordinate profile, (fun i => embed profile (a i)) =
        (fun i => embed profile (b i)) → a = b := by
  dsimp only
  let checked := input.checked.pureProgram.authority.headers.declarations
  have good := ((Core.Typing.validDeclarations_iff _).mp checked.accepted).indexed.declarations _ member
  change (ExactConstruction.affine model dimension coords).valid (exactView checked.resolved.declarations.indexed) = true at good
  simp only [ExactConstruction.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isSome_iff_exists] at good
  obtain ⟨⟨⟨⟨profile, selected⟩, bounded⟩, size⟩, unique⟩ := good
  exact ⟨input.revisionMatches, Wire.exactSources_of_program input.decoded, bounded, size, unique, profile, selected, fun _ _ => chart_injective⟩

end VastitasOracle.ExactAffine
