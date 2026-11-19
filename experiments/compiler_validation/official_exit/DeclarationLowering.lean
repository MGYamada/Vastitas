import DeclarationPasses
import DeclarationFold

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem twoPasses {α β σ : Type} (x : StateT σ Namespace.Result α) (f : α → StateT σ Namespace.Result β)
    (s t u : σ) (a : α) (b : β) (first : x.run s = .ok (a,t)) (second : (f a).run t = .ok (b,u)) :
    (x >>= f).run s = .ok (b,u) := by
  rw [StateT.run_bind,first]
  exact second

def lowerBodies (cache : Source.ProjectionCache) : Source.ResolveM Core.Declarations :=
  headers.owned.foldlM (fun env entry => Source.resolveBody idx {} cache entry.1 entry.2.span entry.2.body env) ⟨[],[],[]⟩

theorem initial : (Source.buildProjectionCache idx {} headers.owned >>= lowerBodies).run [] = .ok (accumulated,bodyEdges) :=
  twoPasses _ lowerBodies [] [] bodyEdges {} accumulated projections bodyFold

theorem initialLiteral : (Source.buildProjectionCache idx {} headers.owned >>= fun cache =>
    headers.owned.foldlM (fun env entry => Source.resolveBody idx {} cache entry.1 entry.2.span entry.2.body env)
    (⟨[],[],[]⟩ : Core.Declarations)).run [] = .ok (accumulated, bodyEdges) := initial

theorem actualLowered : Source.lower headers = .ok resolved := by
  unfold Source.lower
  dsimp only
  rw [graphs, show headers.indexed = idx from rfl, initialLiteral]
  rw [← sources]
  simp only [bind, Except.bind, smoothImplementations, opens, affine, smooth, metrics, frames, nature]
  conv in (List.filterMapM _ headers.owned) =>
    change (Except.ok [] : Namespace.Result (List (DeclId × DeclId)))
  simp only [spectral, averages, models, errorbars]
  conv in (List.filterMapM _ headers.owned) =>
    change (Except.ok [] : Namespace.Result (List (DeclId × DeclId)))
  simp only [relative, gluing, exportResolved]
  rfl

theorem namesPreserved : accumulated.ids = headers.declarationIds := by rfl

theorem referenceValid (n : String) (h : n ∈ names) : (ref n).Valid idx := by
  unfold Source.Reference.Valid
  exact ⟨show compatibilityScope ∈ idx.scopes by decide,rfl,congrArg Except.toOption (resolveMember n h {})⟩

theorem referencesValid : Source.ReferencesValid idx resolved := by
  have stored : resolved.references = ((rows.flatMap (·.edges) ++ geometryNames).map (ref ·)) := by rfl
  have existing : ∀ n ∈ rows.flatMap (·.edges) ++ geometryNames, n ∈ names := by decide
  intro r member
  rw [stored] at member
  obtain ⟨n,found,rfl⟩ := List.mem_map.mp member
  exact referenceValid n (existing n found)

theorem roles : geometry.valid accumulated = true := by decide

/-- The actual checked source pass returns this precise data, preserving every
nominal entry and ordered reference. Its public exported roles are valid. -/
theorem loweredAndAudited : Source.lower headers = .ok resolved ∧
    Source.ReferencesValid headers.indexed resolved ∧ resolved.declarations.ids = headers.declarationIds ∧
    resolved.geometry.all (·.valid resolved.declarations) = true :=
  ⟨actualLowered,referencesValid,namesPreserved,roles⟩

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.loweredAndAudited
