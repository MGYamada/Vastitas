import VastitasKernel.LegacyIndexed
import VastitasKernel.IndexedGeometryProfile

namespace VastitasKernel.Indexed.GeometryCompatibilityRegression

private def id := LegacyIndexed.id
private def setting (base : BaseKind) : GeometrySetting DeclId :=
  ⟨id (if base == .qq then "Scheme" else "Smooth"), LegacyIndexed.marker base,
   LegacyIndexed.baseObject base, LegacyIndexed.primitiveId "affine" base,
   LegacyIndexed.primitiveId "base" base, LegacyIndexed.primitiveId "origin" base,
   LegacyIndexed.primitiveId "identity" base, LegacyIndexed.primitiveId "dimension" base⟩

private def profile : GeometryProfile DeclId :=
  ⟨setting .qq, setting .cinfReal, id "Point", id "Morphism", id "Pointed", id "compose", id "apply"⟩

private def env : Core.Declarations := {
  indexed := LegacyIndexed.declarations.indexed ++ [.qq, .cinfReal].map (fun base =>
    ⟨(setting base).domain, .classification [id "Objects"] [LegacyIndexed.implementation base]⟩)
  packages := [⟨profile.pointed, [.qq, .cinfReal].map fun base =>
    ⟨(setting base).objectType, [⟨profile.point, [.witness, .global (setting base).baseObject]⟩]⟩⟩]
  primitives := LegacyIndexed.declarations.primitives.map fun declaration =>
    let binding := match declaration.binding with
      | .origin type family base => .origin (profile.setting (if type.marker == profile.scheme.marker then .qq else .cinfReal)).objectType family base
      | .identity type family => .identity (profile.setting (if type.marker == profile.scheme.marker then .qq else .cinfReal)).objectType family
      | .dimension type => .dimension (profile.setting (if type.marker == profile.scheme.marker then .qq else .cinfReal)).objectType
      | other => other
    { declaration with binding } }

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"geometry compatibility regression: {name}")

#eval check "declared finite environment" (Core.validDeclarations env)
#eval check "independent export audit" (profile.valid env)
#eval check "origin cannot name dimension" (!({ profile with scheme := { profile.scheme with origin := profile.scheme.dimension } }.valid env))
#eval check "markers stay distinct" (!({ profile with smooth := { profile.smooth with marker := profile.scheme.marker } }.valid env))
#eval check "point and morphism cannot be interchanged" (!({ profile with point := profile.morphism }.valid env))
#eval check "base object cannot be a marker" (!({ profile with scheme := { profile.scheme with baseObject := profile.scheme.marker } }.valid env))

private def constraints (family : DeclId) (rules : List Constraint) : Core.Declarations :=
  { env with indexed := env.indexed.map fun entry =>
    if entry.id == family then match entry.declaration with
      | .family contract => { entry with declaration := .family { contract with constraints := rules } }
      | _ => entry
    else entry }

#eval check "sealed endpoint families already require same-base" (!(Core.validDeclarations (constraints profile.point [])))
#eval check "legacy export cannot erase same-base constraint" (!(profile.valid (constraints profile.point [])))
#eval check "stronger map family is valid general indexed data" (Core.validDeclarations
  (constraints profile.morphism [.sameBase 0 1, .sameObject 0 1]))
#eval check "legacy export cannot silently restrict all maps to equal endpoints" (!(profile.valid
  (constraints profile.morphism [.sameBase 0 1, .sameObject 0 1])))

#eval check "canonical ordinary base is in its full domain" (decide
  ((ObjectRef.type? env.indexed (.global profile.scheme.baseObject)).any
    (fun actual => decide (actual.Refines env.indexed profile.scheme.objectType)) = true))
#eval check "base/marker swap cannot select a package" ((env.package?
  ⟨profile.pointed, [.domain profile.scheme.domain, .object (.global profile.scheme.baseObject)]⟩).isNone)

end VastitasKernel.Indexed.GeometryCompatibilityRegression
