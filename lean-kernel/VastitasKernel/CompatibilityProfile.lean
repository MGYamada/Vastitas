import VastitasKernel.IndexedDispatchSource

/-! The kernel-owned compatibility profile of the legacy geometry (`Scheme`,
`CInfScheme`, `Point`, `Morphism`, `Pointed` and their primitives). The wire
schemas of protocols 2 to 6 cannot carry library metadata, so
`LegacySource.adapt` appends this package to every program of those
protocols. A protocol-9 request asks for the same package with its optional
field `legacy_geometry` (`ResourceSource.Program.legacyGeometry`, #533).

The package is ordinary unresolved source: closed declarations and one
`geometry_compat` export, which pass the same declaration and role checks as a
source library. It grants no new primitive, mathematical fact, dispatch key or
edit authority, and its identity is reserved (`reservedSource`), so no request
can supply or name it. -/
namespace VastitasKernel.Indexed.CompatibilityProfile

/-- The identity of the profile package. It is independent of display
filenames, and the original namespace of a request validates before the
profile is added. -/
def profileId : Namespace.PackageId := ⟨"vastitas:compat:2-6", "legacy_geometry", "1.0.0"⟩

private def rootModule : Namespace.Module := {
  path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }

private def reference (name : String) : Source.Path := ⟨[name], {}⟩
private def declaration (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def setting (base : BaseKind) : GeometrySetting Source.Path :=
  let suffix := if base == .qq then "QQ" else "Smooth"
  ⟨reference (if base == .qq then "Scheme" else "CInfScheme"),
   reference (if base == .qq then "QQ" else "CInfReal"), reference ("Base" ++ suffix),
   reference ("affine" ++ suffix), reference ("base" ++ suffix), reference ("origin" ++ suffix),
   reference ("identity" ++ suffix), reference ("dimension" ++ suffix)⟩

/-- The `geometry_compat` export of the profile package. -/
def geometryProfile : GeometryProfile Source.Path :=
  ⟨setting .qq, setting .cinfReal, reference "Point", reference "Morphism", reference "Pointed",
   reference "compose", reference "apply"⟩

private def settingDeclarations (base : BaseKind) : List Source.Declaration :=
  let s := setting base
  let implementation := reference (if base == .qq then "GridQQ" else "GridSmooth")
  let type : Source.ObjectType := ⟨s.domain, s.marker⟩
  [declaration s.marker.name .marker,
   declaration implementation.name (.implementation s.marker .affineDescriptor [.origin, .dimension]),
   declaration s.domain.name (.classification [reference "Objects"] [implementation]),
   declaration s.baseObject.name (.global implementation),
   declaration s.affine.name (.primitive ⟨"descriptor", [("implementation", .path implementation)]⟩),
   declaration s.base.name (.primitive ⟨"global", [("declaration", .path s.baseObject)]⟩),
   declaration s.origin.name (.primitive ⟨"origin", [("domain", .objectType type),
     ("point_family", .path geometryProfile.point), ("base_object", .path s.baseObject)]⟩),
   declaration s.identity.name (.primitive ⟨"identity", [("domain", .objectType type),
     ("map_family", .path geometryProfile.morphism)]⟩),
   declaration s.dimension.name (.primitive ⟨"dim", [("domain", .objectType type)]⟩)]

/-- Explicit closed declarations of the legacy geometry. Every declaration and
role is checked by the common checker. -/
def profilePackage : DispatchSource.Package := {
  id := profileId, dependencies := [], geometryCompat := some geometryProfile,
  modules := [{ module := rootModule, declarations :=
    settingDeclarations .qq ++ settingDeclarations .cinfReal ++
    [declaration "Objects" (.classification [] [reference "GridQQ", reference "GridSmooth"]),
     declaration "Point" (.family ⟨[.object (reference "Objects"), .object (reference "Objects")], [.sameBase 0 1], .point⟩),
     declaration "Morphism" (.family ⟨[.object (reference "Objects"), .object (reference "Objects")], [.sameBase 0 1], .morphism⟩),
     declaration "Pointed" (.package ([.qq, .cinfReal].map fun base =>
       let s := setting base
       ⟨⟨s.domain, s.marker⟩, [⟨reference "Point", [.witness, .global s.baseObject]⟩]⟩)),
     declaration "compose" (.primitive ⟨"compose", [("map_family", .path (reference "Morphism"))]⟩),
     declaration "apply" (.primitive ⟨"apply", [("map_family", .path (reference "Morphism")),
       ("point_family", .path (reference "Point"))]⟩)] }] }

end VastitasKernel.Indexed.CompatibilityProfile
