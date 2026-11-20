import VastitasKernel.FloatProfile
import VastitasKernel.StorageRealization

namespace VastitasKernel.Indexed.AffineRealizationProfile

/-- A fresh mathematical declaration belongs to a physical constructor occurrence.
The package source is reserved in the wire, including as a dependency target. -/
structure Site where
  representation : Storage.Realization.Representation
  dimension : Nat
  span : Span
  deriving Repr, Inhabited

def Site.subject (site : Site) : DeclId :=
  ⟨Namespace.affineConstructor.scope, s!"AffineAt{site.span.start}"⟩

def identityGraph (subject : DeclId) : DeclId :=
  ⟨subject.scope, "IdentityOf" ++ subject.name⟩

def Site.descriptor (site : Site) : Storage.Realization.Descriptor :=
  ⟨site.subject, site.subject, site.representation⟩

private def ref (name : String) : Source.Path := ⟨[name], {}⟩

private def decl (name : String) (body : Source.Body) : Source.Declaration :=
  ⟨name, body, false, {}⟩

private def declarations (site : Site) : List Source.Declaration :=
  let real := site.representation.isReal
  let coords := (List.range site.dimension).map fun i => (if real then "x" else "z") ++ toString i
  let name := site.subject.name
  let space := if real then .smoothAffine (ref "SmoothR") site.dimension coords else
    .exactGeometry (.affine (ref "CC") site.dimension coords)
  let graph := if real then .morphism (ref "Smooth") [ref name, ref name] .identity else
    .exactGeometry (.identity (ref name))
  [⟨name, space, false, site.span⟩, ⟨(identityGraph site.subject).name, graph, false, site.span⟩]

/-- These are ordinary unresolved mathematical declarations. Both the inferred
base and each generated identity pass through the public indexed checker. -/
def package (sites : List Site) : DispatchSource.Package :=
  let real := if sites.any (·.representation.isReal) then
    [decl "CInfReal" .marker, decl "SmoothR" (.implementation (ref "CInfReal") .smoothAffine []),
     decl "CInfAffine" (.classification [] [ref "SmoothR"]),
     decl "Smooth" (.family ⟨[.object (ref "CInfAffine"), .object (ref "CInfAffine")],
       [.canonical 0, .canonical 1], .smooth⟩)] else []
  let complex := if sites.any (!·.representation.isReal) then
    [decl "Cauchy" (.exactGeometry .cauchyQQ), decl "Pairs" (.exactGeometry (.complexPairs (ref "Cauchy"))),
     decl "RR" (.exactGeometry (.realMeadow (ref "Cauchy"))),
     decl "CC" (.exactGeometry (.complexMeadow (ref "Pairs") (ref "RR")))] else []
  let root : Namespace.Module := {
    path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }
  let owner := Namespace.affineConstructor
  { id := owner.scope.package, dependencies := [], modules := [
    {module := root, declarations := []},
    {module := {root with path := owner.scope.path, resourceFunctions := [⟨owner.name, true, {}⟩]},
     declarations := real ++ complex ++ sites.flatMap declarations}] }

end VastitasKernel.Indexed.AffineRealizationProfile
