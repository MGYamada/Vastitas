import CompatibilityLookup

namespace VastitasQualification.ExitAdmission
open VastitasKernel Indexed
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

inductive Payload where
  | indexed (d : Declaration)
  | package (shapes : List PackageShape)
  | primitive (op : PrimitiveBinding)
  deriving Inhabited

structure ProfileRow where
  name : String
  payload : Payload
  edges : List String
  deriving Inhabited

def ProfileRow.insert (r : ProfileRow) (env : Core.Declarations) : Core.Declarations :=
  let id := compatOwner r.name
  match r.payload with
  | .indexed d => {env with indexed := env.indexed ++ [⟨id,d⟩]}
  | .package shapes => {env with packages := env.packages ++ [⟨id,shapes⟩]}
  | .primitive op => {env with primitives := env.primitives ++ [⟨id,op⟩]}

def ProfileRow.record (r : ProfileRow) (refs : List Source.Reference) := r.edges.foldl (fun rs n => ref n :: rs) refs

private def settingRows (domain marker grid suffix : String) : List ProfileRow :=
  let base := "Base" ++ suffix
  let ty : ObjectType := ⟨compatOwner domain,compatOwner marker⟩
  [⟨marker,.indexed .marker,[]⟩,
   ⟨grid,.indexed (.implementation (compatOwner marker) .affineDescriptor [.origin,.dimension]),[marker]⟩,
   ⟨domain,.indexed (.classification [compatOwner "Objects"] [compatOwner grid]),["Objects",grid]⟩,
   ⟨base,.indexed (.global (compatOwner grid)),[grid]⟩,
   ⟨"affine" ++ suffix,.primitive (.descriptor (compatOwner grid)),[grid]⟩,
   ⟨"base" ++ suffix,.primitive (.global (compatOwner base)),[base]⟩,
   ⟨"origin" ++ suffix,.primitive (.origin ty (compatOwner "Point") (compatOwner base)),[domain,marker,"Point",base]⟩,
   ⟨"identity" ++ suffix,.primitive (.identity ty (compatOwner "Morphism")),[domain,marker,"Morphism"]⟩,
   ⟨"dimension" ++ suffix,.primitive (.dimension ty),[domain,marker]⟩]

private def family (repr : FamilyRepresentation) : Payload :=
  .indexed <| .family ⟨[.object (compatOwner "Objects"),.object (compatOwner "Objects")],[.sameBase 0 1],repr⟩
private def pointed (domain marker base : String) : PackageShape :=
  ⟨⟨compatOwner domain,compatOwner marker⟩,[⟨compatOwner "Point",[.witness,.global (compatOwner base)]⟩]⟩

def rows := settingRows "Scheme" "QQ" "GridQQ" "QQ" ++ settingRows "CInfScheme" "CInfReal" "GridSmooth" "Smooth" ++
  [⟨"Objects",.indexed (.classification [] [compatOwner "GridQQ",compatOwner "GridSmooth"]),["GridQQ","GridSmooth"]⟩,
   ⟨"Point",family .point,["Objects","Objects"]⟩, ⟨"Morphism",family .morphism,["Objects","Objects"]⟩,
   ⟨"Pointed",.package [pointed "Scheme" "QQ" "BaseQQ",pointed "CInfScheme" "CInfReal" "BaseSmooth"],
      ["Scheme","QQ","Point","BaseQQ","CInfScheme","CInfReal","Point","BaseSmooth"]⟩,
   ⟨"compose",.primitive (.compose (compatOwner "Morphism")),["Morphism"]⟩,
   ⟨"apply",.primitive (.apply (compatOwner "Morphism") (compatOwner "Point")),["Morphism","Point"]⟩]

def accumulated := rows.foldl (fun env row => row.insert env) ⟨[],[],[]⟩
def bodyEdges := rows.foldl (fun rs row => row.record rs) []
def profileSetting (domain marker suffix : String) : GeometrySetting DeclId :=
  ⟨compatOwner domain,compatOwner marker,compatOwner ("Base" ++ suffix),compatOwner ("affine" ++ suffix),
    compatOwner ("base" ++ suffix),compatOwner ("origin" ++ suffix),compatOwner ("identity" ++ suffix),compatOwner ("dimension" ++ suffix)⟩
def geometry : GeometryProfile DeclId := ⟨profileSetting "Scheme" "QQ" "QQ",profileSetting "CInfScheme" "CInfReal" "Smooth",
  compatOwner "Point",compatOwner "Morphism",compatOwner "Pointed",compatOwner "compose",compatOwner "apply"⟩
def geometryNames := ["Scheme","QQ","BaseQQ","affineQQ","baseQQ","originQQ","identityQQ","dimensionQQ",
  "CInfScheme","CInfReal","BaseSmooth","affineSmooth","baseSmooth","originSmooth","identitySmooth","dimensionSmooth","Point","Morphism","Pointed","compose","apply"]
def resolved : Source.Resolved := ⟨accumulated,bodyEdges.reverse ++ geometryNames.map (ref ·),some geometry⟩

def step (i : Nat) (env : Indexed.Core.Declarations) (refs : List Source.Reference) :
    Namespace.Result (Indexed.Core.Declarations × List Source.Reference) :=
  let row := headers.owned[i]!
  (Source.resolveBody idx {} {} row.1 row.2.span row.2.body env).run refs

def matched (i : Nat) := ∀ (env : Indexed.Core.Declarations) (rs : List Source.Reference),
  step i env rs = .ok ((rows[i]!).insert env,(rows[i]!).record rs)

def foldFrom (env : Indexed.Core.Declarations) (rs : List Source.Reference) :=
  (headers.owned.foldlM (fun env entry => Source.resolveBody idx {} {} entry.1 entry.2.span entry.2.body env) env).run rs

theorem rowNames : rows.map (·.name) = names := by rfl

end VastitasQualification.ExitAdmission
#print axioms VastitasQualification.ExitAdmission.rowNames
