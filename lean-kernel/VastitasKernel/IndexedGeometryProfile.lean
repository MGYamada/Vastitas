import VastitasKernel.IndexedCore

/-! An explicit, finite syntax-compatibility export. The provider supplies
unresolved paths, not trusted declaration IDs. This record grants no new
primitive, mathematical fact, dispatch key or edit authority. -/
namespace VastitasKernel.Indexed

structure GeometrySetting (α : Type) where
  domain : α
  marker : α
  baseObject : α
  affine : α
  base : α
  origin : α
  identity : α
  dimension : α
  deriving Repr, Inhabited

structure GeometryProfile (α : Type) where
  scheme : GeometrySetting α
  smooth : GeometrySetting α
  point : α
  morphism : α
  pointed : α
  compose : α
  apply : α
  deriving Repr, Inhabited

def GeometrySetting.objectType (setting : GeometrySetting DeclId) : ObjectType :=
  ⟨setting.domain, setting.marker⟩

def GeometrySetting.valid (env : Core.Declarations) (profile : GeometryProfile DeclId)
    (setting : GeometrySetting DeclId) : Bool :=
  let type := setting.objectType
  (match Indexed.lookup env.indexed setting.domain with | some (.classification ..) => true | _ => false) &&
  decide (type.Valid env.indexed) &&
  (ObjectRef.type? env.indexed (.global setting.baseObject)).any
    (fun base => decide (base.Refines env.indexed type)) &&
  (match env.primitive? setting.affine with
   | some (.descriptor implementation) => (implementationType env.indexed implementation).any
       (fun concrete => decide (concrete.Refines env.indexed type))
   | _ => false) &&
  env.primitive? setting.base == some (.global setting.baseObject) &&
  env.primitive? setting.origin == some (.origin type profile.point setting.baseObject) &&
  env.primitive? setting.identity == some (.identity type profile.morphism) &&
  env.primitive? setting.dimension == some (.dimension type) &&
  env.package? ⟨profile.pointed, [.domain setting.domain, .marker setting.marker]⟩ ==
    some ⟨type, [⟨profile.point, [.witness, .global setting.baseObject]⟩]⟩

def GeometryProfile.familyValid (env : Core.Declarations) (profile : GeometryProfile DeclId)
    (id : DeclId) (representation : FamilyRepresentation) : Bool :=
  (match Indexed.lookup env.indexed id with
   | some (.family family) => family.representation == representation && family.constraints == [.sameBase 0 1]
   | _ => false) &&
  [profile.scheme.objectType, profile.smooth.objectType].all fun type =>
    validApplication env.indexed ⟨id, [.object (.local type 0), .object (.local type 1)]⟩

def GeometryProfile.valid (env : Core.Declarations) (profile : GeometryProfile DeclId) : Bool :=
  profile.scheme.marker != profile.smooth.marker &&
  profile.familyValid env profile.point .point && profile.familyValid env profile.morphism .morphism &&
  profile.scheme.valid env profile && profile.smooth.valid env profile &&
  env.primitive? profile.compose == some (.compose profile.morphism) &&
  env.primitive? profile.apply == some (.apply profile.morphism profile.point)

def GeometryProfile.setting (profile : GeometryProfile DeclId) : BaseKind → GeometrySetting DeclId
  | .qq => profile.scheme | .cinfReal => profile.smooth

def GeometryProfile.package (profile : GeometryProfile DeclId) (base : BaseKind) : Application :=
  let setting := profile.setting base
  ⟨profile.pointed, [.domain setting.domain, .marker setting.marker]⟩

def GeometryProfile.baseOf (profile : GeometryProfile DeclId) (env : Environment)
    (type : ObjectType) : Option BaseKind :=
  if type.Refines env profile.scheme.objectType then some .qq
  else if type.Refines env profile.smooth.objectType then some .cinfReal else none

end VastitasKernel.Indexed
