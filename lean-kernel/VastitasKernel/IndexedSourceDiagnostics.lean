import VastitasKernel.IndexedSourceTypes

/-! Source provenance is presentation metadata only. Object equality and scope
continue to use the independently checked nominal references, never these names. -/
namespace VastitasKernel.Indexed.Source.Diagnostics

structure Origin where
  name : Option String := none
  span : Span
  reason : String
  deriving Inhabited

abbrev Origins := Std.HashMap Nat Origin

def origin (origins : Origins) : ObjectRef → Option Origin
  | .local _ brand => origins[brand]?
  | .global _ => none

def objectTypeLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId)) (type : Indexed.ObjectType) : String :=
  match geometry.bind (·.baseOf env.indexed type) with
  | some base => base.settingName
  | none => type.domain.name ++ "<" ++ type.marker.name ++ ">"

def objectLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : ObjectRef → String
  | .global id =>
    match geometry with
    | some profile =>
      if id == profile.scheme.baseObject then "Base(QQ)"
      else if id == profile.smooth.baseObject then "Base(CInfReal)" else id.name
    | none => id.name
  | .local type brand =>
    match origins[brand]? with
    | some source => source.name.getD
        s!"{objectTypeLabel env geometry type} from {source.reason} at {source.span.line}:{source.span.column}"
    | none => s!"{objectTypeLabel env geometry type} object {brand}"

def indexLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : Index → String
  | .domain id | .marker id => id.name
  | .natural value => toString value
  | .object reference => objectLabel env geometry origins reference

def typeLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : Core.DataType → String
  | .pure .nat => "Nat" | .pure .int => "Int" | .pure .bool => "Bool" | .pure .unit => "Unit"
  | .pure (.pair .nat) => "Pair<Nat>" | .pure (.pair .int) => "Pair<Int>"
  | .object type => objectTypeLabel env geometry type
  | .indexed app | .package app =>
    let name := match geometry with
      | some profile =>
        if app.family == profile.point then "Point"
        else if app.family == profile.morphism then "Morphism"
        else if app.family == profile.pointed then "Pointed" else app.family.name
      | none => app.family.name
    name ++ "<" ++ String.intercalate ", " (app.indices.map (indexLabel env geometry origins)) ++ ">"

def objectNotes (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (refs : List ObjectRef) : List DiagnosticNote := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut notes := #[]
  for ref in refs do
    if let .local _ brand := ref then
      unless seen.contains brand do
        seen := seen.insert brand
        if let some source := origins[brand]? then
          notes := notes.push {
            span := source.span,
            message := s!"object {objectLabel env geometry origins ref} was introduced here by {source.reason}" }
  return notes.toList

def generativeNotes (origins : Origins) (refs : List ObjectRef) (span : Span) : List DiagnosticNote := Id.run do
  for left in refs do
    if let some a := origin origins left then
      if a.name.isNone && (a.reason == "Affine" || a.reason.startsWith "function call '" || a.reason.startsWith "primitive '") then
        for right in refs do
          if left != right then
            if let some b := origin origins right then
              if b.name.isNone && a.reason == b.reason then
                return [{ span, message := "help: each construction or call returning an object creates a fresh object, even with equal arguments; bind the object once with let and reuse that binding" }]
  return []

end VastitasKernel.Indexed.Source.Diagnostics
