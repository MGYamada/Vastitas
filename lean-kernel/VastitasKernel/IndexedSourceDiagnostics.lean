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

def familyLabel (geometry : Option (GeometryProfile DeclId)) (family : DeclId) : String :=
  match geometry with
  | some profile =>
    if family == profile.point then "Point"
    else if family == profile.morphism then "Morphism"
    else if family == profile.pointed then "Pointed" else family.name
  | none => family.name

def typeLabel (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) : Core.DataType → String
  | .pure .nat => "Nat" | .pure .int => "Int" | .pure .bool => "Bool" | .pure .unit => "Unit"
  | .pure (.pair .nat) => "Pair<Nat>" | .pure (.pair .int) => "Pair<Int>"
  | .object type => objectTypeLabel env geometry type
  | .indexed app | .package app =>
    familyLabel geometry app.family ++ "<" ++
      String.intercalate ", " (app.indices.map (indexLabel env geometry origins)) ++ ">"

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

/-! ## Rejected primitive calls

`validPrimitive` remains the only acceptance check. Only after it rejects a call
does `explainPrimitive` name one failed requirement, chosen from the resolved
binding and the actual operand types, never from the call's source spelling. -/

/-- One operand requirement of a primitive contract, named by the operand's role. -/
inductive RoleRequirement where
  /-- The `role` operand must be an application of the family `expected`. -/
  | family (role : String) (expected actual : DeclId)
  /-- The `field` index of the `role` operand must be the nominal object
  `expected`; `reason` names the operand or declaration that fixes it. -/
  | object (role field : String) (expected actual : ObjectRef) (reason : String)
  /-- The `role` operand, the object `reference`, must have the coefficient marker `expected`. -/
  | marker (role : String) (reference : ObjectRef) (expected actual : DeclId)
  /-- Every implementation in the domain of the `role` operand's type `actual`
  must lie in the domain of `expected`. -/
  | domain (role : String) (reference : ObjectRef) (expected actual : Indexed.ObjectType)
  deriving Repr, Inhabited, DecidableEq

def RoleRequirement.holds (env : Environment) : RoleRequirement → Bool
  | .family _ expected actual => expected == actual
  | .object _ _ expected actual _ => expected == actual
  | .marker _ _ expected actual => expected == actual
  | .domain _ _ expected actual =>
    decide (∀ id ∈ actual.implementations env, id ∈ expected.implementations env)

/-- The role table of each primitive binding, for the actual operand types. Its
order is the diagnostic precedence: operand families first, in operand order,
then the object relations. A binding or operand shape without an entry has no
requirements. New primitives extend this table with their own entries. -/
def roleTable (env : Environment) : PrimitiveBinding → List ValueType → List RoleRequirement
  | .origin expected _ _, [.object actual reference]
  | .identity expected _, [.object actual reference]
  | .dimension expected, [.object actual reference] =>
    [.marker "object" reference expected.marker actual.marker, .domain "object" reference expected actual]
  | .compose family, [.indexed ⟨first, [.object middle, .object _]⟩,
      .indexed ⟨second, [.object _, .object middle']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source"]
  | .apply maps points, [.indexed ⟨map, [.object source, .object _]⟩,
      .indexed ⟨point, [.object target, .object _]⟩] =>
    [.family "map" maps map, .family "point" points point,
     .object "point" "target" source target "the map's source"]
  | .relativeCompose family, [.indexed ⟨first, [.object middle, .object _, .object base]⟩,
      .indexed ⟨second, [.object _, .object middle', .object base']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source",
     .object "second map" "base" base base' "the first map's base"]
  | .relativeView family origin _, [.indexed ⟨map, [.object _, .object _, .object base]⟩] =>
    [.family "map" family map,
     .object "map" "base" (.global origin) base "the base that the primitive views from"]
  | .relativeEqual family, [.indexed ⟨first, [.object source, .object target, .object base]⟩,
      .indexed ⟨second, [.object source', .object target', .object base']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "source" source source' "the first map's source",
     .object "second map" "target" target target' "the first map's target",
     .object "second map" "base" base base' "the first map's base"]
  | .relativePair family fiber, [.indexed ⟨first, [.object source, .object left, .object base]⟩,
      .indexed ⟨second, [.object source', .object right, .object base']⟩] =>
    match plainFiber? env fiber with
    | some (factor, factor', fiberBase) =>
      [.family "first map" family first, .family "second map" family second,
       .object "second map" "source" source source' "the first map's source",
       .object "first map" "base" (.global fiberBase) base "the fiber's base",
       .object "second map" "base" (.global fiberBase) base' "the fiber's base",
       .object "first map" "target" (.global factor) left "the fiber's first factor",
       .object "second map" "target" (.global factor') right "the fiber's second factor"]
    | none => []
  | _, _ => []

/-- Every requirement in the role table is part of the association contract, so
a reported requirement is a genuine failure of that contract. -/
theorem roleTable_sound {env : Environment} {binding : PrimitiveBinding} {allowed : List ObjectRef}
    {brand : Nat} {operands : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env binding allowed brand operands result) :
    ∀ requirement ∈ roleTable env binding operands, requirement.holds env = true := by
  intro requirement member
  unfold roleTable at member
  split at member
  all_goals try simp only [List.mem_nil_iff] at member
  all_goals try split at member
  all_goals try simp only [List.mem_nil_iff] at member
  all_goals simp only [PrimitiveAssociation, ObjectType.Refines, pairFactors, Application.mk.injEq,
    List.cons.injEq, Index.object.injEq, and_true] at association
  all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  all_goals repeat' rcases member with rfl | member
  all_goals simp only [RoleRequirement.holds, beq_iff_eq, decide_eq_true_eq]
  all_goals try simp only [and_assoc] at association
  all_goals repeat obtain ⟨_, association⟩ := association
  all_goals subst_vars
  all_goals first | rfl | assumption | simp_all [Bool.and_eq_true, beq_iff_eq]

/-- Why `validPrimitive` rejected a call. -/
inductive PrimitiveFailure where
  /-- The declared binding is not a valid capability or family contract. -/
  | binding
  /-- An operand violates this requirement of the role table. -/
  | role (requirement : RoleRequirement)
  /-- No role requirement fails, but the result is not a valid type. -/
  | result
  deriving Repr, Inhabited, DecidableEq

/-- The precedence is the binding, then the role table in its order, then the
result. `none` means that no cause was established, including for every
accepted call. -/
def explainPrimitive (env : Environment) (binding : PrimitiveBinding) (allowed : List ObjectRef)
    (brand : Nat) (operands : List ValueType) (result : ValueType) : Option PrimitiveFailure :=
  if validPrimitive env binding allowed brand operands result then none
  else if !validPrimitiveBinding env binding then some .binding
  else match (roleTable env binding operands).find? (!·.holds env) with
    | some requirement => some (.role requirement)
    | none => if validValueType env result then none else some .result

theorem explainPrimitive_rejected {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    {failure : PrimitiveFailure}
    (explained : explainPrimitive env binding allowed brand operands result = some failure) :
    validPrimitive env binding allowed brand operands result = false := by
  cases accepted : validPrimitive env binding allowed brand operands result
  · rfl
  · simp [explainPrimitive, accepted] at explained

theorem explainPrimitive_role {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    {requirement : RoleRequirement}
    (explained : explainPrimitive env binding allowed brand operands result = some (.role requirement)) :
    requirement ∈ roleTable env binding operands ∧ requirement.holds env = false ∧
      ¬ PrimitiveAssociation env binding allowed brand operands result := by
  unfold explainPrimitive at explained
  split at explained
  · cases explained
  split at explained
  · cases explained
  split at explained
  · rename_i found
    simp only [Option.some.injEq, PrimitiveFailure.role.injEq] at explained
    rw [explained] at found
    have member := List.mem_of_find?_eq_some found
    have fails : requirement.holds env = false := by simpa using List.find?_some found
    refine ⟨member, fails, fun association => ?_⟩
    simp [roleTable_sound association requirement member] at fails
  · split at explained <;> cases explained

private def withArticle (role : String) : String :=
  (if "aeiou".contains role.front then "an " else "a ") ++ role

/-- The primary message for an explained failure of the primitive `primitive`. -/
def explainFailure (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (primitive resultLabel : String) : PrimitiveFailure → String
  | .binding => s!"primitive '{primitive}' is not bound to a valid capability or family contract"
  | .result => s!"{primitive} would produce {resultLabel}, which is not a valid instance of its family"
  | .role (.family role expected actual) =>
    s!"{primitive} requires {withArticle role} of family {familyLabel geometry expected}, " ++
      s!"but the supplied {role} has family {familyLabel geometry actual}"
  | .role (.object role field expected actual reason) =>
    let label := objectLabel env geometry origins
    let coefficient := match expected.type? env.indexed, actual.type? env.indexed with
      | some wanted, some found =>
        if wanted.marker == found.marker then ""
        else s!", whose coefficient marker {found.marker.name} differs from {wanted.marker.name}"
      | _, _ => ""
    s!"{primitive} requires {withArticle role} with {field} {label expected} ({reason}), " ++
      s!"but the supplied {role} has {field} {label actual}{coefficient}"
  | .role (.marker role reference expected actual) =>
    s!"{primitive} requires {withArticle role} with coefficient marker {expected.name}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has coefficient marker {actual.name}"
  | .role (.domain role reference expected actual) =>
    s!"{primitive} requires {withArticle role} whose domain lies within {expected.domain.name}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has domain {actual.domain.name}"

end VastitasKernel.Indexed.Source.Diagnostics
