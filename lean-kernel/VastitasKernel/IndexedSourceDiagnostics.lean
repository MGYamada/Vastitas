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
order is the diagnostic precedence: the operands' families first, in operand
order, then the object relations in the order listed. A binding or operand shape
without an entry has no requirements. New primitives extend this table with
their own entries. -/
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
    [.family "map" family map, .object "map" "base" (.global origin) base "the view's source base"]
  | .relativeEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices with
    | [.object source, .object target, .object base], [.object source', .object target', .object base'] =>
      [.object "second map" "source" source source' "the first map's source",
       .object "second map" "target" target target' "the first map's target",
       .object "second map" "base" base base' "the first map's base"]
    | _, _ => []
  | .relativeCoefficient family source target _ _, [.indexed ⟨map, indices⟩] =>
    .family "map" family map ::
    match indices with
    | [.object source', .object target', .object _] =>
      [.object "map" "source" (.global source) source' "the primitive's declared source",
       .object "map" "target" (.global target) target' "the primitive's declared target"]
    | _ => []
  | .relativePair family fiber, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices, plainFiber? env fiber with
    | [.object source, .object left, .object base], [.object source', .object right, .object base'],
        some (factor, factor', fiberBase) =>
      [.object "second map" "source" source source' "the first map's source",
       .object "first map" "base" (.global fiberBase) base "the fiber's base",
       .object "second map" "base" (.global fiberBase) base' "the fiber's base",
       .object "first map" "target" (.global factor) left "the fiber's first factor",
       .object "second map" "target" (.global factor') right "the fiber's second factor"]
    | _, _, _ => []
  | .smoothCompose family, [.indexed ⟨first, [.object middle, .object _]⟩,
      .indexed ⟨second, [.object _, .object middle']⟩] =>
    [.family "first map" family first, .family "second map" family second,
     .object "second map" "target" middle middle' "the first map's source"]
  | .smoothEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first map" family first, .family "second map" family second] ++
    match firstIndices, secondIndices with
    | [.object source, .object target], [.object source', .object target'] =>
      [.object "second map" "source" source source' "the first map's source",
       .object "second map" "target" target target' "the first map's target"]
    | _, _ => []
  | .smoothComposite family, [.indexed ⟨map, _⟩] => [.family "map" family map]
  | .fiberVector _ smooth object, .indexed ⟨point, [.object (.global _), .object x]⟩ :: _ =>
    [.family "point" smooth point,
     .object "point" "target" (.global object) x "the primitive's declared object"]
  | .fiberAt family smooth, [.indexed ⟨element, [.object x]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "element" family element, .family "point" smooth point,
     .object "point" "target" x x' "the element's object"]
  | .fiberEqual family, [.indexed ⟨first, firstIndices⟩, .indexed ⟨second, secondIndices⟩] =>
    [.family "first element" family first, .family "second element" family second] ++
    match firstIndices, secondIndices with
    | [.object x], [.object x'] => [.object "second element" "object" x x' "the first element's object"]
    | _, _ => []
  | .fiberComponent family object _, [.indexed ⟨element, [.object x]⟩] =>
    [.family "element" family element,
     .object "element" "object" (.global object) x "the primitive's declared object"]
  | .fiberPairing cotangent tangent, [.indexed ⟨covector, [.object x]⟩, .indexed ⟨vector, [.object x']⟩] =>
    [.family "covector" cotangent covector, .family "vector" tangent vector,
     .object "vector" "object" x x' "the covector's object"]
  | .cotangentPullback smooth cotangent _, [.indexed ⟨map, [.object x, .object y]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩, .indexed ⟨seed, [.object y']⟩] =>
    [.family "map" smooth map, .family "point" smooth point, .family "seed" cotangent seed,
     .object "point" "target" x x' "the map's source",
     .object "seed" "object" y y' "the map's target"]
  | .differential smooth _ line, [.indexed ⟨function, [.object x, .object y]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "function" smooth function, .family "point" smooth point,
     .object "function" "target" (.global line) y "the primitive's declared line",
     .object "point" "target" x x' "the function's source"]
  | .linearize smooth _, [.indexed ⟨map, [.object x, .object _]⟩,
      .indexed ⟨point, [.object (.global _), .object x']⟩] =>
    [.family "map" smooth map, .family "point" smooth point,
     .object "point" "target" x x' "the map's source"]
  | .cotangentBackward tape cotangent, [.indexed ⟨recorded, [.object _, .object y]⟩,
      .indexed ⟨seed, [.object y']⟩] =>
    [.family "tape" tape recorded, .family "seed" cotangent seed,
     .object "seed" "object" y y' "the tape's target"]
  | .metricFlat _ object _ tangent _, [.indexed ⟨vector, [.object x]⟩] =>
    [.family "vector" tangent vector,
     .object "vector" "object" (.global object) x "the metric's object"]
  | .metricSharp _ _ object _ _ cotangent _, [.indexed ⟨covector, [.object x]⟩] =>
    [.family "covector" cotangent covector,
     .object "covector" "object" (.global object) x "the metric's object"]
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
  all_goals try simp only [List.mem_append] at member
  all_goals try split at member
  all_goals try simp only [List.mem_nil_iff, or_false] at member
  all_goals simp only [PrimitiveAssociation, ObjectType.Refines, pairFactors, Application.mk.injEq,
    List.cons.injEq, Index.object.injEq, and_true] at association
  -- Shapes more general than the contract's own patterns: split the contract.
  all_goals try split at association
  all_goals simp only [List.mem_cons, List.mem_nil_iff, or_false, or_assoc] at member
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

theorem explainPrimitive_binding {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    (explained : explainPrimitive env binding allowed brand operands result = some .binding) :
    validPrimitiveBinding env binding = false := by
  unfold explainPrimitive at explained
  revert explained
  split
  · simp
  · split
    · simp_all
    · split
      · simp
      · split <;> simp

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

theorem explainPrimitive_result {env : Environment} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {brand : Nat} {operands : List ValueType} {result : ValueType}
    (explained : explainPrimitive env binding allowed brand operands result = some .result) :
    validValueType env result = false := by
  unfold explainPrimitive at explained
  revert explained
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp_all

private def withArticle (role : String) : String :=
  (if "aeiou".contains role.front then "an " else "a ") ++ role

private def qualifiedName (id : DeclId) : String :=
  String.intercalate "::" (id.scope.package.name :: id.scope.path ++ [id.name])

/-- Labels for two declarations; equal short names are qualified until they differ. -/
private def declarationLabels (expected actual : DeclId) : String × String :=
  if expected == actual || expected.name != actual.name then (expected.name, actual.name)
  else if qualifiedName expected != qualifiedName actual then (qualifiedName expected, qualifiedName actual)
  else (s!"{qualifiedName expected} in {expected.scope.package.source}",
    s!"{qualifiedName actual} in {actual.scope.package.source}")

/-- Labels for two objects; distinct objects with equal labels are told apart
by their declarations or introduction sites. -/
private def objectLabels (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (expected actual : ObjectRef) : String × String :=
  let label := objectLabel env geometry origins
  if expected == actual || label expected != label actual then (label expected, label actual)
  else match expected, actual with
    | .global e, .global a => declarationLabels e a
    | _, _ =>
      let precise (reference : ObjectRef) := match reference with
        | .global id => qualifiedName id
        | .local _ brand => match origins[brand]? with
          | some source => s!"{label reference} introduced at {source.span.line}:{source.span.column}"
          | none => s!"{label reference} (object {brand})"
      (precise expected, precise actual)

/-- The primary message for an explained failure of the primitive `primitive`. -/
def explainFailure (env : Core.Declarations) (geometry : Option (GeometryProfile DeclId))
    (origins : Origins) (primitive resultLabel : String) : PrimitiveFailure → String
  | .binding => s!"{primitive} is not bound to a valid capability or family contract"
  | .result => s!"{primitive} would produce {resultLabel}, which is not a valid type"
  | .role (.family role expected actual) =>
    let (wanted, found) := declarationLabels expected actual
    s!"{primitive} requires {withArticle role} of family {wanted}, but the supplied {role} has family {found}"
  | .role (.object role field expected actual reason) =>
    let (wanted, found) := objectLabels env geometry origins expected actual
    let coefficient := match expected.type? env.indexed, actual.type? env.indexed with
      | some wantedType, some foundType =>
        if wantedType.marker == foundType.marker then ""
        else s!", whose coefficient marker {foundType.marker.name} differs from {wantedType.marker.name}"
      | _, _ => ""
    s!"{primitive} requires {withArticle role} with {field} {wanted} ({reason}), " ++
      s!"but the supplied {role} has {field} {found}{coefficient}"
  | .role (.marker role reference expected actual) =>
    let (wanted, found) := declarationLabels expected actual
    s!"{primitive} requires {withArticle role} with coefficient marker {wanted}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has coefficient marker {found}"
  | .role (.domain role reference expected actual) =>
    let (wanted, found) := declarationLabels expected.domain actual.domain
    s!"{primitive} requires {withArticle role} whose domain lies within {wanted}, " ++
      s!"but the supplied {role} {objectLabel env geometry origins reference} has domain {found}"

end VastitasKernel.Indexed.Source.Diagnostics
