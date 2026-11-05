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

/-! ### The role table, derived from the binding's shape

The requirements of a shape, for the actual operand types, in the diagnostic
precedence: the operands' families first, in operand order, then the fixed
indices in operand and slot order, then the requirements of each relation in
the order the shape lists them. The table applies once the operands have the
shape's index pattern (`Shape.shaped`); before that a rejected call is a shape
mismatch, which the generic endpoint message lists, except that a shape with
`families := .early` reports the families as soon as each operand is of the
expected kind. A binding or operand list without a requirement has none. -/
end VastitasKernel.Indexed.Source.Diagnostics

namespace VastitasKernel.Indexed.Shape
open VastitasKernel.Indexed.Source.Diagnostics

/-- The role and index field at a position of the shape. -/
def roleField (shape : Shape) (position : Position) : Option (String × String) :=
  match shape.operands[position.operand]? with
  | some (.indexed role _ slots) => match slots[position.slot]? with
    | some (.var field) => some (role, field)
    | some (.fixed _ field _) => some (role, field)
    | _ => none
  | _ => none

def operandRole : Operand → Option String
  | .indexed role _ _ => some role
  | .application role _ => some role
  | _ => none

/-- The families of the indexed operands, in operand order. -/
def familyRequirements : List Operand → List ValueType → List RoleRequirement
  | .indexed role family _ :: operands, .indexed application :: arguments =>
      .family role family application.family :: familyRequirements operands arguments
  | .application role family :: operands, .indexed application :: arguments =>
      .family role family application.family :: familyRequirements operands arguments
  | _ :: operands, _ :: arguments => familyRequirements operands arguments
  | _, _ => []

/-- The fixed indices of one operand, in slot order. -/
def fixedSlotRequirements (role : String) : List Slot → List Index → List RoleRequirement
  | .fixed ref field reason :: slots, .object actual :: indices =>
      .object role field ref actual reason :: fixedSlotRequirements role slots indices
  | _ :: slots, _ :: indices => fixedSlotRequirements role slots indices
  | _, _ => []

/-- The fixed indices of the indexed operands, in operand order. -/
def fixedRequirements : List Operand → List ValueType → List RoleRequirement
  | .indexed role _ slots :: operands, .indexed application :: arguments =>
      fixedSlotRequirements role slots application.indices ++ fixedRequirements operands arguments
  | _ :: operands, _ :: arguments => fixedRequirements operands arguments
  | _, _ => []

/-- The object references of an index list whose indices are all objects. -/
def objectIndices : List Index → Option (List ObjectRef)
  | [] => some []
  | .object ref :: indices => (objectIndices indices).map (ref :: ·)
  | _ => none

/-- The object references of an indexed argument whose indices are all objects. -/
def indicesAt (arguments : List ValueType) (operand : Nat) : Option (List ObjectRef) :=
  (applicationAt arguments operand).bind (objectIndices ·.indices)

/-- The requirement that explains a failed relation, when the operands have
the parts it compares. -/
def _root_.VastitasKernel.Indexed.Relation.requirement (env : Environment) (shape : Shape)
    (arguments : List ValueType) : Relation → List RoleRequirement
  | .sameRef first second =>
    match shape.roleField first, shape.roleField second, refAt arguments first, refAt arguments second with
    | some (firstRole, firstField), some (secondRole, secondField), some expected, some actual =>
      [.object secondRole secondField expected actual s!"the {firstRole}'s {firstField}"]
    | _, _, _, _ => []
  | .sameApplication first second fields =>
    match (shape.operands[first]?).bind operandRole, (shape.operands[second]?).bind operandRole,
        indicesAt arguments first, indicesAt arguments second with
    | some firstRole, some secondRole, some expected, some actual =>
      if expected.length == fields.length && actual.length == fields.length then
        (fields.zip (expected.zip actual)).map fun (field, expected, actual) =>
          .object secondRole field expected actual s!"the {firstRole}'s {field}"
      else []
    | _, _, _, _ => []
  | .fixedFrom position lookup reason =>
    match shape.roleField position, refAt arguments position, lookup env with
    | some (role, field), some actual, some expected => [.object role field expected actual reason]
    | _, _, _ => []
  | .pointDimension _ _ => []
  | .refines operand =>
    match shape.operands[operand]?, objectAt arguments operand with
    | some (.object role expected), some (actual, ref) =>
      [.marker role ref expected.marker actual.marker, .domain role ref expected actual]
    | _, _ => []
  | .freshBrand => []

/-- The slots of `operand` at which the shape fixes a point's dimension. -/
def pointSlots (shape : Shape) (operand : Nat) : List Nat :=
  shape.relations.filterMap fun
    | .pointDimension position _ => if position.operand == operand then some position.slot else none
    | _ => none

/-- Whether an index list has the pattern of the slots: one object per slot,
and a global object at the slots of `points`, since only a global object has
a dimension. -/
def slotsShaped (points : List Nat) : Nat → List Slot → List Index → Bool
  | _, [], [] => true
  | slot, _ :: slots, .object ref :: indices =>
      (!points.contains slot || ref matches .global _) && slotsShaped points (slot + 1) slots indices
  | _, _, _ => false

/-- Whether each operand is of the kind the shape lists: as many operands as
the shape lists, or more before a tail. -/
def kindsMatch (tailed : Bool) : List Operand → List ValueType → Bool
  | [], rest => tailed || rest.isEmpty
  | .natural :: operands, .natural :: arguments => kindsMatch tailed operands arguments
  | .object _ _ :: operands, .object _ _ :: arguments => kindsMatch tailed operands arguments
  | .indexed _ _ _ :: operands, .indexed _ :: arguments => kindsMatch tailed operands arguments
  | .application _ _ :: operands, .indexed _ :: arguments => kindsMatch tailed operands arguments
  | _, _ => false

/-- Whether the operands have the shape's index pattern: the kinds, and the
pattern of each indexed operand's slots. Families, fixed references and the
tail are not part of the pattern; they are what the table reports. -/
def shaped (shape : Shape) : Nat → List Operand → List ValueType → Bool
  | _, [], rest => shape.tail.isSome || rest.isEmpty
  | index, .natural :: operands, .natural :: arguments => shaped shape (index + 1) operands arguments
  | index, .object _ _ :: operands, .object _ _ :: arguments => shaped shape (index + 1) operands arguments
  | index, .indexed _ _ slots :: operands, .indexed application :: arguments =>
      slotsShaped (shape.pointSlots index) 0 slots application.indices &&
        shaped shape (index + 1) operands arguments
  | index, .application _ _ :: operands, .indexed _ :: arguments => shaped shape (index + 1) operands arguments
  | _, _, _ => false

/-- Whether the table reports the families, by the shape's precedence. -/
def reportsFamilies (shape : Shape) (arguments : List ValueType) : Bool :=
  match shape.families with
  | .shaped => shape.shaped 0 shape.operands arguments
  | .early => kindsMatch shape.tail.isSome shape.operands arguments

def roles (env : Environment) (shape : Shape) (arguments : List ValueType) : List RoleRequirement :=
  (if shape.reportsFamilies arguments then familyRequirements shape.operands arguments else []) ++
    if shape.shaped 0 shape.operands arguments then
      fixedRequirements shape.operands arguments ++
        shape.relations.flatMap (Relation.requirement env shape arguments)
    else []

/-! #### Every requirement is part of the association -/

theorem family_sound {env : Environment} {tail : Option (Environment → Nat)} :
    ∀ {operands : List Operand} {arguments : List ValueType},
      operandsMatch env tail operands arguments = true →
      ∀ {requirement : RoleRequirement}, requirement ∈ familyRequirements operands arguments →
        requirement.holds env = true
  | [], _, _, _, member => by simp [familyRequirements] at member
  | _ :: _, [], matched, _, _ => by simp [operandsMatch] at matched
  | operand :: operands, argument :: arguments, matched, requirement, member => by
    simp only [operandsMatch, Bool.and_eq_true] at matched
    have rest := family_sound matched.2 (requirement := requirement)
    cases operand <;> cases argument <;> simp only [familyRequirements, List.mem_cons] at member <;>
      first
      | exact rest member
      | (rcases member with rfl | member
         · simp only [RoleRequirement.holds, beq_iff_eq]
           first
           | exact (family_of_operandMatches matched.1).symm
           | exact (family_of_application matched.1).symm
         · exact rest member)

theorem fixedSlot_sound {env : Environment} {role : String} :
    ∀ {slots : List Slot} {indices : List Index}, slotsMatch slots indices = true →
      ∀ {requirement : RoleRequirement}, requirement ∈ fixedSlotRequirements role slots indices →
        requirement.holds env = true
  | [], _, _, _, member => by simp [fixedSlotRequirements] at member
  | _ :: _, [], matched, _, _ => by simp [slotsMatch] at matched
  | slot :: slots, index :: indices, matched, requirement, member => by
    have rest : slotsMatch slots indices = true := by
      cases slot <;> cases index <;> simp_all [slotsMatch, Bool.and_eq_true]
    cases slot <;> cases index <;> simp only [fixedSlotRequirements, List.mem_cons] at member <;>
      first
      | exact fixedSlot_sound rest member
      | (rcases member with rfl | member
         · simp only [slotsMatch, Bool.and_eq_true, beq_iff_eq] at matched
           simp [RoleRequirement.holds, matched.1]
         · exact fixedSlot_sound rest member)

theorem fixed_sound {env : Environment} {tail : Option (Environment → Nat)} :
    ∀ {operands : List Operand} {arguments : List ValueType},
      operandsMatch env tail operands arguments = true →
      ∀ {requirement : RoleRequirement}, requirement ∈ fixedRequirements operands arguments →
        requirement.holds env = true
  | [], _, _, _, member => by simp [fixedRequirements] at member
  | _ :: _, [], matched, _, _ => by simp [operandsMatch] at matched
  | operand :: operands, argument :: arguments, matched, requirement, member => by
    simp only [operandsMatch, Bool.and_eq_true] at matched
    have rest := fixed_sound matched.2 (requirement := requirement)
    cases operand <;> cases argument <;> simp only [fixedRequirements, List.mem_append] at member <;>
      first
      | exact rest member
      | (rcases member with member | member
         · exact fixedSlot_sound (slots_of_operandMatches matched.1) member
         · exact rest member)

theorem zip_self_mem {α : Type} : ∀ {expected : List α} {pair : α × α},
    pair ∈ expected.zip expected → pair.1 = pair.2
  | [], _, member => by simp at member
  | _ :: rest, pair, member => by
    simp only [List.zip_cons_cons, List.mem_cons] at member
    rcases member with rfl | member
    · rfl
    · exact zip_self_mem member

theorem indicesAt_of_holds {env : Environment} {shape : Shape} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {first second : Nat} {fields : List String}
    (holds : Relation.holds env shape allowed brand arguments (.sameApplication first second fields) = true) :
    indicesAt arguments first = indicesAt arguments second := by
  unfold indicesAt
  cases firstApplication : applicationAt arguments first <;>
    cases secondApplication : applicationAt arguments second <;>
    simp [Relation.holds, firstApplication, secondApplication] at holds <;> simp [holds]

theorem relation_sound {env : Environment} {shape : Shape} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {relation : Relation}
    (holds : relation.holds env shape allowed brand arguments = true) :
    ∀ {requirement : RoleRequirement}, requirement ∈ relation.requirement env shape arguments →
      requirement.holds env = true := by
  intro requirement member
  cases relation with
  | sameRef first second =>
    simp only [Relation.requirement] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      rename_i expected actual _ _ foundExpected foundActual
      simp only [Relation.holds, foundExpected, foundActual] at holds
      simpa [RoleRequirement.holds] using holds
    · simp at member
  | sameApplication first second fields =>
    have same := indicesAt_of_holds holds
    simp only [Relation.requirement] at member
    cases firstRole : (shape.operands[first]?).bind operandRole with
    | none => simp [firstRole] at member
    | some firstRole =>
    cases secondRole : (shape.operands[second]?).bind operandRole with
    | none => simp [firstRole, secondRole] at member
    | some secondRole =>
    cases expected : indicesAt arguments first with
    | none => simp [firstRole, secondRole, expected] at member
    | some expected =>
    cases actual : indicesAt arguments second with
    | none => simp [firstRole, secondRole, expected, actual] at member
    | some actual =>
    rw [expected, actual] at same
    cases same
    simp only [firstRole, secondRole, expected, actual] at member
    split at member
    · obtain ⟨⟨field, x, y⟩, pairMember, rfl⟩ := List.mem_map.mp member
      have equal : x = y := zip_self_mem (List.of_mem_zip pairMember).2
      simp [RoleRequirement.holds, equal]
    · simp at member
  | fixedFrom position lookup reason =>
    simp only [Relation.requirement] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      rename_i actual expected _ _ foundActual foundExpected
      simp only [Relation.holds, foundActual, foundExpected, beq_iff_eq] at holds
      simp [RoleRequirement.holds, holds]
    · simp at member
  | pointDimension position dimension => simp [Relation.requirement] at member
  | refines operand =>
    simp only [Relation.requirement] at member
    split at member
    · rename_i role expected actual ref _ _ foundOperand foundObject
      simp only [Relation.holds, foundOperand, foundObject, decide_eq_true_eq] at holds
      obtain ⟨_, _, marker, domain⟩ := holds
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · simp [RoleRequirement.holds, marker]
      · simpa [RoleRequirement.holds] using domain
    · simp at member
  | freshBrand => simp [Relation.requirement] at member

/-- Every requirement in the role table of a shape is part of the shape's
association contract, so a reported requirement is a genuine failure of that
contract. -/
theorem roles_sound {env : Environment} {shape : Shape} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : Association env shape allowed brand arguments result) :
    ∀ requirement ∈ roles env shape arguments, requirement.holds env = true := by
  obtain ⟨matched, relations, -⟩ := association
  intro requirement member
  simp only [roles, List.mem_append] at member
  rcases member with member | member
  · split at member
    · exact family_sound matched member
    · simp at member
  · split at member
    · simp only [List.mem_append, List.mem_flatMap] at member
      rcases member with member | ⟨relation, relationMember, member⟩
      · exact fixed_sound matched member
      · exact relation_sound (relations relation relationMember) member
    · simp at member

end VastitasKernel.Indexed.Shape

namespace VastitasKernel.Indexed.Source.Diagnostics

/-- The role table of each primitive binding, for the actual operand types:
the requirements of the binding's shape (`Shape.roles`). -/
def roleTable (env : Environment) (binding : PrimitiveBinding) (operands : List ValueType) :
    List RoleRequirement :=
  Shape.roles env binding.contract.shape operands

/-- Every requirement in the role table is part of the association contract, so
a reported requirement is a genuine failure of that contract: `Shape.roles_sound`
at the binding's shape. -/
theorem roleTable_sound {env : Environment} {binding : PrimitiveBinding} {allowed : List ObjectRef}
    {brand : Nat} {operands : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env binding allowed brand operands result) :
    ∀ requirement ∈ roleTable env binding operands, requirement.holds env = true :=
  Shape.roles_sound association

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
