import VastitasKernel.IndexedSourceTypes

/-! The role requirements of a primitive's shape (`Shape.roles`) and their
soundness: every requirement is part of the association contract
(`Shape.roles_sound`). `IndexedSourceDiagnostics.lean` reads the role table of
a rejected call from them. -/
namespace VastitasKernel.Indexed.Source.Diagnostics

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
  /-- The `field` index of the `role` operand must be the frame `expected`
  (Stage 4); `reason` names the operand or declaration that fixes it. -/
  | frame (role field : String) (expected actual : DeclId) (reason : String)
  /-- The index `index` of the primitive, named `name`, must be below
  `dimension`, the dimension of the object of the frame `frame` at the `field`
  index of the `role` operand (Stage 4). -/
  | bound (role field name : String) (frame : DeclId) (index dimension : Nat)
  deriving Repr, Inhabited, DecidableEq

def RoleRequirement.holds (env : Environment) : RoleRequirement → Bool
  | .family _ expected actual => expected == actual
  | .object _ _ expected actual _ => expected == actual
  | .frame _ _ expected actual _ => expected == actual
  | .bound _ _ _ _ index dimension => decide (index < dimension)
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
    | some (.frameVar field) => some (role, field)
    | some (.fixedFrame _ field _) => some (role, field)
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
  | .fixedFrame frame field reason :: slots, .frame actual :: indices =>
      .frame role field frame actual reason :: fixedSlotRequirements role slots indices
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
  | .sameFrame first second =>
    match shape.roleField first, shape.roleField second, frameIndexAt arguments first,
        frameIndexAt arguments second with
    | some (firstRole, firstField), some (secondRole, secondField), some expected, some actual =>
      [.frame secondRole secondField expected actual s!"the {firstRole}'s {firstField}"]
    | _, _, _, _ => []
  | .frameObject frame object reason =>
    match shape.roleField object, frameIndexAt arguments frame, refAt arguments object with
    | some (role, field), some frame, some actual => match frameObject? env frame with
      | some expected => [.object role field (.global expected) actual reason]
      | none => []
    | _, _, _ => []
  | .frameBound position index name =>
    match shape.roleField position, frameIndexAt arguments position with
    | some (role, field), some frame => match frameDimension? env frame with
      | some dimension => [.bound role field name frame index dimension]
      | none => []
    | _, _ => []

/-- The slots of `operand` at which the shape fixes a point's dimension. -/
def pointSlots (shape : Shape) (operand : Nat) : List Nat :=
  shape.relations.filterMap fun
    | .pointDimension position _ => if position.operand == operand then some position.slot else none
    | _ => none

/-- Whether an index list has the pattern of the slots: one frame per frame
slot, one object per other slot, and a global object at the slots of
`points`, since only a global object has a dimension. -/
def slotsShaped (points : List Nat) : Nat → List Slot → List Index → Bool
  | _, [], [] => true
  | slot, .frameVar _ :: slots, .frame _ :: indices => slotsShaped points (slot + 1) slots indices
  | slot, .fixedFrame .. :: slots, .frame _ :: indices => slotsShaped points (slot + 1) slots indices
  | _, .frameVar _ :: _, _ => false
  | _, .fixedFrame .. :: _, _ => false
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
  | sameFrame first second =>
    simp only [Relation.requirement] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      rename_i expected actual _ _ foundExpected foundActual
      simp only [Relation.holds, foundExpected, foundActual] at holds
      simpa [RoleRequirement.holds] using holds
    · simp at member
  | frameObject frame object reason =>
    simp only [Relation.requirement] at member
    split at member
    · rename_i role field found actual _ foundFrame foundActual
      cases foundObject : frameObject? env found with
      | none => simp [foundObject] at member
      | some expected =>
        simp only [foundObject, List.mem_singleton] at member
        subst member
        simp only [Relation.holds, foundFrame, foundActual, foundObject, beq_iff_eq] at holds
        simp [RoleRequirement.holds, holds]
    · simp at member
  | frameBound position index name =>
    simp only [Relation.requirement] at member
    split at member
    · rename_i role field found _ foundFrame
      cases foundDimension : frameDimension? env found with
      | none => simp [foundDimension] at member
      | some dimension =>
        simp only [foundDimension, List.mem_singleton] at member
        subst member
        simp only [Relation.holds, foundFrame, foundDimension, Option.any_some, decide_eq_true_eq] at holds
        simp [RoleRequirement.holds, holds]
    · simp at member
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
