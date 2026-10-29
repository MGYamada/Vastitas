import VastitasOracle.IndexedWorld
import VastitasOracle.IndexedEvaluation

/-! Semantic value/context lemmas used by whole-term evaluation. Every operation
and annotation is from the actual indexed Core and its independent typing rules. -/
namespace VastitasOracle.IndexedValueSafety
open VastitasKernel (UnaryOp BinaryOp PairElem)
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedWorld

def ResultsHaveTypes (env : Declarations) (world : World) : List Value → List Result → Prop
  | [], [] => True
  | value :: values, result :: results =>
    ValueHasResult env world value result ∧ ResultsHaveTypes env world values results
  | _, _ => False

theorem results_extends {env : Declarations} {before after : World} {values : List Value} {results : List Result}
    (extension : WorldExtends before after) (typed : ResultsHaveTypes env before values results) :
    ResultsHaveTypes env after values results := by
  induction values generalizing results with
  | nil => cases results <;> exact typed
  | cons value values ih =>
    cases results with
    | nil => contradiction
    | cons result results => exact ⟨result_of_worldExtends extension typed.1, ih typed.2⟩

theorem results_length {env : Declarations} {world : World} {values : List Value} {results : List Result}
    (typed : ResultsHaveTypes env world values results) : values.length = results.length := by
  induction values generalizing results with
  | nil => cases results <;> simp_all [ResultsHaveTypes]
  | cons value values ih =>
    cases results with
    | nil => contradiction
    | cons result results => exact congrArg Nat.succ (ih typed.2)

theorem result_without_reference {env : Declarations} {world : World} {value : Value} {result : Result}
    (valid : result.Valid env) (notObject : ∀ type, result.type ≠ .object type)
    (typed : ValueHasType env world value result.type) : ValueHasResult env world value result := by
  refine ⟨typed, ?_⟩
  cases result with
  | mk type reference =>
    cases type <;> cases reference <;> simp_all [Result.Valid, ValueHasRef]

theorem unary_total {env : Declarations} {world : World} {operator : UnaryOp}
    {argument result : DataType} {value : Value}
    (rule : UnaryTyping operator argument result) (typed : ValueHasType env world value argument) :
    ∃ output, evalUnary operator value = some output ∧ ValueHasType env world output result := by
  cases operator <;> obtain ⟨rfl, rfl⟩ := rule <;>
    cases value <;> simp_all [ValueHasType, evalUnary]

theorem binary_total {env : Declarations} {world : World} {operator : BinaryOp}
    {left right result : DataType} {lhs rhs : Value}
    (rule : BinaryTyping operator left right result)
    (leftTyped : ValueHasType env world lhs left) (rightTyped : ValueHasType env world rhs right) :
    ∃ output, evalBinary operator lhs rhs = some output ∧ ValueHasType env world output result := by
  obtain ⟨same, rule⟩ := rule
  subst right
  cases operator <;> dsimp only at rule
  all_goals rcases rule with ⟨choice, rfl⟩
  all_goals first
    | obtain rfl | rfl | rfl | rfl := choice
    | obtain rfl | rfl := choice
    | subst left
  all_goals cases lhs <;> cases rhs <;>
    simp_all [ValueHasType, evalBinary, evalNatBinary, evalIntBinary]

theorem lookup_value {env : Declarations} {world : World} {values : Values} {ctx : Context}
    {symbol : Nat} {result : Result} (context : ContextHasType env world values ctx)
    (found : lookup ctx symbol = some result) :
    ∃ value, values symbol = some value ∧ ValueHasResult env world value result := by
  unfold Typing.lookup at found
  cases binding : ctx.find? (fun parameter => parameter.symbol == symbol) with
  | none => simp [binding] at found
  | some parameter =>
    have same : parameter.symbol = symbol := eq_of_beq
      (List.find?_some (p := fun parameter : Core.Parameter => parameter.symbol == symbol) binding)
    have resultEq : parameter.result = result := by simpa [binding] using found
    obtain ⟨value, present, typed⟩ := context parameter (List.mem_of_find?_eq_some binding)
    exact ⟨value, same ▸ present, resultEq ▸ typed⟩

theorem lookup_absent {ctx : Context} {symbol : Nat} (absent : lookup ctx symbol = none) :
    ∀ parameter ∈ ctx, parameter.symbol ≠ symbol := by
  unfold Typing.lookup at absent
  have absent' : ctx.find? (fun parameter => parameter.symbol == symbol) = none :=
    Option.map_eq_none_iff.mp absent
  intro parameter member equal
  have failed := List.find?_eq_none.mp absent' parameter member
  simp [equal] at failed

theorem context_bind {env : Declarations} {world : World} {values : Values} {ctx : Context}
    {symbol : Nat} {value : Value} {result : Result}
    (context : ContextHasType env world values ctx) (absent : lookup ctx symbol = none)
    (typed : ValueHasResult env world value result) :
    ContextHasType env world (bindValue values symbol value) (⟨symbol, result⟩ :: ctx) := by
  intro parameter member
  rcases List.mem_cons.mp member with equal | member
  · subst parameter
    exact ⟨value, by simp [bindValue], typed⟩
  · obtain ⟨old, found, valid⟩ := context parameter member
    exact ⟨old, by simpa [bindValue, lookup_absent absent parameter member] using found, valid⟩

theorem local_result_total {env : Declarations} {world : World} {value : Value} {type : ObjectType}
    {result : Result} (rule : LocalResult type result) (typed : ValueHasType env world value (.object type))
    (fresh : WorldFreshFor world (resultSerials result)) :
    ∃ after, ValueHasResult env after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after (resultSerials result) := by
  cases result with
  | mk resultType reference =>
    obtain ⟨rfl, rule⟩ := rule
    cases reference with
    | none => contradiction
    | some ref =>
      cases ref with
      | global _ => contradiction
      | «local» actual brand =>
        subst actual
        cases value <;> simp only [ValueHasType] at typed <;> try contradiction
        case object object =>
          refine ⟨bindLocal world brand object, ⟨typed, ?_⟩, ?_, ?_⟩
          · exact ⟨object, rfl, bindLocal_denotes env.indexed world brand object type typed⟩
          · exact bindLocal_fresh_extends world brand object (fresh brand (by simp [resultSerials, localSerial]))
          · simpa [resultSerials, localSerial] using bind_unchanged world brand object

theorem pair_total {env : Declarations} {world : World} {element : PairElem} {left right : Value}
    (leftTyped : ValueHasType env world left (.pure (match (generalizing := false) element with | .nat => .nat | .int => .int)))
    (rightTyped : ValueHasType env world right (.pure (match (generalizing := false) element with | .nat => .nat | .int => .int))) :
    ∃ output, evalPair element left right = some output ∧ ValueHasType env world output (.pure (.pair element)) := by
  cases element <;> cases left <;> cases right
  all_goals first | exact False.elim leftTyped | exact False.elim rightTyped | simp [ValueHasType, evalPair]

theorem project_total {env : Declarations} {world : World} {element : PairElem} {value : Value}
    (first : Bool) (typed : ValueHasType env world value (.pure (.pair element))) :
    ∃ output, evalProject element first value = some output ∧
      ValueHasType env world output (.pure (match (generalizing := false) element with | .nat => .nat | .int => .int)) := by
  cases element <;> cases value
  all_goals first | exact False.elim typed | simp [ValueHasType, evalProject]

theorem result_primitive_iff {env : Declarations} {world : World} {value : Value} {result : Result}
    {output : ValueType} (converted : result.primitiveType? = some output) :
    PrimitiveValueHasType env.indexed world value output ↔ ValueHasResult env world value result := by
  cases result with
  | mk type reference =>
    cases type with
    | pure type =>
      cases type <;> cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
      cases converted
      cases value <;> simp [PrimitiveValueHasType, ValueHasResult, ValueHasType, ValueHasRef]
    | object type =>
      cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
      cases converted
      cases value <;> simp [PrimitiveValueHasType, ValueHasResult, ValueHasType, ValueHasRef]
    | indexed application =>
      cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
      cases converted
      cases value <;> simp [PrimitiveValueHasType, ValueHasResult, ValueHasType, ValueHasRef]
    | package application => simp [Result.primitiveType?] at converted

theorem results_primitive {env : Declarations} {world : World} {values : List Value} {results : List Result}
    {operands : List ValueType} (converted : results.mapM Result.primitiveType? = some operands)
    (typed : ResultsHaveTypes env world values results) :
    PrimitiveValuesHaveTypes env.indexed world values operands := by
  induction results generalizing operands values with
  | nil =>
    cases values <;> simp_all [ResultsHaveTypes, PrimitiveValuesHaveTypes]
  | cons result results ih =>
    cases values with
    | nil => contradiction
    | cons value values =>
      cases head : result.primitiveType? with
      | none => simp [List.mapM_cons, head] at converted
      | some operand =>
        cases tail : results.mapM Result.primitiveType? with
        | none => simp [List.mapM_cons, head, tail] at converted
        | some rest =>
          have equal : operands = operand :: rest := by simpa [List.mapM_cons, head, tail] using converted.symm
          subst operands
          exact ⟨(result_primitive_iff head).mpr typed.1, ih tail typed.2⟩

def primitiveSlots (binding : PrimitiveBinding) (result : Result) : List Nat :=
  match binding with | .descriptor _ => resultSerials result | _ => []

theorem primitive_frame {world : World} {binding : PrimitiveBinding} {result : Result}
    {output : ValueType} {value : Value} (converted : result.primitiveType? = some output) :
    WorldUnchangedOutside world (primitiveWorld world binding output value) (primitiveSlots binding result) := by
  cases binding <;> try exact unchanged_refl _ _
  case descriptor implementation =>
    cases result with
    | mk type reference =>
      cases type with
      | pure type =>
        cases type <;> cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
        cases converted
        exact unchanged_refl _ _
      | object type =>
        cases reference with
        | none => contradiction
        | some ref =>
          cases converted
          cases ref with
          | global _ => exact unchanged_refl _ _
          | «local» actual brand =>
            cases value <;> try exact unchanged_refl _ _
            case object object => simpa [primitiveSlots, resultSerials, localSerial, primitiveWorld] using bind_unchanged world brand object
      | indexed application =>
        cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
        cases converted
        exact unchanged_refl _ _
      | package _ => contradiction

theorem unary_not_object {operator : UnaryOp} {argument result : DataType}
    (rule : UnaryTyping operator argument result) : ∀ type, result ≠ .object type := by
  intro type equal
  rw [equal] at rule
  cases operator <;> simp [UnaryTyping] at rule

theorem binary_not_object {operator : BinaryOp} {left right result : DataType}
    (rule : BinaryTyping operator left right result) : ∀ type, result ≠ .object type := by
  intro type equal
  rw [equal] at rule
  cases operator <;> simp_all [BinaryTyping]
  all_goals rcases rule.2.1 with h | h <;> simp_all

theorem descriptor_serial {result : Result} {type : ObjectType} {brand : Nat}
    (converted : result.primitiveType? = some (.object type (.local type brand))) :
    resultSerials result = [brand] ∧ primitiveBrand result = brand := by
  cases result with
  | mk data reference =>
    cases data with
    | pure data => cases data <;> cases reference <;> simp [Result.primitiveType?] at converted
    | object actual =>
      cases reference <;> simp only [Result.primitiveType?] at converted <;> try contradiction
      cases converted
      simp [resultSerials, localSerial, primitiveBrand]
    | indexed _ => cases reference <;> simp [Result.primitiveType?] at converted
    | package _ => contradiction

theorem primitive_fresh {env : Declarations} {world : World} {binding : PrimitiveBinding}
    {allowed : List ObjectRef} {operands : List ValueType} {output : ValueType} {result : Result}
    (converted : result.primitiveType? = some output)
    (rule : PrimitiveTyped env.indexed binding allowed (primitiveBrand result) operands output)
    (fresh : WorldFreshFor world (primitiveSlots binding result)) :
    PrimitiveFresh binding world (primitiveBrand result) := by
  cases binding <;> try trivial
  case descriptor implementation =>
    have association := rule.association
    unfold PrimitiveAssociation at association
    split at association <;> try contradiction
    · obtain ⟨type, _, _, rfl⟩ := association
      exact fresh _ (by simp [primitiveSlots, (descriptor_serial converted).1])

def branchSlots (yes no result : Result) : List Nat :=
  if yes.reference = no.reference then [] else resultSerials result

theorem branch_result {env : Declarations} {world : World} {value : Value}
    {yes no result : Result} (choice : Bool) (rule : BranchTyping yes no result)
    (typed : ValueHasResult env world value (if choice then yes else no))
    (fresh : WorldFreshFor world (branchSlots yes no result)) :
    ∃ after, ValueHasResult env after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after (branchSlots yes no result) := by
  have valueTyped : ValueHasType env world value yes.type := by
    cases choice <;> simpa only [Bool.false_eq_true, ↓reduceIte, rule.1] using typed.1
  have resultTyped : ValueHasType env world value result.type := rule.2.1 ▸ valueTyped
  have association := rule.2.2
  cases type : yes.type with
  | object objectType =>
    rw [type] at association valueTyped
    by_cases same : yes.reference = no.reference
    · have refEq : result.reference = yes.reference := by simpa only [same, ↓reduceIte] using association
      refine ⟨world, ⟨resultTyped, ?_⟩, worldExtends_refl world, unchanged_refl world _⟩
      cases choice <;> simpa only [Bool.false_eq_true, ↓reduceIte, refEq, same] using typed.2
    · have localRule : LocalResult objectType result := by simpa only [same, ↓reduceIte] using association
      simpa only [branchSlots, same, ↓reduceIte] using local_result_total localRule valueTyped
        (show WorldFreshFor world (resultSerials result) from by simpa only [branchSlots, same, ↓reduceIte] using fresh)
  | pure _ | indexed _ | package _ =>
    rw [type] at association
    exact ⟨world, ⟨resultTyped, by simp [ValueHasRef, association]⟩,
      worldExtends_refl world, unchanged_refl world _⟩

theorem results_fields {env : Declarations} {world : World} {values : List Value} {results : List Result}
    {applications : List Application} (converted : indexedFields results = some applications)
    (typed : ResultsHaveTypes env world values results) :
    ∃ fields, values = fields.map Value.indexed ∧ FieldsHaveTypes env.indexed world fields applications := by
  induction results generalizing applications values with
  | nil =>
    cases values <;> simp_all [indexedFields, ResultsHaveTypes, FieldsHaveTypes]
  | cons result results ih =>
    cases values with
    | nil => contradiction
    | cons value values =>
      cases result with
      | mk type reference =>
        cases type <;> cases reference <;> simp only [indexedFields, List.mapM_cons] at converted <;> try contradiction
        case indexed.none application =>
          cases rest : indexedFields results with
          | none => simp [indexedFields] at rest; simp [rest] at converted
          | some applications' =>
            have restEq := rest
            unfold indexedFields at restEq
            have equal : applications = application :: applications' := by
              simpa [restEq] using converted.symm
            subst applications
            obtain ⟨fields, equal, fieldsTyped⟩ := ih rest typed.2
            have valueTyped := typed.1.1
            cases value <;> try exact False.elim valueTyped
            case indexed field => exact ⟨field :: fields, by simp [equal], valueTyped, fieldsTyped⟩

theorem fields_length {env : Environment} {world : World} {fields : List IndexedValue}
    {applications : List Application} (typed : FieldsHaveTypes env world fields applications) :
    fields.length = applications.length := by
  induction fields generalizing applications with
  | nil => cases applications <;> simp_all [FieldsHaveTypes]
  | cons field fields ih =>
    cases applications with
    | nil => contradiction
    | cons application applications => exact congrArg Nat.succ (ih typed.2)

theorem bind_fields_context {env : Declarations} {world : World} {values : Values} {ctx : Context}
    {symbols : List Nat} {fields : List IndexedValue} {applications : List Application}
    (context : ContextHasType env world values ctx) (unique : symbols.Nodup)
    (absent : ∀ symbol ∈ symbols, lookup ctx symbol = none)
    (lengths : symbols.length = applications.length) (typed : FieldsHaveTypes env.indexed world fields applications) :
    ∃ opened, bindFields values symbols fields = some opened ∧
      ContextHasType env world opened
        ((symbols.zip applications).map (fun (symbol, app) => ⟨symbol, ⟨.indexed app, none⟩⟩) ++ ctx) := by
  induction symbols generalizing ctx values fields applications with
  | nil =>
    cases applications <;> try contradiction
    cases fields <;> try contradiction
    exact ⟨values, rfl, context⟩
  | cons symbol symbols ih =>
    cases applications with
    | nil => contradiction
    | cons application applications =>
      cases fields with
      | nil => contradiction
      | cons field fields =>
        have headContext := context_bind context (absent symbol (List.mem_cons_self))
          (show ValueHasResult env world (.indexed field) ⟨.indexed application, none⟩ from ⟨typed.1, trivial⟩)
        have tailAbsent : ∀ other ∈ symbols,
            lookup (⟨symbol, ⟨.indexed application, none⟩⟩ :: ctx) other = none := by
          intro other member
          have different : symbol ≠ other := fun equal => (List.nodup_cons.mp unique).1 (equal ▸ member)
          simpa only [Typing.lookup, List.find?_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true,
            ↓reduceIte] using absent other (List.mem_cons_of_mem _ member)
        obtain ⟨opened, bound, openedTyped⟩ := ih headContext (List.nodup_cons.mp unique).2 tailAbsent
          (Nat.succ.inj lengths) typed.2
        refine ⟨opened, bound, ?_⟩
        intro parameter member
        simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.mem_cons] at member
        apply openedTyped parameter
        rcases member with equal | member
        · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl equal))
        · rcases List.mem_append.mp member with inFields | inContext
          · exact List.mem_append_left _ inFields
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ inContext)

end VastitasOracle.IndexedValueSafety
