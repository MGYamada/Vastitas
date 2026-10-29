import VastitasOracle.IndexedValueSafety

/-! Whole-term preservation follows the actual Core syntax. Callee contracts
are discharged separately by induction over the independently checked order. -/
namespace VastitasOracle.IndexedEvaluationSafety
open VastitasKernel (UnaryOp BinaryOp PairElem)
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedWorld
open VastitasOracle.IndexedValueSafety VastitasOracle.IndexedEvaluation

def Called (module : Module) (id : Nat) (arguments : List Value) (value : Value) : Prop :=
  ∃ function activation,
    module.functions.find? (fun function => function.id == id) = some function ∧
    bindArguments function.parameters arguments = some activation ∧
    Evaluates module activation function.body value

def CallReturns (module : Module) (functions : Signatures) (id : Nat) : Prop :=
  ∀ world arguments operands substitution result,
    CallTyping module.declarations functions id arguments substitution result →
    ResultsHaveTypes module.declarations world operands arguments →
    WorldFreshFor world (resultSerials result) →
    ∃ after value, Called module id operands value ∧
      ValueHasResult module.declarations after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after (resultSerials result)

def TermOutcome (module : Module) (world : World) (values : Values) (term : Term) : Prop :=
  ∃ after value, Evaluates module values term value ∧
    ValueHasResult module.declarations after value term.result ∧ WorldExtends world after ∧
    WorldUnchangedOutside world after (allocatedSerials module.declarations term)

def ArgsOutcome (module : Module) (world : World) (values : Values) (terms : List Term) : Prop :=
  ∃ after results, ArgumentsEvaluate module values terms results ∧
    ResultsHaveTypes module.declarations after results (terms.map Term.result) ∧ WorldExtends world after ∧
    WorldUnchangedOutside world after (terms.flatMap (allocatedSerials module.declarations))

def SafeTerm (module : Module) (functions : Signatures) (term : Term) : Prop :=
  ∀ ctx world values, module.declarations.Valid →
    (∀ id ∈ term.callIds, CallReturns module functions id) →
    HasType module.declarations functions ctx term → ContextHasType module.declarations world values ctx →
    (allocatedSerials module.declarations term).Nodup →
    WorldFreshFor world (allocatedSerials module.declarations term) → TermOutcome module world values term

def SafeArgs (module : Module) (functions : Signatures) (terms : List Term) : Prop :=
  ∀ ctx world values, module.declarations.Valid →
    (∀ id ∈ terms.flatMap Term.callIds, CallReturns module functions id) →
    ArgsTyped module.declarations functions ctx terms → ContextHasType module.declarations world values ctx →
    (terms.flatMap (allocatedSerials module.declarations)).Nodup →
    WorldFreshFor world (terms.flatMap (allocatedSerials module.declarations)) → ArgsOutcome module world values terms

theorem sequence_pair {module : Module} {functions : Signatures} {left right : Term}
    (leftSafe : SafeTerm module functions left) (rightSafe : SafeTerm module functions right)
    {ctx : Context} {world : World} {values : Values} (valid : module.declarations.Valid)
    (calls : ∀ id ∈ left.callIds ++ right.callIds, CallReturns module functions id)
    (leftTyped : HasType module.declarations functions ctx left)
    (rightTyped : HasType module.declarations functions ctx right)
    (context : ContextHasType module.declarations world values ctx)
    (unique : (allocatedSerials module.declarations left ++ allocatedSerials module.declarations right).Nodup)
    (fresh : WorldFreshFor world (allocatedSerials module.declarations left ++ allocatedSerials module.declarations right)) :
    ∃ after lhs rhs, Evaluates module values left lhs ∧ Evaluates module values right rhs ∧
      ValueHasResult module.declarations after lhs left.result ∧
      ValueHasResult module.declarations after rhs right.result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after
        (allocatedSerials module.declarations left ++ allocatedSerials module.declarations right) := by
  obtain ⟨uniqueLeft, uniqueRight, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, lhs, lhsEval, lhsType, leftExtends, leftFrame⟩ :=
    leftSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) leftTyped context
      uniqueLeft (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have freshRight := fresh_after leftFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot rightMember leftMember => disjoint slot leftMember slot rightMember rfl)
  obtain ⟨after, rhs, rhsEval, rhsType, rightExtends, rightFrame⟩ :=
    rightSafe ctx middle values valid (fun id member => calls id (List.mem_append_right _ member)) rightTyped
      (context_extends leftExtends context) uniqueRight freshRight
  exact ⟨after, lhs, rhs, lhsEval, rhsEval, result_of_worldExtends rightExtends lhsType, rhsType,
    worldExtends_trans leftExtends rightExtends, unchanged_trans leftFrame rightFrame⟩

theorem safe_args_nil (module : Module) (functions : Signatures) : SafeArgs module functions [] := by
  intro ctx world values valid calls typed context unique fresh
  exact ⟨world, [], arguments_nil module values, trivial, worldExtends_refl world, unchanged_refl world _⟩

theorem safe_args_cons {module : Module} {functions : Signatures} {head : Term} {tail : List Term}
    (headSafe : SafeTerm module functions head) (tailSafe : SafeArgs module functions tail) :
    SafeArgs module functions (head :: tail) := by
  intro ctx world values valid calls typed context unique fresh
  obtain ⟨uniqueHead, uniqueTail, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, headValue, headEval, headType, headExtends, headFrame⟩ :=
    headSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) typed.1 context
      uniqueHead (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have freshTail := fresh_after headFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot tailMember headMember => disjoint slot headMember slot tailMember rfl)
  obtain ⟨after, results, tailEval, tailTypes, tailExtends, tailFrame⟩ :=
    tailSafe ctx middle values valid (fun id member => calls id (List.mem_append_right _ member)) typed.2
      (context_extends headExtends context) uniqueTail freshTail
  exact ⟨after, headValue :: results, arguments_cons headEval tailEval,
    ⟨result_of_worldExtends tailExtends headType, tailTypes⟩,
    worldExtends_trans headExtends tailExtends, unchanged_trans headFrame tailFrame⟩

theorem safe_natural (module : Module) (functions : Signatures) (value : Nat) :
    SafeTerm module functions (.natural value) := by
  intro ctx world values valid calls typed context unique fresh
  exact ⟨world, .natural value, natural module values value, ⟨trivial, trivial⟩,
    worldExtends_refl world, unchanged_refl world _⟩

theorem safe_integer (module : Module) (functions : Signatures) (value : Int) :
    SafeTerm module functions (.integer value) := by
  intro ctx world values valid calls typed context unique fresh
  exact ⟨world, .integer value, integer module values value, ⟨trivial, trivial⟩,
    worldExtends_refl world, unchanged_refl world _⟩

theorem safe_boolean (module : Module) (functions : Signatures) (value : Bool) :
    SafeTerm module functions (.boolean value) := by
  intro ctx world values valid calls typed context unique fresh
  exact ⟨world, .boolean value, boolean module values value, ⟨trivial, trivial⟩,
    worldExtends_refl world, unchanged_refl world _⟩

theorem safe_unit (module : Module) (functions : Signatures) : SafeTerm module functions .unit := by
  intro ctx world values valid calls typed context unique fresh
  exact ⟨world, .unit, unit module values, ⟨trivial, trivial⟩,
    worldExtends_refl world, unchanged_refl world _⟩

theorem safe_variable (module : Module) (functions : Signatures) (symbol : Nat) (result : Result) :
    SafeTerm module functions (.variable symbol result) := by
  intro ctx world values valid calls typed context unique fresh
  obtain ⟨value, found, valueTyped⟩ := lookup_value context typed.2
  exact ⟨world, value, variable_value found, valueTyped, worldExtends_refl world, unchanged_refl world _⟩

theorem safe_unary {module : Module} {functions : Signatures} {operand : Term}
    (operator : UnaryOp) (result : Result) (safe : SafeTerm module functions operand) :
    SafeTerm module functions (.unary operator operand result) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, argument, evaluated, argumentTyped, extension, frame⟩ :=
    safe ctx world values valid calls typed.2.1 context unique fresh
  obtain ⟨value, operated, valueTyped⟩ := unary_total typed.2.2 argumentTyped.1
  exact ⟨after, value, unary evaluated operated,
    result_without_reference typed.1 (unary_not_object typed.2.2) valueTyped, extension, frame⟩

theorem safe_binary {module : Module} {functions : Signatures} {left right : Term}
    (operator : BinaryOp) (result : Result) (leftSafe : SafeTerm module functions left)
    (rightSafe : SafeTerm module functions right) : SafeTerm module functions (.binary operator left right result) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, lhs, rhs, leftEval, rightEval, leftTyped, rightTyped, extension, frame⟩ :=
    sequence_pair leftSafe rightSafe valid calls typed.2.1 typed.2.2.1 context unique fresh
  obtain ⟨value, operated, valueTyped⟩ := binary_total typed.2.2.2 leftTyped.1 rightTyped.1
  exact ⟨after, value, binary leftEval rightEval operated,
    result_without_reference typed.1 (binary_not_object typed.2.2.2) valueTyped, extension, frame⟩

theorem safe_ascribe {module : Module} {functions : Signatures} {operand : Term}
    (annotation : DataType) (safe : SafeTerm module functions operand) :
    SafeTerm module functions (.ascribe annotation operand) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, value, evaluated, valueTyped, extension, frame⟩ :=
    safe ctx world values valid calls typed.2.1 context unique fresh
  exact ⟨after, value, ascribe annotation evaluated,
    ⟨value_compatible typed.2.2 valueTyped.1, valueTyped.2⟩, extension, frame⟩

theorem safe_scope {module : Module} {functions : Signatures} {body : Term}
    (safe : SafeTerm module functions body) : SafeTerm module functions (.scope body) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, value, evaluated, valueTyped, extension, frame⟩ :=
    safe ctx world values valid calls typed.2.1 context unique fresh
  exact ⟨after, value, scope evaluated, valueTyped, extension, frame⟩

theorem safe_pair {module : Module} {functions : Signatures} {left right : Term}
    (element : PairElem) (leftSafe : SafeTerm module functions left)
    (rightSafe : SafeTerm module functions right) : SafeTerm module functions (.pair element left right) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, lhs, rhs, leftEval, rightEval, leftTyped, rightTyped, extension, frame⟩ :=
    sequence_pair leftSafe rightSafe valid calls typed.2.1 typed.2.2.1 context unique fresh
  have leftType := typed.2.2.2.1
  have rightType := typed.2.2.2.2
  have operation : ∃ value, evalPair element lhs rhs = some value ∧
      ValueHasType module.declarations after value (.pure (.pair element)) := by
    cases element
    all_goals
      apply pair_total
      · exact leftType ▸ leftTyped.1
      · rw [← leftType, ← rightType]; exact rightTyped.1
  obtain ⟨value, operated, valueTyped⟩ := operation
  exact ⟨after, value, pair leftEval rightEval operated, ⟨valueTyped, trivial⟩, extension, frame⟩

theorem safe_project {module : Module} {functions : Signatures} {operand : Term}
    (element : PairElem) (first : Bool) (safe : SafeTerm module functions operand) :
    SafeTerm module functions (.project element first operand) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, argument, evaluated, argumentTyped, extension, frame⟩ :=
    safe ctx world values valid calls typed.2.1 context unique fresh
  obtain ⟨value, operated, valueTyped⟩ := project_total first (typed.2.2 ▸ argumentTyped.1)
  refine ⟨after, value, project evaluated operated, ?_, extension, frame⟩
  cases element <;> exact ⟨valueTyped, trivial⟩

theorem safe_natToInt {module : Module} {functions : Signatures} {operand : Term}
    (safe : SafeTerm module functions operand) : SafeTerm module functions (.natToInt operand) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  simp only [TermOutcome, allocatedSerials]
  obtain ⟨after, argument, evaluated, argumentTyped, extension, frame⟩ :=
    safe ctx world values valid calls typed.2.1 context unique fresh
  have naturalType : ValueHasType module.declarations after argument (.pure .nat) := typed.2.2 ▸ argumentTyped.1
  cases argument <;> try exact False.elim naturalType
  case natural value =>
    exact ⟨after, .integer (Int.ofNat value), natToInt evaluated, ⟨trivial, trivial⟩, extension, frame⟩

theorem safe_primitive {module : Module} {functions : Signatures} {arguments : List Term}
    (id : DeclId) (result : Result) (safe : SafeArgs module functions arguments) :
    SafeTerm module functions (.primitive id arguments result) := by
  intro ctx world values valid calls typed context unique fresh
  have rule := typed.2.2
  unfold PrimitiveTyping at rule
  split at rule <;> try contradiction
  rename_i binding operands output found inputConversion outputConversion
  simp only [Term.callIds] at calls
  have allocEq : allocatedSerials module.declarations (.primitive id arguments result) =
      arguments.flatMap (allocatedSerials module.declarations) ++ primitiveSlots binding result := by
    cases binding <;> simp only [allocatedSerials, found, primitiveSlots]
  rw [allocEq] at unique fresh
  obtain ⟨uniqueArgs, _, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, inputs, evaluated, inputTypes, argExtends, argFrame⟩ :=
    safe ctx world values valid calls typed.2.1 context uniqueArgs
      (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have outputFresh := fresh_after argFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot outputMember argMember => disjoint slot argMember slot outputMember rfl)
  obtain ⟨after, value, operated, extension, valueTyped, exactWorld⟩ :=
    primitive_total_and_typed rule (results_primitive inputConversion inputTypes)
      (primitive_fresh outputConversion rule outputFresh)
  subst after
  refine ⟨_, value, primitive found evaluated operated, (result_primitive_iff outputConversion).mp valueTyped,
    worldExtends_trans argExtends extension, ?_⟩
  simpa only [allocEq] using
    unchanged_trans argFrame (primitive_frame outputConversion (value := value))

theorem safe_call {module : Module} {functions : Signatures} {arguments : List Term}
    (id : Nat) (substitution : List (ObjectRef × ObjectRef)) (result : Result)
    (safe : SafeArgs module functions arguments) : SafeTerm module functions (.call id arguments substitution result) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  obtain ⟨uniqueArgs, _, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, inputs, evaluated, inputTypes, argExtends, argFrame⟩ :=
    safe ctx world values valid (fun id member => calls id (List.mem_cons_of_mem _ member)) typed.2.1 context uniqueArgs
      (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have outputFresh := fresh_after argFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot outputMember argMember => disjoint slot argMember slot outputMember rfl)
  obtain ⟨after, value, called, valueTyped, extension, frame⟩ :=
    calls id (List.mem_cons_self) middle _ inputs substitution result typed.2.2 inputTypes outputFresh
  obtain ⟨function, activation, found, bound, bodyEval⟩ := called
  refine ⟨after, value, call found evaluated bound bodyEval, valueTyped,
    worldExtends_trans argExtends extension, ?_⟩
  simpa only [allocatedSerials] using unchanged_trans argFrame frame

theorem safe_let {module : Module} {functions : Signatures} {operand body : Term}
    (symbol : Nat) (operandSafe : SafeTerm module functions operand) (bodySafe : SafeTerm module functions body) :
    SafeTerm module functions (.letE symbol operand body) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  obtain ⟨uniqueOperand, uniqueBody, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, boundValue, operandEval, operandTyped, operandExtends, operandFrame⟩ :=
    operandSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) typed.2.1 context
      uniqueOperand (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have bodyFresh := fresh_after operandFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot bodyMember operandMember => disjoint slot operandMember slot bodyMember rfl)
  obtain ⟨after, value, bodyEval, bodyTyped, bodyExtends, bodyFrame⟩ :=
    bodySafe _ middle (bindValue values symbol boundValue) valid
      (fun id member => calls id (List.mem_append_right _ member)) typed.2.2.2
      (context_bind (context_extends operandExtends context) typed.2.2.1 operandTyped) uniqueBody bodyFresh
  refine ⟨after, value, letE operandEval bodyEval, bodyTyped, worldExtends_trans operandExtends bodyExtends, ?_⟩
  simpa only [allocatedSerials] using unchanged_trans operandFrame bodyFrame

theorem safe_branch {module : Module} {functions : Signatures} {condition yes no : Term}
    (result : Result) (conditionSafe : SafeTerm module functions condition)
    (yesSafe : SafeTerm module functions yes) (noSafe : SafeTerm module functions no) :
    SafeTerm module functions (.branch condition yes no result) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds, List.append_assoc] at calls
  simp only [allocatedSerials, List.append_assoc] at unique fresh
  rw [← List.append_assoc (allocatedSerials module.declarations yes)] at unique fresh
  obtain ⟨conditionUnique, tailUnique, conditionDisjoint⟩ := List.nodup_append.mp unique
  obtain ⟨branchesUnique, _, resultDisjoint⟩ := List.nodup_append.mp tailUnique
  obtain ⟨yesUnique, noUnique, _⟩ := List.nodup_append.mp branchesUnique
  obtain ⟨middle, booleanValue, conditionEval, conditionTyped, conditionExtends, conditionFrame⟩ :=
    conditionSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) typed.2.1 context
      conditionUnique (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have booleanType : ValueHasType module.declarations middle booleanValue (.pure .bool) := typed.2.2.1 ▸ conditionTyped.1
  cases booleanValue <;> try exact False.elim booleanType
  case boolean choice =>
    have tailFresh := fresh_after conditionFrame
      (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
      (fun slot tailMember conditionMember => conditionDisjoint slot conditionMember slot tailMember rfl)
    have chosenSafe : SafeTerm module functions (if choice then yes else no) := by cases choice <;> assumption
    have chosenTyped : HasType module.declarations functions ctx (if choice then yes else no) := by
      cases choice
      · exact typed.2.2.2.2.1
      · exact typed.2.2.2.1
    have chosenUnique : (allocatedSerials module.declarations (if choice then yes else no)).Nodup := by
      cases choice <;> assumption
    have chosenSubset : ∀ slot ∈ allocatedSerials module.declarations (if choice then yes else no),
        slot ∈ allocatedSerials module.declarations yes ++ allocatedSerials module.declarations no := by
      cases choice
      · exact fun _ member => List.mem_append_right _ member
      · exact fun _ member => List.mem_append_left _ member
    have chosenCalls : ∀ id ∈ (if choice then yes else no).callIds, CallReturns module functions id := by
      cases choice
      · exact fun id member => calls id (List.mem_append_right _ (List.mem_append_right _ member))
      · exact fun id member => calls id (List.mem_append_right _ (List.mem_append_left _ member))
    obtain ⟨evaluatedWorld, value, chosenEval, chosenType, chosenExtends, chosenFrame⟩ :=
      chosenSafe ctx middle values valid chosenCalls chosenTyped (context_extends conditionExtends context)
        chosenUnique (fresh_subset (fun slot member => List.mem_append_left _ (chosenSubset slot member)) tailFresh)
    have branchesFrame := unchanged_subset chosenFrame chosenSubset
    have outputFresh := fresh_after branchesFrame
      (fresh_subset (fun _ member => List.mem_append_right _ member) tailFresh)
      (fun slot resultMember branchMember => resultDisjoint slot branchMember slot resultMember rfl)
    have chosenResult : ValueHasResult module.declarations evaluatedWorld value (if choice then yes.result else no.result) := by
      cases choice <;> exact chosenType
    obtain ⟨after, valueTyped, resultExtends, resultFrame⟩ :=
      branch_result choice typed.2.2.2.2.2 chosenResult outputFresh
    refine ⟨after, value, branch conditionEval chosenEval, valueTyped,
      worldExtends_trans conditionExtends (worldExtends_trans chosenExtends resultExtends), ?_⟩
    simpa only [allocatedSerials, branchSlots, List.append_assoc] using
      unchanged_trans conditionFrame (unchanged_trans branchesFrame resultFrame)

theorem safe_pack {module : Module} {functions : Signatures} {witness : Term} {fields : List Term}
    (application : Application) (witnessSafe : SafeTerm module functions witness)
    (fieldsSafe : SafeArgs module functions fields) : SafeTerm module functions (.pack application witness fields) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  have rule := typed.2.2.2
  unfold PackageTyping at rule
  split at rule <;> try contradiction
  rename_i shape reference applications found witnessRef fieldTypes
  obtain ⟨witnessUnique, fieldsUnique, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, witnessValue, witnessEval, witnessTyped, witnessExtends, witnessFrame⟩ :=
    witnessSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) typed.2.1 context
      witnessUnique (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
  have fieldsFresh := fresh_after witnessFrame
    (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
    (fun slot fieldMember witnessMember => disjoint slot witnessMember slot fieldMember rfl)
  obtain ⟨after, fieldValues, fieldsEval, fieldsTyped, fieldsExtends, fieldsFrame⟩ :=
    fieldsSafe ctx middle values valid (fun id member => calls id (List.mem_append_right _ member)) typed.2.2.1
      (context_extends witnessExtends context) fieldsUnique fieldsFresh
  obtain ⟨contents, equal, contentsTyped⟩ := results_fields fieldTypes fieldsTyped
  subst fieldValues
  obtain ⟨object, equal, packageTyped⟩ := IndexedPackageSemantics.core_pack_semantics valid found witnessRef fieldTypes
    typed (result_of_worldExtends fieldsExtends witnessTyped) contentsTyped
  subst witnessValue
  refine ⟨after, .package object contents, pack witnessEval (fields_from_arguments fieldsEval),
    ⟨packageTyped, trivial⟩, worldExtends_trans witnessExtends fieldsExtends, ?_⟩
  simpa only [allocatedSerials] using unchanged_trans witnessFrame fieldsFrame

theorem safe_unpack {module : Module} {functions : Signatures} {package body : Term}
    (witnessSymbol : Nat) (fieldSymbols : List Nat) (packageSafe : SafeTerm module functions package)
    (bodySafe : SafeTerm module functions body) :
    SafeTerm module functions (.unpack witnessSymbol fieldSymbols package body) := by
  intro ctx world values valid calls typed context unique fresh
  simp only [Term.callIds] at calls
  simp only [allocatedSerials] at unique fresh
  have rule := typed.2.2.2.2.2
  cases packageType : package.result.type <;> simp only [packageType] at rule <;> try contradiction
  case package application =>
    cases found : module.declarations.package? application with
    | none => simp [found] at rule
    | some shape =>
      simp only [found] at rule
      obtain ⟨packageUnique, tailUnique, disjoint⟩ := List.nodup_append.mp unique
      obtain ⟨middle, packageValue, packageEval, packageTyped, packageExtends, packageFrame⟩ :=
        packageSafe ctx world values valid (fun id member => calls id (List.mem_append_left _ member)) typed.2.1 context
          packageUnique (fresh_subset (fun _ member => List.mem_append_left _ member) fresh)
      have tailFresh := fresh_after packageFrame
        (fresh_subset (fun _ member => List.mem_append_right _ member) fresh)
        (fun slot tailMember packageMember => disjoint slot packageMember slot tailMember rfl)
      have payloadType : ValueHasType module.declarations middle packageValue (.package application) := packageType ▸ packageTyped.1
      cases packageValue <;> try exact False.elim payloadType
      case package witness fields =>
        obtain ⟨openingExtends, witnessDenotes, fieldsTyped⟩ := IndexedPackageSemantics.core_opening_semantics
          valid packageType found typed packageTyped.1 (tailFresh witnessSymbol (List.mem_cons_self))
        have witnessType : ObjectHasType module.declarations.indexed witness shape.witnessType := by
          obtain ⟨type, same, witnessType⟩ := witnessDenotes.2
          simp only [ObjectRef.type?] at same
          cases same
          exact witnessType
        have witnessContext := context_bind
          (context_extends openingExtends (context_extends packageExtends context))
          (typed.2.2.2.1 witnessSymbol (List.mem_cons_self))
          (show ValueHasResult module.declarations (bindLocal middle witnessSymbol witness) (.object witness)
            ⟨.object shape.witnessType, some (.local shape.witnessType witnessSymbol)⟩ from
              ⟨witnessType, witness, rfl, witnessDenotes⟩)
        have fieldAbsent : ∀ symbol ∈ fieldSymbols,
            lookup (⟨witnessSymbol, ⟨.object shape.witnessType, some (.local shape.witnessType witnessSymbol)⟩⟩ :: ctx) symbol = none := by
          intro symbol member
          have different : witnessSymbol ≠ symbol := fun equal => (List.nodup_cons.mp typed.2.2.1).1 (equal ▸ member)
          simpa only [Typing.lookup, List.find?_cons, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true,
            ↓reduceIte] using typed.2.2.2.1 symbol (List.mem_cons_of_mem _ member)
        obtain ⟨opened, bound, openedTyped⟩ := bind_fields_context witnessContext
          (List.nodup_cons.mp typed.2.2.1).2 fieldAbsent
          (by simpa [PackageShape.instantiate] using rule.1) fieldsTyped
        have openedContextTyped : ContextHasType module.declarations (bindLocal middle witnessSymbol witness) opened
            (openedContext shape witnessSymbol fieldSymbols ++ ctx) := by
          intro parameter member
          simp only [openedContext, List.cons_append, List.mem_cons] at member
          apply openedTyped parameter
          rcases member with equal | member
          · exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl equal))
          · rcases List.mem_append.mp member with fieldMember | contextMember
            · exact List.mem_append_left _ fieldMember
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ contextMember)
        have openingFrame := bind_unchanged middle witnessSymbol witness
        have bodyFresh := fresh_after openingFrame
          (fresh_subset (fun _ member => List.mem_cons_of_mem _ member) tailFresh)
          (fun slot member equal => (List.nodup_cons.mp tailUnique).1
            ((List.mem_singleton.mp equal) ▸ member))
        obtain ⟨after, value, bodyEval, bodyTyped, bodyExtends, bodyFrame⟩ :=
          bodySafe _ _ opened valid (fun id member => calls id (List.mem_append_right _ member)) rule.2.1
            openedContextTyped (List.nodup_cons.mp tailUnique).2 bodyFresh
        refine ⟨after, value, unpack packageEval bound bodyEval, bodyTyped,
          worldExtends_trans packageExtends (worldExtends_trans openingExtends bodyExtends), ?_⟩
        simpa only [allocatedSerials, List.singleton_append] using
          unchanged_trans packageFrame (unchanged_trans openingFrame bodyFrame)

/-- Structural induction over every constructor of the real indexed Core.
The semantic callee contracts remain explicit; this theorem alone does not
discharge them from a checked module's dependency order. -/
theorem safe_term_under_calls (module : Module) (functions : Signatures) (term : Term) :
    SafeTerm module functions term :=
  Term.rec
    (motive_1 := SafeTerm module functions)
    (motive_2 := SafeArgs module functions)
    (safe_natural module functions)
    (safe_integer module functions)
    (safe_boolean module functions)
    (safe_unit module functions)
    (safe_variable module functions)
    (fun operator _ result safe => safe_unary operator result safe)
    (fun operator _ _ result leftSafe rightSafe => safe_binary operator result leftSafe rightSafe)
    (fun element _ _ leftSafe rightSafe => safe_pair element leftSafe rightSafe)
    (fun element first _ safe => safe_project element first safe)
    (fun _ safe => safe_natToInt safe)
    (fun annotation _ safe => safe_ascribe annotation safe)
    (fun id _ result safe => safe_primitive id result safe)
    (fun id _ substitution result safe => safe_call id substitution result safe)
    (fun _ _ _ result conditionSafe yesSafe noSafe => safe_branch result conditionSafe yesSafe noSafe)
    (fun application _ _ witnessSafe fieldsSafe => safe_pack application witnessSafe fieldsSafe)
    (fun witnessSymbol fieldSymbols _ _ packageSafe bodySafe => safe_unpack witnessSymbol fieldSymbols packageSafe bodySafe)
    (fun _ safe => safe_scope safe)
    (fun symbol _ _ operandSafe bodySafe => safe_let symbol operandSafe bodySafe)
    (safe_args_nil module functions)
    (fun _ _ headSafe tailSafe => safe_args_cons headSafe tailSafe)
    term

/-- Accepted typing and fresh audited allocations imply a finite observation
bound and a typed result, provided callees satisfy their semantic contracts.
No successful evaluator execution is assumed. The result holds at every fuel
at least that bound, and preserves all world slots outside the term's audited
allocations. -/
theorem evaluation_total_and_typed {module : Module} {functions : Signatures} {term : Term}
    {ctx : Context} {world : World} {values : Values} (valid : module.declarations.Valid)
    (calls : ∀ id ∈ term.callIds, CallReturns module functions id)
    (typed : HasType module.declarations functions ctx term)
    (context : ContextHasType module.declarations world values ctx)
    (unique : (allocatedSerials module.declarations term).Nodup)
    (fresh : WorldFreshFor world (allocatedSerials module.declarations term)) :
    TermOutcome module world values term :=
  safe_term_under_calls module functions term ctx world values valid calls typed context unique fresh

end VastitasOracle.IndexedEvaluationSafety
