import VastitasOracle.AllocationSafety

namespace VastitasOracle.Safety

open VastitasKernel VastitasKernel.Typing VastitasKernel.Semantics

def SafeTermUnderCalls (functions : List CheckedFunction) (signatures : Signatures)
    (term : Term) : Prop :=
  ∀ ctx world env,
    (∀ id ∈ term.callIds, CallReturns functions signatures id) →
    HasType signatures ctx term → ContextHasType world env ctx →
    (allocatedRefs term).Nodup → WorldFreshFor world (allocatedRefs term) →
    TermOutcome functions world env term

def SafeArgsUnderCalls (functions : List CheckedFunction) (signatures : Signatures)
    (args : List Term) : Prop :=
  ∀ ctx world env,
    (∀ id ∈ args.flatMap Term.callIds, CallReturns functions signatures id) →
    ArgsTyped signatures ctx args → ContextHasType world env ctx →
    (args.flatMap allocatedRefs).Nodup → WorldFreshFor world (args.flatMap allocatedRefs) →
    ArgsOutcome functions world env args

theorem fresh_subset (world : World) (small large : List ObjectRef)
    (subset : ∀ ref ∈ small, ref ∈ large) (fresh : WorldFreshFor world large) :
    WorldFreshFor world small := fun ref member => fresh ref (subset ref member)

theorem sequence_pair (functions : List CheckedFunction) (signatures : Signatures)
    (left right : Term) (leftSafe : SafeTermUnderCalls functions signatures left)
    (rightSafe : SafeTermUnderCalls functions signatures right)
    (ctx : Context) (world : World) (env : Environment)
    (calls : ∀ id ∈ left.callIds ++ right.callIds, CallReturns functions signatures id)
    (leftTyped : HasType signatures ctx left) (rightTyped : HasType signatures ctx right)
    (context : ContextHasType world env ctx)
    (unique : (allocatedRefs left ++ allocatedRefs right).Nodup)
    (fresh : WorldFreshFor world (allocatedRefs left ++ allocatedRefs right)) :
    ∃ after lhs rhs, Eval functions env left lhs ∧ Eval functions env right rhs ∧
      ValueHasResultType after lhs left.resultType ∧ ValueHasResultType after rhs right.resultType ∧
      WorldExtends world after ∧
      WorldUnchangedOutside world after (allocatedRefs left ++ allocatedRefs right) := by
  obtain ⟨uniqueLeft, uniqueRight, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, lhs, leftEval, lhsTyped, leftExtends, leftUnchanged⟩ :=
    leftSafe ctx world env (fun id member => calls id (List.mem_append_left _ member))
      leftTyped context uniqueLeft
      (fresh_subset world _ _ (fun ref member => List.mem_append_left _ member) fresh)
  have freshRight : WorldFreshFor middle (allocatedRefs right) :=
    fresh_after_unchanged world middle _ _ leftUnchanged
      (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
      (fun ref memberRight memberLeft => disjoint ref memberLeft ref memberRight rfl)
  obtain ⟨after, rhs, rightEval, rhsTyped, rightExtends, rightUnchanged⟩ :=
    rightSafe ctx middle env (fun id member => calls id (List.mem_append_right _ member))
      rightTyped (contextHasType_of_worldExtends world middle leftExtends env ctx context)
      uniqueRight freshRight
  exact ⟨after, lhs, rhs, leftEval, rightEval,
    valueHasResultType_of_worldExtends middle after rightExtends lhs _ lhsTyped,
    rhsTyped, worldExtends_trans world middle after leftExtends rightExtends,
    worldUnchangedOutside_trans world middle after _ _ leftUnchanged rightUnchanged⟩

theorem safe_literal (functions : List CheckedFunction) (signatures : Signatures)
    (ty : Ty) (n : Nat) : SafeTermUnderCalls functions signatures (.literal ty n) := by
  intro ctx world env calls typed context unique fresh
  obtain rfl | rfl := typed.2
  · exact ⟨world, .nat n, Eval.nat env n, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world _⟩
  · exact ⟨world, .int (Int.ofNat n), Eval.int env n, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world _⟩

theorem safe_boolean (functions : List CheckedFunction) (signatures : Signatures)
    (b : Bool) : SafeTermUnderCalls functions signatures (.boolean b) := by
  intro ctx world env calls typed context unique fresh
  exact ⟨world, .bool b, Eval.boolean env b, ⟨trivial, trivial⟩,
    worldExtends_refl world, worldUnchangedOutside_refl world _⟩

theorem safe_unit (functions : List CheckedFunction) (signatures : Signatures) :
    SafeTermUnderCalls functions signatures .unit := by
  intro ctx world env calls typed context unique fresh
  exact ⟨world, .unit, Eval.unit env, ⟨trivial, trivial⟩,
    worldExtends_refl world, worldUnchangedOutside_refl world _⟩

theorem safe_variable (functions : List CheckedFunction) (signatures : Signatures)
    (symbol : Nat) (result : ResultType) :
    SafeTermUnderCalls functions signatures (.var symbol result) := by
  intro ctx world env calls typed context unique fresh
  obtain ⟨value, found, valid⟩ := variable_value_exists world env ctx symbol result context typed.2
  exact ⟨world, value, Eval.variable found, valid,
    worldExtends_refl world, worldUnchangedOutside_refl world _⟩

theorem safe_unary (functions : List CheckedFunction) (signatures : Signatures)
    (op : UnaryOp) (arg : Term) (ty : Ty)
    (argSafe : SafeTermUnderCalls functions signatures arg) :
    SafeTermUnderCalls functions signatures (.unary op arg ty) := by
  intro ctx world env calls typed context unique fresh
  obtain ⟨after, operand, evaluated, valid, extension, unchanged⟩ :=
    argSafe ctx world env (by simpa only [Term.callIds] using calls) typed.2.1 context
      (by simpa only [allocatedRefs] using unique) (by simpa only [allocatedRefs] using fresh)
  obtain ⟨value, operated, resultTyped⟩ := unary_total_and_typed after op arg.ty ty operand
    typed.2.2 valid.1
  exact ⟨after, value, Eval.unary evaluated operated, ⟨resultTyped, trivial⟩, extension,
    by simpa only [allocatedRefs] using unchanged⟩

theorem safe_binary (functions : List CheckedFunction) (signatures : Signatures)
    (op : BinaryOp) (left right : Term) (ty : Ty)
    (leftSafe : SafeTermUnderCalls functions signatures left)
    (rightSafe : SafeTermUnderCalls functions signatures right) :
    SafeTermUnderCalls functions signatures (.binary op left right ty) := by
  intro ctx world env calls typed context unique fresh
  obtain ⟨after, lhs, rhs, leftEval, rightEval, lhsTyped, rhsTyped, extension, unchanged⟩ :=
    sequence_pair functions signatures left right leftSafe rightSafe ctx world env
      (by simpa only [Term.callIds] using calls) typed.2.1 typed.2.2.1 context
      (by simpa only [allocatedRefs] using unique) (by simpa only [allocatedRefs] using fresh)
  obtain ⟨value, operated, resultTyped⟩ :=
    binary_total_and_typed after op left.ty right.ty ty lhs rhs typed.2.2.2 lhsTyped.1 rhsTyped.1
  exact ⟨after, value, Eval.binary leftEval rightEval operated, ⟨resultTyped, trivial⟩,
    extension, by simpa only [allocatedRefs] using unchanged⟩

theorem safe_pack (functions : List CheckedFunction) (signatures : Signatures)
    (base : BaseKind) (scheme point : Term)
    (schemeSafe : SafeTermUnderCalls functions signatures scheme)
    (pointSafe : SafeTermUnderCalls functions signatures point) :
    SafeTermUnderCalls functions signatures (.pack base scheme point) := by
  intro ctx world env calls typed context unique fresh
  obtain ⟨after, objectValue, pointValue, objectEval, pointEval,
    objectTyped, pointTyped, extension, unchanged⟩ :=
    sequence_pair functions signatures scheme point schemeSafe pointSafe ctx world env
      (by simpa only [Term.callIds] using calls) typed.2.1 typed.2.2.1 context
      (by simpa only [allocatedRefs] using unique) (by simpa only [allocatedRefs] using fresh)
  have schemeTy := typed.2.2.2.1
  have rule := typed.2.2.2.2
  cases refEq : scheme.resultType.objectRef with
  | none => simp [refEq] at rule
  | some ref =>
      simp only [refEq] at rule
      obtain ⟨refBase, pointTy⟩ := rule
      have known := objectTyped.2
      rw [refEq] at known
      obtain ⟨object, rfl, denotes⟩ := known
      have pTyped := pointTyped.1
      change ValueHasType after pointValue point.ty at pTyped
      rw [pointTy] at pTyped
      obtain ⟨p, rfl⟩ := point_value after pointValue _ _ pTyped
      have packaged := package_has_type after ref object p denotes (by simpa [refBase] using pTyped)
      exact ⟨after, _, Eval.pack objectEval pointEval,
        ⟨by simpa [refBase, Term.resultType] using packaged, trivial⟩, extension,
        by simpa only [allocatedRefs] using unchanged⟩

theorem safe_args_nil (functions : List CheckedFunction) (signatures : Signatures) :
    SafeArgsUnderCalls functions signatures [] := by
  intro ctx world env calls typed context unique fresh
  exact ⟨world, [], EvalArgs.nil env, trivial,
    worldExtends_refl world, worldUnchangedOutside_refl world _⟩

theorem safe_args_cons (functions : List CheckedFunction) (signatures : Signatures)
    (head : Term) (tail : List Term) (headSafe : SafeTermUnderCalls functions signatures head)
    (tailSafe : SafeArgsUnderCalls functions signatures tail) :
    SafeArgsUnderCalls functions signatures (head :: tail) := by
  intro ctx world env calls typed context unique fresh
  simp only [List.flatMap_cons] at calls unique fresh
  obtain ⟨headUnique, tailUnique, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, value, headEval, headTyped, headExtension, headUnchanged⟩ :=
    headSafe ctx world env (fun id member => calls id (List.mem_append_left _ member))
      typed.1 context headUnique
      (fresh_subset world _ _ (fun ref member => List.mem_append_left _ member) fresh)
  have tailFresh := fresh_after_unchanged world middle _ _ headUnchanged
    (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
    (fun ref inTail inHead => disjoint ref inHead ref inTail rfl)
  obtain ⟨after, values, tailEval, tailTyped, tailExtension, tailUnchanged⟩ :=
    tailSafe ctx middle env (fun id member => calls id (List.mem_append_right _ member))
      typed.2 (contextHasType_of_worldExtends world middle headExtension env ctx context)
      tailUnique tailFresh
  exact ⟨after, value :: values, EvalArgs.cons headEval tailEval,
    ⟨valueHasResultType_of_worldExtends middle after tailExtension value _ headTyped, tailTyped⟩,
    worldExtends_trans world middle after headExtension tailExtension,
    by simpa only [List.flatMap_cons] using
      worldUnchangedOutside_trans world middle after _ _ headUnchanged tailUnchanged⟩

theorem safe_builtin (functions : List CheckedFunction) (signatures : Signatures)
    (op : BuiltinOp) (args : List Term) (result : ResultType)
    (argsSafe : SafeArgsUnderCalls functions signatures args) :
    SafeTermUnderCalls functions signatures (.builtin op args result) := by
  intro ctx world env calls typed context unique fresh
  have allocations : allocatedRefs (.builtin op args result) =
      args.flatMap allocatedRefs ++ builtinAllocations op result := by
    cases op <;> simp [allocatedRefs, builtinAllocations]
  rw [allocations] at unique fresh
  obtain ⟨argsUnique, _, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, values, argsEval, argsTyped, argsExtension, argsUnchanged⟩ :=
    argsSafe ctx world env (by simpa only [Term.callIds] using calls)
      typed.2.1 context argsUnique
      (fresh_subset world _ _ (fun ref member => List.mem_append_left _ member) fresh)
  have resultFresh := fresh_after_unchanged world middle _ _ argsUnchanged
    (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
    (fun ref inResult inArgs => disjoint ref inArgs ref inResult rfl)
  obtain ⟨after, value, operated, resultTyped, resultExtension, resultUnchanged⟩ :=
    builtin_total_and_typed middle op _ result values typed.2.2 argsTyped resultFresh
  refine ⟨after, value, Eval.builtin argsEval operated, resultTyped,
    worldExtends_trans world middle after argsExtension resultExtension, ?_⟩
  rw [allocations]
  exact worldUnchangedOutside_trans world middle after _ _ argsUnchanged resultUnchanged

theorem safe_call (functions : List CheckedFunction) (signatures : Signatures)
    (id : Nat) (args : List Term) (substitution : List (ObjectRef × ObjectRef))
    (result : ResultType) (argsSafe : SafeArgsUnderCalls functions signatures args) :
    SafeTermUnderCalls functions signatures (.call id args substitution result) := by
  intro ctx world env calls typed context unique fresh
  simp only [allocatedRefs] at unique fresh
  obtain ⟨argsUnique, _, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, values, argsEval, argsTyped, argsExtension, argsUnchanged⟩ :=
    argsSafe ctx world env (fun called member => calls called (by simp [Term.callIds, member]))
      typed.2.1 context argsUnique
      (fresh_subset world _ _ (fun ref member => List.mem_append_left _ member) fresh)
  have resultFresh := fresh_after_unchanged world middle _ _ argsUnchanged
    (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
    (fun ref inResult inArgs => disjoint ref inArgs ref inResult rfl)
  obtain ⟨function, argEnv, after, value, found, bindings, evaluated,
    resultTyped, resultExtension, resultUnchanged⟩ :=
    calls id (by simp [Term.callIds]) _ substitution result middle values typed.2.2 argsTyped resultFresh
  exact ⟨after, value, Eval.call found argsEval bindings evaluated, resultTyped,
    worldExtends_trans world middle after argsExtension resultExtension,
    by simpa only [allocatedRefs] using
      worldUnchangedOutside_trans world middle after _ _ argsUnchanged resultUnchanged⟩

theorem safe_let (functions : List CheckedFunction) (signatures : Signatures)
    (symbol : Nat) (value body : Term)
    (valueSafe : SafeTermUnderCalls functions signatures value)
    (bodySafe : SafeTermUnderCalls functions signatures body) :
    SafeTermUnderCalls functions signatures (.letE symbol value body) := by
  intro ctx world env calls typed context unique fresh
  simp only [allocatedRefs] at unique fresh
  simp only [Term.callIds] at calls
  obtain ⟨valueUnique, bodyUnique, disjoint⟩ := List.nodup_append.mp unique
  obtain ⟨middle, bound, valueEval, valueTyped, valueExtension, valueUnchanged⟩ :=
    valueSafe ctx world env (fun id member => calls id (List.mem_append_left _ member))
      typed.2.1 context valueUnique
      (fresh_subset world _ _ (fun ref member => List.mem_append_left _ member) fresh)
  have bodyFresh := fresh_after_unchanged world middle _ _ valueUnchanged
    (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
    (fun ref inBody inValue => disjoint ref inValue ref inBody rfl)
  have extendedContext := context_bindValue middle env ctx symbol value.resultType bound
    (contextHasType_of_worldExtends world middle valueExtension env ctx context)
    typed.2.2.1 valueTyped
  obtain ⟨after, result, bodyEval, resultTyped, bodyExtension, bodyUnchanged⟩ :=
    bodySafe (⟨symbol, value.resultType⟩ :: ctx) middle (bindValue env symbol bound)
      (fun id member => calls id (List.mem_append_right _ member))
      typed.2.2.2 extendedContext bodyUnique bodyFresh
  exact ⟨after, result, Eval.letE valueEval bodyEval, resultTyped,
    worldExtends_trans world middle after valueExtension bodyExtension,
    by simpa only [allocatedRefs] using
      worldUnchangedOutside_trans world middle after _ _ valueUnchanged bodyUnchanged⟩

theorem safe_branch (functions : List CheckedFunction) (signatures : Signatures)
    (condition yes no : Term) (result : ResultType)
    (conditionSafe : SafeTermUnderCalls functions signatures condition)
    (yesSafe : SafeTermUnderCalls functions signatures yes)
    (noSafe : SafeTermUnderCalls functions signatures no) :
    SafeTermUnderCalls functions signatures (.branch condition yes no result) := by
  intro ctx world env calls typed context unique fresh
  let extra := branchAllocations yes.resultType no.resultType result
  have allRefs : allocatedRefs (.branch condition yes no result) =
      ((allocatedRefs condition ++ allocatedRefs yes) ++ allocatedRefs no) ++ extra := by
    simp [allocatedRefs, extra, branchAllocations]
  rw [allRefs] at unique fresh
  obtain ⟨prefixUnique, extraUnique, prefixDisjoint⟩ := List.nodup_append.mp unique
  obtain ⟨conditionYesUnique, noUnique, noDisjoint⟩ := List.nodup_append.mp prefixUnique
  obtain ⟨conditionUnique, yesUnique, yesDisjoint⟩ := List.nodup_append.mp conditionYesUnique
  obtain ⟨middle, conditionValue, conditionEval, conditionTyped,
    conditionExtension, conditionUnchanged⟩ :=
    conditionSafe ctx world env
      (fun id member => calls id (by simp [Term.callIds, member])) typed.2.1 context conditionUnique
      (fresh_subset world _ _ (fun ref member => by simp [member]) fresh)
  have booleanTyped : ValueHasType middle conditionValue .bool := by
    simpa only [← typed.2.2.1, Term.ty] using conditionTyped.1
  obtain ⟨flag, rfl⟩ := bool_value middle conditionValue booleanTyped
  let chosen := if flag then yes else no
  have chosenSafe : SafeTermUnderCalls functions signatures chosen := by
    cases flag <;> simpa [chosen] using (by assumption : SafeTermUnderCalls functions signatures _)
  have chosenTyped : HasType signatures ctx chosen := by
    cases flag <;> simp only [chosen, Bool.false_eq_true, ↓reduceIte]
    · exact typed.2.2.2.2.1
    · exact typed.2.2.2.1
  have chosenUnique : (allocatedRefs chosen).Nodup := by
    cases flag <;> simp only [chosen, Bool.false_eq_true, ↓reduceIte]
    · exact noUnique
    · exact yesUnique
  have chosenInPrefix : ∀ ref ∈ allocatedRefs chosen,
      ref ∈ (allocatedRefs condition ++ allocatedRefs yes) ++ allocatedRefs no := by
    intro ref member
    cases flag <;> simp_all [chosen]
  have chosenDisjoint : ∀ ref ∈ allocatedRefs chosen, ref ∉ allocatedRefs condition := by
    intro ref member inCondition
    cases flag with
    | false =>
        have inNo : ref ∈ allocatedRefs no := by simpa [chosen] using member
        exact noDisjoint ref (List.mem_append_left _ inCondition) ref inNo rfl
    | true =>
        have inYes : ref ∈ allocatedRefs yes := by simpa [chosen] using member
        exact yesDisjoint ref inCondition ref inYes rfl
  have chosenFresh : WorldFreshFor middle (allocatedRefs chosen) :=
    fresh_after_unchanged world middle _ _ conditionUnchanged
      (fresh_subset world _ _
        (fun ref member => List.mem_append_left _ (chosenInPrefix ref member)) fresh)
      chosenDisjoint
  obtain ⟨selectedWorld, value, selectedEval, valueTyped, selectedExtension, selectedUnchanged⟩ :=
    chosenSafe ctx middle env
      (fun id member => calls id (by cases flag <;> simp_all [chosen, Term.callIds]))
      chosenTyped (contextHasType_of_worldExtends world middle conditionExtension env ctx context)
      chosenUnique chosenFresh
  have prefixUnchanged := worldUnchangedOutside_trans world middle selectedWorld _ _
    conditionUnchanged selectedUnchanged
  have extraFresh : WorldFreshFor selectedWorld extra :=
    fresh_after_unchanged world selectedWorld _ _ prefixUnchanged
      (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
      (by
        intro ref inExtra inChanged
        obtain inCondition | inChosen := List.mem_append.mp inChanged
        · exact prefixDisjoint ref (by simp [inCondition]) ref inExtra rfl
        · exact prefixDisjoint ref (chosenInPrefix ref inChosen) ref inExtra rfl)
  obtain ⟨after, resultTyped, resultExtension, resultUnchanged⟩ :=
    branch_result_typed selectedWorld yes.resultType no.resultType result chosen.resultType value
      typed.2.2.2.2.2
      (hasType_resultWellFormed signatures ctx yes typed.2.2.2.1)
      (hasType_resultWellFormed signatures ctx no typed.2.2.2.2.1)
      (by cases flag <;> simp [chosen]) valueTyped extraFresh
  have fullEval : Eval functions env (.branch condition yes no result) value := by
    cases flag with
    | false => exact Eval.branchFalse conditionEval (by simpa [chosen] using selectedEval)
    | true => exact Eval.branchTrue conditionEval (by simpa [chosen] using selectedEval)
  refine ⟨after, value, fullEval, resultTyped,
    worldExtends_trans world selectedWorld after
      (worldExtends_trans world middle selectedWorld conditionExtension selectedExtension)
      resultExtension, ?_⟩
  apply worldUnchangedOutside_mono world after
    ((allocatedRefs condition ++ allocatedRefs chosen) ++ extra) _
  · intro ref member
    rw [allRefs]
    obtain inPrefix | inExtra := List.mem_append.mp member
    · obtain inCondition | inChosen := List.mem_append.mp inPrefix
      · simp [inCondition]
      · exact List.mem_append_left _ (chosenInPrefix ref inChosen)
    · exact List.mem_append_right _ inExtra
  · exact worldUnchangedOutside_trans world selectedWorld after _ _ prefixUnchanged resultUnchanged

theorem safe_unpack (functions : List CheckedFunction) (signatures : Signatures)
    (objectSymbol pointSymbol : Nat) (value body : Term)
    (valueSafe : SafeTermUnderCalls functions signatures value)
    (bodySafe : SafeTermUnderCalls functions signatures body) :
    SafeTermUnderCalls functions signatures (.unpack objectSymbol pointSymbol value body) := by
  intro ctx world env calls typed context unique fresh
  have bodyTyped := typed.2.2.2.2.2
  cases valueTy : value.ty <;> simp only [valueTy] at bodyTyped <;> try contradiction
  case pointed base =>
    simp only [allocatedRefs, valueTy] at unique fresh
    simp only [Term.callIds] at calls
    obtain ⟨prefixUnique, bodyUnique, bodyDisjoint⟩ := List.nodup_append.mp unique
    obtain ⟨valueUnique, _, objectDisjoint⟩ := List.nodup_append.mp prefixUnique
    obtain ⟨middle, packageValue, valueEval, packageTyped, valueExtension, valueUnchanged⟩ :=
      valueSafe ctx world env (fun id member => calls id (List.mem_append_left _ member))
        typed.2.1 context valueUnique
        (fresh_subset world _ _ (fun ref member => by simp [member]) fresh)
    have packageType : ValueHasType middle packageValue (.pointed base) := by
      simpa only [← valueTy, Term.ty] using packageTyped.1
    obtain ⟨package, rfl⟩ := pointed_value middle packageValue base packageType
    let opened := bindLocal middle base objectSymbol package.scheme
    have objectFresh : interpretRef middle (.local base objectSymbol) = none := by
      exact (valueUnchanged _ (fun member => objectDisjoint _ member _ (by simp) rfl)).trans
        (fresh _ (by simp))
    have openExtension : WorldExtends middle opened :=
      bindLocal_fresh_extends middle base objectSymbol package.scheme objectFresh
    have openUnchanged : WorldUnchangedOutside middle opened [.local base objectSymbol] :=
      bindLocal_unchangedOutside middle base objectSymbol package.scheme
    have prefixUnchanged := worldUnchangedOutside_trans world middle opened _ _
      valueUnchanged openUnchanged
    have prefixExtension := worldExtends_trans world middle opened valueExtension openExtension
    have bodyFresh : WorldFreshFor opened (allocatedRefs body) :=
      fresh_after_unchanged world opened _ _ prefixUnchanged
        (fresh_subset world _ _ (fun ref member => List.mem_append_right _ member) fresh)
        (fun ref inBody inPrefix => bodyDisjoint ref inPrefix ref inBody rfl)
    let objectResult : ResultType := ⟨.object base, some (.local base objectSymbol)⟩
    let pointResult : ResultType := ⟨unpackedPointType base objectSymbol, none⟩
    have objectTyped : ValueHasResultType opened (.object package.scheme) objectResult :=
      ⟨packageType.1, ⟨package.scheme, rfl,
        unpack_scheme_has_type middle base objectSymbol package packageType⟩⟩
    have pointTyped : ValueHasResultType opened (.point package.point) pointResult :=
      ⟨unpack_point_has_type middle base objectSymbol package packageType, trivial⟩
    have objectsContext := context_bindValue opened env ctx objectSymbol objectResult
      (.object package.scheme)
      (contextHasType_of_worldExtends world opened prefixExtension env ctx context)
      typed.2.2.2.1 objectTyped
    have different : objectSymbol ≠ pointSymbol := typed.2.2.1
    have pointFresh : lookupBinding (⟨objectSymbol, objectResult⟩ :: ctx) pointSymbol = none := by
      simpa [lookupBinding, List.find?_cons, different] using typed.2.2.2.2.1
    have openedContext := context_bindValue opened
      (bindValue env objectSymbol (.object package.scheme)) (⟨objectSymbol, objectResult⟩ :: ctx)
      pointSymbol pointResult (.point package.point) objectsContext pointFresh pointTyped
    obtain ⟨after, result, bodyEval, resultTyped, bodyExtension, bodyUnchanged⟩ :=
      bodySafe (⟨pointSymbol, pointResult⟩ :: ⟨objectSymbol, objectResult⟩ :: ctx) opened
        (bindValue (bindValue env objectSymbol (.object package.scheme)) pointSymbol (.point package.point))
        (fun id member => calls id (List.mem_append_right _ member))
        bodyTyped openedContext bodyUnique bodyFresh
    exact ⟨after, result, Eval.unpack valueEval bodyEval, resultTyped,
      worldExtends_trans world opened after prefixExtension bodyExtension,
      by simpa only [allocatedRefs, valueTy] using
        worldUnchangedOutside_trans world opened after _ _ prefixUnchanged bodyUnchanged⟩

theorem safe_term_under_calls (functions : List CheckedFunction) (signatures : Signatures)
    (term : Term) : SafeTermUnderCalls functions signatures term :=
  Term.rec
    (motive_1 := SafeTermUnderCalls functions signatures)
    (motive_2 := SafeArgsUnderCalls functions signatures)
    (safe_literal functions signatures)
    (safe_boolean functions signatures)
    (safe_unit functions signatures)
    (safe_variable functions signatures)
    (safe_call functions signatures)
    (safe_builtin functions signatures)
    (safe_unary functions signatures)
    (safe_binary functions signatures)
    (safe_branch functions signatures)
    (safe_pack functions signatures)
    (safe_let functions signatures)
    (safe_unpack functions signatures)
    (safe_args_nil functions signatures)
    (safe_args_cons functions signatures)
    term

/-- Every well-typed term has a finite, type-preserving evaluation when its
non-recursive callees satisfy their typed contracts. No evaluator execution or
successful checker result is used as the definition of the typing judgment. -/
theorem evaluation_total_and_typed (functions : List CheckedFunction) (signatures : Signatures)
    (ctx : Context) (world : World) (env : Environment) (term : Term)
    (calls : ∀ id ∈ term.callIds, CallReturns functions signatures id)
    (typed : HasType signatures ctx term) (context : ContextHasType world env ctx)
    (unique : (allocatedRefs term).Nodup) (fresh : WorldFreshFor world (allocatedRefs term)) :
    TermOutcome functions world env term :=
  safe_term_under_calls functions signatures term ctx world env calls typed context unique fresh

end VastitasOracle.Safety
