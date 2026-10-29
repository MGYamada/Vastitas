import VastitasOracle.IndexedCallTransport

/-! Activation construction from actual checked parameter/argument contracts. -/
namespace VastitasOracle.IndexedArgumentSafety
open VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics VastitasKernel.Indexed.Core.Typing
open VastitasOracle.IndexedSemantics VastitasOracle.IndexedWorld
open VastitasOracle.IndexedValueSafety VastitasOracle.IndexedCallTransport

theorem parameters_avoid_previous {env : Declarations} {previous parameters : Context}
    (formed : ParametersValid env previous parameters) :
    ∀ parameter ∈ parameters, ∀ old ∈ previous, parameter.symbol ≠ old.symbol := by
  induction parameters generalizing previous with
  | nil => simp
  | cons head tail ih =>
    intro parameter member old oldMember
    rcases List.mem_cons.mp member with equal | member
    · subst parameter
      exact Ne.symm (lookup_absent formed.1 old oldMember)
    · exact ih formed.2.2.2.2 parameter member old (List.mem_cons_of_mem _ oldMember)

theorem parameters_unique {env : Declarations} {previous parameters : Context}
    (formed : ParametersValid env previous parameters) : (parameters.map Core.Parameter.symbol).Nodup := by
  induction parameters generalizing previous with
  | nil => simp
  | cons parameter parameters ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih formed.2.2.2.2⟩
    intro member
    obtain ⟨other, member, equal⟩ := List.mem_map.mp member
    exact parameters_avoid_previous formed.2.2.2.2 other member parameter (List.mem_cons_self) equal

theorem parameter_formed {env : Declarations} {previous parameters : Context} {parameter : Core.Parameter}
    (formed : ParametersValid env previous parameters) (member : parameter ∈ parameters) :
    parameter.result.Valid env ∧
      (match parameter.result.type with
       | .object type => parameter.result.reference = some (.local type parameter.symbol)
       | _ => parameter.result.reference = none) := by
  induction parameters generalizing previous with
  | nil => contradiction
  | cons head tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst parameter; exact ⟨formed.2.1, formed.2.2.2.1⟩
    · exact ih formed.2.2.2.2 member

theorem parameters_refs_into {env : Declarations} {previous parameters : Context} {allowed : List ObjectRef}
    (formed : ParametersValid env previous parameters)
    (previousCovered : ∀ ref ∈ contextRefs previous, ref.Scoped allowed)
    (own : ∀ parameter ∈ parameters, ∀ ref ∈ parameter.result.reference.toList, ref.Scoped allowed) :
    ∀ ref ∈ contextRefs parameters, ref.Scoped allowed := by
  induction parameters generalizing previous with
  | nil => simp [contextRefs]
  | cons parameter parameters ih =>
    have headCovered : ∀ ref ∈ parameter.result.refs, ref.Scoped allowed := by
      intro ref member
      rcases List.mem_append.mp member with reference | typeRef
      · exact own parameter (List.mem_cons_self) ref reference
      · have scope := formed.2.2.1 ref typeRef
        cases ref with
        | global _ => trivial
        | «local» type brand => exact previousCovered (.local type brand) scope
    have extended : ∀ ref ∈ contextRefs (parameter :: previous), ref.Scoped allowed := by
      intro ref member
      rcases List.mem_append.mp member with head | tail
      · exact headCovered ref head
      · exact previousCovered ref tail
    have tailCovered := ih formed.2.2.2.2 extended
      (fun parameter member => own parameter (List.mem_cons_of_mem _ member))
    intro ref member
    rcases List.mem_append.mp member with head | tail
    · exact headCovered ref head
    · exact tailCovered ref tail

theorem parameters_refs_covered {env : Declarations} {parameters : Context}
    (formed : ParametersValid env [] parameters) :
    ∀ ref ∈ contextRefs parameters, ref.Scoped (parameters.flatMap fun parameter => parameter.result.reference.toList) := by
  apply parameters_refs_into formed (by simp [contextRefs])
  intro parameter member ref reference
  cases ref with
  | global _ => trivial
  | «local» type brand => exact List.mem_flatMap.mpr ⟨parameter, member, reference⟩

def ArgumentWitnesses (env : Declarations) (world : World) (activation : Values)
    (parameters : Context) (arguments : List Result) : Prop :=
  ∀ parameter ∈ parameters, ∃ argument value,
    (parameter, argument) ∈ parameters.zip arguments ∧
    activation parameter.symbol = some value ∧ ValueHasResult env world value argument

theorem bind_arguments_typed {env : Declarations} {world : World} {parameters : Context}
    {arguments : List Result} {values : List Value}
    (unique : (parameters.map Core.Parameter.symbol).Nodup)
    (lengths : parameters.length = arguments.length) (typed : ResultsHaveTypes env world values arguments) :
    ∃ activation, bindArguments parameters values = some activation ∧
      ArgumentWitnesses env world activation parameters arguments := by
  induction parameters generalizing arguments values with
  | nil =>
    cases arguments <;> try contradiction
    cases values <;> try contradiction
    exact ⟨fun _ => none, rfl, by simp [ArgumentWitnesses]⟩
  | cons parameter parameters ih =>
    cases arguments with
    | nil => contradiction
    | cons argument arguments =>
      cases values with
      | nil => contradiction
      | cons value values =>
        obtain ⟨activation, bound, witnesses⟩ := ih (List.nodup_cons.mp unique).2 (Nat.succ.inj lengths) typed.2
        refine ⟨bindValue activation parameter.symbol value, by simp [bindArguments, bound], ?_⟩
        intro other member
        rcases List.mem_cons.mp member with equal | member
        · subst other
          exact ⟨argument, value, List.mem_cons_self, by simp [bindValue], typed.1⟩
        · obtain ⟨actual, operand, pairMember, present, operandTyped⟩ := witnesses other member
          have different : other.symbol ≠ parameter.symbol := fun equal =>
            (List.nodup_cons.mp unique).1 (List.mem_map.mpr ⟨other, member, equal⟩)
          exact ⟨actual, operand, List.mem_cons_of_mem _ pairMember,
            by simpa [bindValue, different] using present, operandTyped⟩

def objectWorld (values : Values) : World := fun symbol =>
  match values symbol with | some (.object object) => some object | _ => none

theorem argument_reference_corresponds {env : Declarations} {world : World} {parameters : Context}
    {arguments : List Result} {activation : Values} {substitution : List (ObjectRef × ObjectRef)}
    (formed : ParametersValid env [] parameters)
    (matched : FinalArgumentsMatch env parameters arguments substitution)
    (witnesses : ArgumentWitnesses env world activation parameters arguments)
    {ref : ObjectRef} (member : ref ∈ parameters.flatMap fun parameter => parameter.result.reference.toList) :
    ∃ object, RefDenotes env.indexed (objectWorld activation) ref object ∧
      RefDenotes env.indexed world (renameRef substitution ref) object := by
  obtain ⟨parameter, parameterMember, reference⟩ := List.mem_flatMap.mp member
  have referenceEq : parameter.result.reference = some ref := by simpa using reference
  obtain ⟨argument, value, pairMember, present, typed⟩ := witnesses parameter parameterMember
  have matchedPair := matched.2 (parameter, argument) pairMember
  have parameterFacts := parameter_formed formed parameterMember
  have shape := parameterFacts.2
  cases parameterType : parameter.result.type <;> simp only [parameterType] at shape
  all_goals try { rw [shape] at referenceEq; contradiction }
  case object type =>
    have refEq : ref = .local type parameter.symbol := Option.some.inj (referenceEq.symm.trans shape)
    have association := matchedPair.2
    rw [referenceEq] at association
    cases argumentRef : argument.reference with
    | none => simp [argumentRef] at association
    | some actual =>
      simp only [argumentRef] at association
      have denotes := typed.2
      rw [argumentRef] at denotes
      obtain ⟨object, rfl, actualDenotes⟩ := denotes
      have objectTyped : ObjectHasType env.indexed object type := by
        have upcast := value_compatible matchedPair.1 typed.1
        simpa only [parameterType, DataType.rename, ValueHasType] using upcast
      refine ⟨object, ?_, ?_⟩
      · rw [refEq]
        exact ⟨by simp [interpretRef, objectWorld, present], type, rfl, objectTyped⟩
      · simpa only [association] using actualDenotes

theorem parameter_reference_transport {env : Declarations} {world : World} {parameters : Context}
    {arguments : List Result} {activation : Values} {substitution : List (ObjectRef × ObjectRef)}
    (formed : ParametersValid env [] parameters)
    (matched : FinalArgumentsMatch env parameters arguments substitution)
    (witnesses : ArgumentWitnesses env world activation parameters arguments) :
    ∀ ref ∈ contextRefs parameters, ∀ object,
      RefDenotes env.indexed (objectWorld activation) ref object ↔
        RefDenotes env.indexed world (renameRef substitution ref) object := by
  intro ref member object
  cases ref with
  | global _ => rfl
  | «local» type brand =>
    have own := parameters_refs_covered formed (.local type brand) member
    obtain ⟨common, formalDenotes, actualDenotes⟩ := argument_reference_corresponds formed matched witnesses own
    constructor
    · intro denotes
      have equal := denotes_unique formalDenotes denotes
      exact equal ▸ actualDenotes
    · intro denotes
      have equal := denotes_unique actualDenotes denotes
      exact equal ▸ formalDenotes

/-- The actual argument binder creates a typed activation. The correspondence
retains runtime endpoints even when an actual object domain refines its formal
parameter domain. Neither equal descriptors nor equal dimensions supply it. -/
theorem call_activation {env : Declarations} {world : World} {parameters : Context}
    {arguments : List Result} {values : List Value} {substitution : List (ObjectRef × ObjectRef)}
    (formed : ParametersValid env [] parameters)
    (matched : FinalArgumentsMatch env parameters arguments substitution)
    (typed : ResultsHaveTypes env world values arguments) :
    ∃ activation, bindArguments parameters values = some activation ∧
      ContextHasType env (objectWorld activation) activation parameters ∧
      (∀ ref ∈ contextRefs parameters, ∀ object,
        RefDenotes env.indexed (objectWorld activation) ref object ↔
          RefDenotes env.indexed world (renameRef substitution ref) object) := by
  obtain ⟨activation, bound, witnesses⟩ := bind_arguments_typed (parameters_unique formed) matched.1 typed
  have transport := parameter_reference_transport formed matched witnesses
  refine ⟨activation, bound, ?_, transport⟩
  intro parameter member
  obtain ⟨argument, value, pairMember, present, operandTyped⟩ := witnesses parameter member
  have matchedPair := matched.2 (parameter, argument) pairMember
  have facts := parameter_formed formed member
  refine ⟨value, present, ?_, ?_⟩
  · exact value_rename_backward facts.1.1
      (fun ref refMember object denotes =>
        (transport ref (List.mem_flatMap.mpr ⟨parameter, member, List.mem_append_right _ refMember⟩) object).mpr denotes)
      (value_compatible matchedPair.1 operandTyped.1)
  · cases reference : parameter.result.reference with
    | none => trivial
    | some ref =>
      have association := matchedPair.2
      rw [reference] at association
      cases actualReference : argument.reference with
      | none => simp [actualReference] at association
      | some actual =>
        simp only [actualReference] at association
        have denotes := operandTyped.2
        rw [actualReference] at denotes
        obtain ⟨object, equal, actualDenotes⟩ := denotes
        refine ⟨object, equal, ?_⟩
        apply (transport ref (List.mem_flatMap.mpr ⟨parameter, member,
          List.mem_append_left _ (by simp [reference])⟩) object).mpr
        simpa only [association] using actualDenotes

end VastitasOracle.IndexedArgumentSafety
