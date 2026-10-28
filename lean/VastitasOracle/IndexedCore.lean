import VastitasKernel.IndexedTypeAudit
import VastitasOracle.Dependency

/-! Structural acceptance of the declaration-driven Core. This does not yet
assert source correspondence, typed evaluation or native backend refinement. -/
namespace VastitasOracle.IndexedCore
open VastitasKernel.Indexed VastitasKernel.Indexed.Core VastitasKernel.Indexed.Core.Typing

theorem checkModule_input (module : Module) (requireMain : Bool) (checked : CheckedModule requireMain)
    (accepted : checkModule module requireMain = .ok checked) : checked.module = module := by
  unfold checkModule at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted
        rfl
      · contradiction
    · contradiction
  · contradiction

theorem checked_module_ordered (checked : CheckedModule requireMain) :
    VastitasKernel.Dependency.OrderedFrom [] (dependencyEntries checked.module) :=
  VastitasOracle.Dependency.audit_sound _ checked.ordered

/-- All evidence concerns the exact accepted module, including its declaration
contracts and actual call graph, rather than independently selected metadata. -/
theorem checkModule_acceptance (module : Module) (requireMain : Bool) (checked : CheckedModule requireMain)
    (accepted : checkModule module requireMain = .ok checked) :
    checked.module = module ∧ ModuleTyped module ∧
      VastitasKernel.Dependency.OrderedFrom [] (dependencyEntries module) ∧ MainValid module requireMain := by
  have same := checkModule_input module requireMain checked accepted
  refine ⟨same, ?_, ?_, ?_⟩
  · simpa only [same] using checked.typed
  · simpa only [same] using checked_module_ordered checked
  · simpa only [same] using checked.entry

theorem checked_function_body (checked : CheckedModule requireMain) (function : Function)
    (member : function ∈ checked.module.functions) :
    HasType checked.module.declarations (signatures checked.module) function.parameters function.body :=
  (checked.typed.functions function member).2.1

theorem checked_fresh_serials (checked : CheckedModule requireMain) :
    (freshSerials checked.module).Nodup := checked.typed.fresh

theorem typed_scope_does_not_escape (env : Declarations) (functions : Signatures) (ctx : Context) (body : Term)
    (typed : HasType env functions ctx (.scope body)) : body.result.type.Scoped (contextRefs ctx) := typed.2.2

theorem typed_unpack_does_not_escape (env : Declarations) (functions : Signatures) (ctx : Context)
    (witnessSymbol : Nat) (fieldSymbols : List Nat) (package body : Term)
    (application : Application) (shape : PackageShape)
    (type : package.result.type = .package application) (declared : env.package? application = some shape)
    (typed : HasType env functions ctx (.unpack witnessSymbol fieldSymbols package body)) :
    body.result.type.Scoped (contextRefs ctx) := by
  simp only [HasType, type, declared] at typed
  exact typed.2.2.2.2.2.2.2

theorem ascription_keeps_reference (annotation : DataType) (value : Term) :
    (Term.ascribe annotation value).result.reference = value.result.reference := rfl

theorem typed_ascription (env : Declarations) (functions : Signatures) (ctx : Context)
    (annotation : DataType) (value : Term) (typed : HasType env functions ctx (.ascribe annotation value)) :
    Compatible env value.result.type annotation := typed.2.2

theorem typed_call_substitution (env : Declarations) (functions : Signatures) (ctx : Context)
    (id : Nat) (arguments : List Term) (substitution : List (ObjectRef × ObjectRef)) (result : Result)
    (signature : Signature) (found : functions.find? (fun signature => signature.id == id) = some signature)
    (typed : HasType env functions ctx (.call id arguments substitution result)) :
    CallSubstitution env substitution := by
  have relation := typed.2.2
  simp only [CallTyping, found] at relation
  exact relation.2.2.1

theorem typed_primitive_contract (env : Declarations) (functions : Signatures) (ctx : Context)
    (id : DeclId) (arguments : List Term) (result : Result) (binding : PrimitiveBinding)
    (operands : List ValueType) (output : ValueType)
    (found : env.primitive? id = some binding)
    (input : (arguments.map Term.result).mapM Result.primitiveType? = some operands)
    (outputType : result.primitiveType? = some output)
    (typed : HasType env functions ctx (.primitive id arguments result)) :
    PrimitiveTyped env.indexed binding (contextRefs ctx) (primitiveBrand result) operands output := by
  have relation := typed.2.2
  simpa only [PrimitiveTyping, found, input, outputType] using relation

theorem typed_package_association (env : Declarations) (functions : Signatures) (ctx : Context)
    (application : Application) (witness : Term) (fields : List Term) (shape : PackageShape)
    (reference : ObjectRef) (applications : List Application)
    (found : env.package? application = some shape) (witnessType : witness.result.reference = some reference)
    (fieldTypes : indexedFields (fields.map Term.result) = some applications)
    (typed : HasType env functions ctx (.pack application witness fields)) :
    PackagePayload.Valid env.indexed shape ⟨reference, applications⟩ := by
  have relation := typed.2.2.2
  simp only [PackageTyping, found, witnessType, fieldTypes] at relation
  exact relation.2

end VastitasOracle.IndexedCore
