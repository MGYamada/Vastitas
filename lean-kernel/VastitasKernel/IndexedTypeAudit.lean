import VastitasKernel.IndexedTyping
import VastitasKernel.Dependency

namespace VastitasKernel.Indexed.Core.Typing
open VastitasKernel.Indexed.Audit

theorem validDeclarations_iff (env : Declarations) : validDeclarations env = true ↔ env.Valid := by
  simp only [validDeclarations, Bool.and_eq_true, List.all_eq_true, validEnvironment_iff,
    decide_eq_true_eq, validPrimitiveBinding_iff, and_assoc]
  exact ⟨fun ⟨indexed, bounded, unique, packages, primitives⟩ => ⟨indexed, bounded, unique, packages, primitives⟩,
    fun valid => ⟨valid.indexed, valid.bounded, valid.unique, valid.packages, valid.primitives⟩⟩

instance (env : Declarations) : Decidable env.Valid :=
  decidable_of_iff (validDeclarations env = true) (validDeclarations_iff env)

mutual
  def hasTypeDecidable (env : Declarations) (functions : Signatures) (ctx : Context) (term : Term) :
      Decidable (HasType env functions ctx term) := by
    cases term with
    | natural | integer | boolean | unit | «variable» => unfold HasType; infer_instance
    | unary op operand result =>
      haveI := hasTypeDecidable env functions ctx operand
      unfold HasType
      infer_instance
    | binary op left right result =>
      haveI := hasTypeDecidable env functions ctx left
      haveI := hasTypeDecidable env functions ctx right
      unfold HasType
      infer_instance
    | pair element first second =>
      haveI := hasTypeDecidable env functions ctx first
      haveI := hasTypeDecidable env functions ctx second
      unfold HasType
      infer_instance
    | project element first value =>
      haveI := hasTypeDecidable env functions ctx value
      unfold HasType
      infer_instance
    | natToInt value =>
      haveI := hasTypeDecidable env functions ctx value
      unfold HasType
      infer_instance
    | ascribe annotation value =>
      haveI := hasTypeDecidable env functions ctx value
      unfold HasType
      infer_instance
    | primitive id arguments result =>
      haveI := argsTypedDecidable env functions ctx arguments
      unfold HasType
      infer_instance
    | call id arguments substitution result =>
      haveI := argsTypedDecidable env functions ctx arguments
      unfold HasType
      infer_instance
    | branch condition yes no result =>
      haveI := hasTypeDecidable env functions ctx condition
      haveI := hasTypeDecidable env functions ctx yes
      haveI := hasTypeDecidable env functions ctx no
      unfold HasType
      infer_instance
    | pack id witness fields =>
      haveI := hasTypeDecidable env functions ctx witness
      haveI := argsTypedDecidable env functions ctx fields
      unfold HasType
      infer_instance
    | scope body =>
      haveI := hasTypeDecidable env functions ctx body
      unfold HasType
      infer_instance
    | letE symbol value body =>
      haveI := hasTypeDecidable env functions ctx value
      haveI := hasTypeDecidable env functions (⟨symbol, value.result⟩ :: ctx) body
      unfold HasType
      infer_instance
    | unpack witnessSymbol fieldSymbols package body =>
      haveI := hasTypeDecidable env functions ctx package
      unfold HasType
      dsimp only
      cases package.result.type with
      | package id =>
        dsimp only
        cases env.package? id with
        | none => infer_instance
        | some shape =>
          haveI := hasTypeDecidable env functions (openedContext shape witnessSymbol fieldSymbols ++ ctx) body
          infer_instance
      | _ => infer_instance
    termination_by sizeOf term
    decreasing_by all_goals simp_wf; all_goals omega

  def argsTypedDecidable (env : Declarations) (functions : Signatures) (ctx : Context) (arguments : List Term) :
      Decidable (ArgsTyped env functions ctx arguments) := by
    cases arguments with
    | nil => unfold ArgsTyped; infer_instance
    | cons argument rest =>
      haveI := hasTypeDecidable env functions ctx argument
      haveI := argsTypedDecidable env functions ctx rest
      unfold ArgsTyped
      infer_instance
    termination_by sizeOf arguments
    decreasing_by all_goals simp_wf; all_goals omega
end

instance (env : Declarations) (functions : Signatures) (ctx : Context) (term : Term) :
    Decidable (HasType env functions ctx term) := hasTypeDecidable env functions ctx term

instance (env : Declarations) (functions : Signatures) (ctx : Context) (arguments : List Term) :
    Decidable (ArgsTyped env functions ctx arguments) := argsTypedDecidable env functions ctx arguments

def ParametersValid (env : Declarations) : Context → List Parameter → Prop
  | _, [] => True
  | previous, parameter :: rest =>
      lookup previous parameter.symbol = none ∧ parameter.result.Valid env ∧
      parameter.result.type.Scoped (contextRefs previous) ∧
      (match parameter.result.type with
       | .object type => parameter.result.reference = some (.local type parameter.symbol)
       | _ => parameter.result.reference = none) ∧ ParametersValid env (parameter :: previous) rest

instance parametersValidDecidable (env : Declarations) (previous : Context) (parameters : List Parameter) :
    Decidable (ParametersValid env previous parameters) := by
  cases parameters with
  | nil => unfold ParametersValid; infer_instance
  | cons parameter rest =>
    haveI := parametersValidDecidable env (parameter :: previous) rest
    unfold ParametersValid
    cases parameter.result.type <;> infer_instance

def FunctionTyped (env : Declarations) (functions : Signatures) (function : Function) : Prop :=
  ParametersValid env [] function.parameters ∧ HasType env functions function.parameters function.body ∧
    function.returnType.Valid env ∧ Compatible env function.body.result.type function.returnType ∧
    function.returnType.Scoped (contextRefs function.parameters)

instance (env : Declarations) (functions : Signatures) (function : Function) :
    Decidable (FunctionTyped env functions function) := by
  unfold FunctionTyped
  infer_instance

def localSerial (ref : ObjectRef) : Option Nat := match ref with
  | .local _ serial => some serial | .global _ => none

def resultSerials (result : Result) : List Nat := result.reference.toList.filterMap localSerial

/-- Audit all actual allocation nodes, even unused branches. Canonical globals
and aliases do not allocate. Numeric freshness is independent of claimed types. -/
def allocatedSerials (env : Declarations) : Term → List Nat
  | .natural _ | .integer _ | .boolean _ | .unit | .variable .. => []
  | .primitive id arguments result => arguments.flatMap (allocatedSerials env) ++
      (match env.primitive? id with | some (.descriptor _) => (resultSerials result) | _ => [])
  | .call _ arguments _ result => arguments.flatMap (allocatedSerials env) ++ (resultSerials result)
  | .unary _ operand _ | .project _ _ operand | .natToInt operand | .scope operand | .ascribe _ operand => allocatedSerials env operand
  | .binary _ left right _ | .pair _ left right => allocatedSerials env left ++ allocatedSerials env right
  | .branch condition yes no result => allocatedSerials env condition ++ allocatedSerials env yes ++
      allocatedSerials env no ++ (if yes.result.reference = no.result.reference then [] else (resultSerials result))
  | .pack _ witness fields => allocatedSerials env witness ++ fields.flatMap (allocatedSerials env)
  | .letE _ value body => allocatedSerials env value ++ allocatedSerials env body
  | .unpack witnessSymbol _ value body => allocatedSerials env value ++ witnessSymbol :: allocatedSerials env body

def freshSerials (module : Module) : List Nat := module.functions.flatMap fun function =>
  function.parameters.flatMap (fun parameter => (resultSerials parameter.result)) ++ allocatedSerials module.declarations function.body

structure ModuleTyped (module : Module) : Prop where
  declarations : module.declarations.Valid
  uniqueFunctions : (module.functions.map Function.id).Nodup
  fresh : (freshSerials module).Nodup
  functions : ∀ function ∈ module.functions, FunctionTyped module.declarations (signatures module) function

instance (module : Module) : Decidable (ModuleTyped module) :=
  decidable_of_iff
    (module.declarations.Valid ∧ (module.functions.map Function.id).Nodup ∧
      (freshSerials module).Nodup ∧ ∀ function ∈ module.functions,
        FunctionTyped module.declarations (signatures module) function)
    ⟨fun ⟨declarations, unique, fresh, functions⟩ => ⟨declarations, unique, fresh, functions⟩,
      fun valid => ⟨valid.declarations, valid.uniqueFunctions, valid.fresh, valid.functions⟩⟩

def dependencyEntries (module : Module) : List Dependency.Entry := module.functions.map fun function =>
  ⟨function.id, function.body.callIds, function.span⟩

def MainValid (module : Module) (requireMain : Bool) : Prop :=
  match module.main with
  | none => requireMain = false
  | some id => match module.functions.find? (fun function => function.id == id) with
    | some function => function.parameters = [] ∧ function.returnType = .pure .int
    | none => False

instance (module : Module) (requireMain : Bool) : Decidable (MainValid module requireMain) := by
  unfold MainValid
  split
  · infer_instance
  · split <;> infer_instance

/-- Full typed/dependency/entrypoint audit. This constructor is not a public
wire input, and is stronger than an annotation-only certificate. -/
structure CheckedModule (requireMain : Bool) where
  module : Module
  typed : ModuleTyped module
  ordered : Dependency.audit (dependencyEntries module) = true
  entry : MainValid module requireMain

def checkModule (module : Module) (requireMain : Bool := false) : Except Diagnostic (CheckedModule requireMain) := do
  if typed : ModuleTyped module then
    if ordered : Dependency.audit (dependencyEntries module) = true then
      if entry : MainValid module requireMain then
        return ⟨module, typed, ordered, entry⟩
      else throw { code := "E_MAIN", message := "entry point must have signature fn main() -> Int" }
    else throw { code := "E_DEPENDENCY", message := "Core dependencies must refer to earlier functions" }
  else throw { code := "E_INTERNAL_TYPE", message := "indexed Core failed independent declaration, typing, scope or freshness audit" }

end VastitasKernel.Indexed.Core.Typing
