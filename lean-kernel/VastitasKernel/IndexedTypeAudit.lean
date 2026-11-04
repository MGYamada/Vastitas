import VastitasKernel.IndexedTyping
import VastitasKernel.FiniteIndex
import VastitasKernel.Dependency
import VastitasKernel.Distinct

namespace VastitasKernel.Indexed.Core.Typing
open VastitasKernel.Indexed.Audit

theorem validDeclarations_iff (env : Declarations) : validDeclarations env = true ↔ env.Valid := by
  simp only [validDeclarations, Bool.and_eq_true, List.all_eq_true, validEnvironment_iff,
    decide_eq_true_eq, validPrimitiveBinding_iff, and_assoc]
  exact ⟨fun ⟨indexed, bounded, unique, packages, primitives⟩ => ⟨indexed, bounded, unique, packages, primitives⟩,
    fun valid => ⟨valid.indexed, valid.bounded, valid.unique, valid.packages, valid.primitives⟩⟩

instance (env : Declarations) : Decidable env.Valid :=
  decidable_of_iff (validDeclarations env = true) (validDeclarations_iff env)

/-- A first-match symbol table and ordered references for the exact lexical context. -/
structure ContextIndex (ctx : Context) where
  bindings : Std.HashMap Nat Parameter
  exactBindings : bindings = Finite.firstIndex Parameter.symbol ctx
  refs : List ObjectRef
  exactRefs : refs = contextRefs ctx

def ContextIndex.build (ctx : Context) : ContextIndex ctx :=
  ⟨Finite.firstIndex Parameter.symbol ctx, rfl, contextRefs ctx, rfl⟩

def ContextIndex.bind {ctx : Context} (index : ContextIndex ctx) (binding : Parameter) :
    ContextIndex (binding :: ctx) :=
  ⟨index.bindings.insert binding.symbol binding, by rw [index.exactBindings]; rfl,
    binding.result.refs ++ index.refs, by rw [index.exactRefs]; rfl⟩

def ContextIndex.prepend {ctx : Context} (index : ContextIndex ctx) :
    (locals : Context) → ContextIndex (locals ++ ctx)
  | [] => index
  | binding :: rest => (index.prepend rest).bind binding

def ContextIndex.get? {ctx : Context} (index : ContextIndex ctx) (symbol : Nat) : Option Result :=
  index.bindings[symbol]?.map Parameter.result

theorem ContextIndex.get?_eq {ctx : Context} (index : ContextIndex ctx) (symbol : Nat) :
    index.get? symbol = lookup ctx symbol := by
  simp only [ContextIndex.get?, index.exactBindings, Finite.firstIndex_lookup, lookup]

theorem HasType.resultValid {env : Declarations} {functions : Signatures} {ctx : Context} {term : Term}
    (typed : HasType env functions ctx term) : term.result.Valid env := by
  cases term <;> exact typed.1

/-- A let's result is its body's result. The recursive body check already
establishes its validity, even when finding that result traverses further lets. -/
theorem letTyped_iff (env : Declarations) (functions : Signatures) (ctx : Context)
    (symbol : Nat) (value body : Term) :
    HasType env functions ctx (.letE symbol value body) ↔
      HasType env functions ctx value ∧ lookup ctx symbol = none ∧
      HasType env functions (⟨symbol, value.result⟩ :: ctx) body := by
  exact ⟨fun typed => typed.2, fun parts => ⟨parts.2.2.resultValid, parts⟩⟩

mutual
  def hasTypeWithIndex (env : Declarations) (functions : Signatures) (ctx : Context)
      (index : ContextIndex ctx) (term : Term) :
      Decidable (HasType env functions ctx term) := by
    cases term with
    | natural | integer | boolean | unit => unfold HasType; infer_instance
    | «variable» symbol result =>
      unfold HasType
      simp only [← index.get?_eq]
      infer_instance
    | unary op operand result =>
      haveI := hasTypeWithIndex env functions ctx index operand
      unfold HasType
      infer_instance
    | binary op left right result =>
      haveI := hasTypeWithIndex env functions ctx index left
      haveI := hasTypeWithIndex env functions ctx index right
      unfold HasType
      infer_instance
    | pair element first second =>
      haveI := hasTypeWithIndex env functions ctx index first
      haveI := hasTypeWithIndex env functions ctx index second
      unfold HasType
      infer_instance
    | project element first value =>
      haveI := hasTypeWithIndex env functions ctx index value
      unfold HasType
      infer_instance
    | natToInt value =>
      haveI := hasTypeWithIndex env functions ctx index value
      unfold HasType
      infer_instance
    | ascribe annotation value =>
      haveI := hasTypeWithIndex env functions ctx index value
      unfold HasType
      infer_instance
    | primitive id arguments result =>
      haveI := argsTypedWithIndex env functions ctx index arguments
      haveI : Decidable (PrimitiveTyping env ctx id (arguments.map Term.result) result) := by
        unfold PrimitiveTyping
        rw [← index.exactRefs]
        split <;> infer_instance
      unfold HasType
      infer_instance
    | call id arguments substitution result =>
      haveI := argsTypedWithIndex env functions ctx index arguments
      unfold HasType
      infer_instance
    | branch condition yes no result =>
      haveI := hasTypeWithIndex env functions ctx index condition
      haveI := hasTypeWithIndex env functions ctx index yes
      haveI := hasTypeWithIndex env functions ctx index no
      unfold HasType
      infer_instance
    | pack id witness fields =>
      haveI := hasTypeWithIndex env functions ctx index witness
      haveI := argsTypedWithIndex env functions ctx index fields
      unfold HasType
      infer_instance
    | scope body =>
      haveI := hasTypeWithIndex env functions ctx index body
      unfold HasType
      rw [← index.exactRefs]
      infer_instance
    | letE symbol value body =>
      haveI := hasTypeWithIndex env functions ctx index value
      haveI := hasTypeWithIndex env functions _ (index.bind ⟨symbol, value.result⟩) body
      rw [letTyped_iff, ← index.get?_eq]
      infer_instance
    | unpack witnessSymbol fieldSymbols package body =>
      haveI := hasTypeWithIndex env functions ctx index package
      unfold HasType
      simp only [← index.get?_eq, ← index.exactRefs]
      cases package.result.type with
      | package id =>
        dsimp only
        cases env.package? id with
        | none => infer_instance
        | some shape =>
          haveI := hasTypeWithIndex env functions _
            (index.prepend (openedContext shape witnessSymbol fieldSymbols)) body
          infer_instance
      | _ => infer_instance
    termination_by sizeOf term
    decreasing_by all_goals simp_wf; all_goals omega

  def argsTypedWithIndex (env : Declarations) (functions : Signatures) (ctx : Context)
      (index : ContextIndex ctx) (arguments : List Term) :
      Decidable (ArgsTyped env functions ctx arguments) := by
    cases arguments with
    | nil => unfold ArgsTyped; infer_instance
    | cons argument rest =>
      haveI := hasTypeWithIndex env functions ctx index argument
      haveI := argsTypedWithIndex env functions ctx index rest
      unfold ArgsTyped
      infer_instance
    termination_by sizeOf arguments
    decreasing_by all_goals simp_wf; all_goals omega
end

def hasTypeDecidable (env : Declarations) (functions : Signatures) (ctx : Context) (term : Term) :
    Decidable (HasType env functions ctx term) := hasTypeWithIndex env functions ctx (.build ctx) term

def argsTypedDecidable (env : Declarations) (functions : Signatures) (ctx : Context) (args : List Term) :
    Decidable (ArgsTyped env functions ctx args) := argsTypedWithIndex env functions ctx (.build ctx) args

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

def parametersValidWithIndex (env : Declarations) (previous : Context)
    (index : ContextIndex previous) (parameters : List Parameter) :
    Decidable (ParametersValid env previous parameters) := by
  cases parameters with
  | nil => unfold ParametersValid; infer_instance
  | cons parameter rest =>
    haveI := parametersValidWithIndex env _ (index.bind parameter) rest
    unfold ParametersValid
    simp only [← index.get?_eq, ← index.exactRefs]
    cases parameter.result.type <;> infer_instance

instance parametersValidDecidable (env : Declarations) (previous : Context) (parameters : List Parameter) :
    Decidable (ParametersValid env previous parameters) :=
  parametersValidWithIndex env previous (.build previous) parameters

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
      (match env.primitive? id with
        | some binding => if binding.allocates then resultSerials result else []
        | none => [])
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

instance (module : Module) : Decidable (ModuleTyped module) := by
  haveI : Decidable (module.functions.map Function.id).Nodup :=
    decidable_of_iff (Finite.distinct (module.functions.map Function.id) = true) (Finite.distinct_iff _)
  haveI : Decidable (freshSerials module).Nodup :=
    decidable_of_iff (Finite.distinct (freshSerials module) = true) (Finite.distinct_iff _)
  let table := signatures module
  exact
  decidable_of_iff
    (module.declarations.Valid ∧ (module.functions.map Function.id).Nodup ∧
      (freshSerials module).Nodup ∧ ∀ function ∈ module.functions,
        FunctionTyped module.declarations table function)
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
