import VastitasKernel.Typing

/-!
Executable validation of the independent structural typing rules. This audit
checks the actual annotated term, including variable lookup, primitive operand
contracts, dependent call substitutions, packages, and every intermediate term.
It is deliberately independent of the raw-source elaborator's control flow.
-/
namespace VastitasKernel.Typing

mutual
  def hasTypeDecidable (signatures : Signatures) (ctx : Context) (term : Term) :
      Decidable (HasType signatures ctx term) := by
    cases term with
    | literal ty value => unfold HasType; infer_instance
    | boolean value => unfold HasType; infer_instance
    | unit => unfold HasType; infer_instance
    | var symbol result => unfold HasType; infer_instance
    | call id args substitution result =>
        haveI := argsTypedDecidable signatures ctx args
        unfold HasType
        infer_instance
    | builtin op args result =>
        haveI := argsTypedDecidable signatures ctx args
        unfold HasType
        infer_instance
    | unary op arg result =>
        haveI := hasTypeDecidable signatures ctx arg
        unfold HasType
        infer_instance
    | binary op left right result =>
        haveI := hasTypeDecidable signatures ctx left
        haveI := hasTypeDecidable signatures ctx right
        unfold HasType
        infer_instance
    | branch condition yes no result =>
        haveI := hasTypeDecidable signatures ctx condition
        haveI := hasTypeDecidable signatures ctx yes
        haveI := hasTypeDecidable signatures ctx no
        unfold HasType
        infer_instance
    | pack base scheme point =>
        haveI := hasTypeDecidable signatures ctx scheme
        haveI := hasTypeDecidable signatures ctx point
        unfold HasType
        dsimp only
        cases scheme.resultType.objectRef <;> infer_instance
    | letE symbol value body =>
        haveI := hasTypeDecidable signatures ctx value
        haveI := hasTypeDecidable signatures (⟨symbol, value.resultType⟩ :: ctx) body
        unfold HasType
        infer_instance
    | unpack objectSymbol pointSymbol value body =>
        haveI := hasTypeDecidable signatures ctx value
        unfold HasType
        dsimp only
        cases value.ty with
        | pointed base =>
            haveI := hasTypeDecidable signatures
              (⟨pointSymbol, ⟨unpackedPointType base objectSymbol, none⟩⟩ ::
               ⟨objectSymbol, ⟨.object base, some (.local base objectSymbol)⟩⟩ :: ctx) body
            infer_instance
        | _ => infer_instance
    termination_by sizeOf term
    decreasing_by all_goals simp_wf; all_goals omega

  def argsTypedDecidable (signatures : Signatures) (ctx : Context) (args : List Term) :
      Decidable (ArgsTyped signatures ctx args) := by
    cases args with
    | nil => unfold ArgsTyped; infer_instance
    | cons arg rest =>
        haveI := hasTypeDecidable signatures ctx arg
        haveI := argsTypedDecidable signatures ctx rest
        unfold ArgsTyped
        infer_instance
    termination_by sizeOf args
    decreasing_by all_goals simp_wf; all_goals omega
end

instance (signatures : Signatures) (ctx : Context) (term : Term) :
    Decidable (HasType signatures ctx term) := hasTypeDecidable signatures ctx term

instance (signatures : Signatures) (ctx : Context) (args : List Term) :
    Decidable (ArgsTyped signatures ctx args) := argsTypedDecidable signatures ctx args

instance parametersWellFormedDecidable (previous : Context) (params : List CheckedParam) :
    Decidable (ParametersWellFormed previous params) := by
  cases params with
  | nil => unfold ParametersWellFormed; infer_instance
  | cons param rest =>
      haveI := parametersWellFormedDecidable (param :: previous) rest
      unfold ParametersWellFormed
      cases param.ty <;> infer_instance

instance (signatures : Signatures) (function : CheckedFunction) :
    Decidable (FunctionWellTyped signatures function) := by
  unfold FunctionWellTyped
  infer_instance

/-- Validate all actual bodies against the finalized module signature map. -/
def auditBodies (module : CheckedModule) : Bool :=
  let signatures := moduleSignatures module
  module.functions.all (fun function => decide (FunctionWellTyped signatures function))

/-- Linear-time distinctness validation used for function IDs and fresh brands. -/
def distinctFrom {α : Type} [BEq α] [Hashable α]
    (seen : Std.HashSet α) : List α → Bool
  | [] => true
  | value :: rest =>
      if seen.contains value then false
      else distinctFrom (seen.insert value) rest

def freshRefs (module : CheckedModule) : List ObjectRef :=
  module.functions.flatMap fun function =>
    parameterRefs function.params ++ allocatedRefs function.body

/-- Full checked-language audit, beyond the legacy annotation-only certificate. -/
def auditModule (module : CheckedModule) : Bool :=
  distinctFrom {} (module.functions.map (·.id)) &&
  distinctFrom {} (freshRefs module) && auditBodies module

end VastitasKernel.Typing
