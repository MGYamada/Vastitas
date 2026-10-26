import VastitasKernel.Core

/-!
Declarative typing rules for the annotated checked language. These predicates
refer to syntax, signature lookup, and nominal endpoint equality. They do not
refer to execution of the elaborator or to its success/failure result.

Fresh allocation is a separate module invariant: a syntactically well-typed
affine construction must not reuse another construction's brand.
-/
namespace VastitasKernel.Typing

structure FunctionSignature where
  id : Nat
  params : List CheckedParam
  returnType : Ty
  deriving Repr, Inhabited

abbrev Signatures := Std.HashMap Nat FunctionSignature
abbrev Context := List CheckedParam

def signatureOf (function : CheckedFunction) : FunctionSignature :=
  ⟨function.id, function.params, function.returnType⟩

def lookupSignature (signatures : Signatures) (id : Nat) : Option FunctionSignature :=
  signatures[id]?

def moduleSignatures (module : CheckedModule) : Signatures :=
  module.functions.foldl (fun signatures function =>
    signatures.insert function.id (signatureOf function)) {}

def lookupBinding (ctx : Context) (symbol : Nat) : Option ResultType :=
  (ctx.find? (fun binding => binding.symbol == symbol)).map (·.resultType)

def resultRefs (result : ResultType) : List ObjectRef :=
  result.objectRef.toList ++ result.ty.refs

def contextRefs (ctx : Context) : List ObjectRef :=
  ctx.flatMap (fun binding => resultRefs binding.resultType)

def parameterRefs (params : List CheckedParam) : List ObjectRef :=
  params.filterMap (·.resultType.objectRef)

def ResultWellFormed (result : ResultType) : Prop :=
  result.ty.WellFormed ∧ match result.ty, result.objectRef with
  | .object base, some ref => ref.baseKind = base
  | .object _, none => False
  | _, none => True
  | _, some _ => False

instance (result : ResultType) : Decidable (ResultWellFormed result) := by
  unfold ResultWellFormed
  cases result.ty <;> cases result.objectRef <;> infer_instance

def UnaryTyping (op : UnaryOp) (arg result : Ty) : Prop :=
  match op with
  | .neg => arg = .int ∧ result = .int
  | .not => arg = .bool ∧ result = .bool

instance (op : UnaryOp) (arg result : Ty) : Decidable (UnaryTyping op arg result) := by
  cases op <;> unfold UnaryTyping <;> infer_instance

def BinaryTyping (op : BinaryOp) (left right result : Ty) : Prop :=
  left = right ∧ match op with
  | .add | .sub | .mul => (left = .nat ∨ left = .int) ∧ result = left
  | .eq | .ne =>
      (left = .nat ∨ left = .int ∨ left = .bool ∨ left = .unit) ∧ result = .bool
  | .lt | .le | .gt | .ge => (left = .nat ∨ left = .int) ∧ result = .bool
  | .and | .or => left = .bool ∧ result = .bool

instance (op : BinaryOp) (left right result : Ty) :
    Decidable (BinaryTyping op left right result) := by
  cases op <;> unfold BinaryTyping <;> infer_instance

/-- An object result either aliases a known endpoint or introduces a local brand. -/
def LocalObjectResult (base : BaseKind) (result : ResultType) : Prop :=
  result.ty = .object base ∧ match result.objectRef with
  | some (.local actual _) => actual = base
  | _ => False

instance (base : BaseKind) (result : ResultType) :
    Decidable (LocalObjectResult base result) := by
  unfold LocalObjectResult
  split <;> infer_instance

def BuiltinTyping (op : BuiltinOp) (args : List ResultType) (result : ResultType) : Prop :=
  match op, args with
  | .affine base, [⟨.nat, none⟩] => LocalObjectResult base result
  | .base base, [] => result = ⟨.object base, some (.base base)⟩
  | .origin, [⟨.object base, some ref⟩] =>
      ref.baseKind = base ∧ result = ⟨.point ref (.base base), none⟩
  | .identity, [⟨.object base, some ref⟩] =>
      ref.baseKind = base ∧ result = ⟨.morphism ref ref, none⟩
  | .dimension, [⟨.object base, some ref⟩] =>
      ref.baseKind = base ∧ result = ⟨.nat, none⟩
  | .compose, [⟨.morphism middle target, none⟩, ⟨.morphism source middle', none⟩] =>
      middle = middle' ∧ source.baseKind = middle.baseKind ∧
      middle.baseKind = target.baseKind ∧ result = ⟨.morphism source target, none⟩
  | .apply, [⟨.morphism source target, none⟩, ⟨.point target' test, none⟩] =>
      source = target' ∧ source.baseKind = target.baseKind ∧
      source.baseKind = test.baseKind ∧ result = ⟨.point target test, none⟩
  | .int, [⟨.nat, none⟩] => result = ⟨.int, none⟩
  | _, _ => False

instance (op : BuiltinOp) (args : List ResultType) (result : ResultType) :
    Decidable (BuiltinTyping op args result) := by
  unfold BuiltinTyping
  split <;> infer_instance

def BranchTyping (yes no result : ResultType) : Prop :=
  yes.ty = no.ty ∧ result.ty = yes.ty ∧
  match yes.ty with
  | .object base =>
      if yes.objectRef = no.objectRef then result.objectRef = yes.objectRef
      else LocalObjectResult base result
  | _ => result.objectRef = none

instance (yes no result : ResultType) : Decidable (BranchTyping yes no result) := by
  unfold BranchTyping
  cases yes.ty <;> infer_instance

def ArgumentsMatch : List CheckedParam → List ResultType →
    List (ObjectRef × ObjectRef) → List (ObjectRef × ObjectRef) → Prop
  | [], [], initial, final => final = initial
  | param :: params, arg :: args, initial, final =>
      arg.ty = param.ty.rename initial ∧
      match param.resultType.objectRef, arg.objectRef with
      | none, _ => ArgumentsMatch params args initial final
      | some formal, some actual =>
          formal.baseKind = actual.baseKind ∧
          ArgumentsMatch params args ((formal, actual) :: initial) final
      | some _, none => False
  | _, _, _, _ => False

instance argumentsMatchDecidable (params : List CheckedParam) (args : List ResultType)
    (initial final : List (ObjectRef × ObjectRef)) :
    Decidable (ArgumentsMatch params args initial final) := by
  cases params with
  | nil => cases args <;> simp only [ArgumentsMatch] <;> infer_instance
  | cons param params =>
      cases args with
      | nil => simp only [ArgumentsMatch]; infer_instance
      | cons arg args =>
          simp only [ArgumentsMatch]
          cases param.resultType.objectRef with
          | none =>
              haveI := argumentsMatchDecidable params args initial final
              infer_instance
          | some formal =>
              cases arg.objectRef with
              | none => infer_instance
              | some actual =>
                  haveI := argumentsMatchDecidable params args ((formal, actual) :: initial) final
                  infer_instance

def FinalArgumentsMatch : List CheckedParam → List ResultType →
    List (ObjectRef × ObjectRef) → Prop
  | [], [], _ => True
  | param :: params, arg :: args, substitution =>
      arg.ty = param.ty.rename substitution ∧
      (match param.resultType.objectRef, arg.objectRef with
       | none, _ => True
       | some formal, some actual => renameRef substitution formal = actual
       | some _, none => False) ∧
      FinalArgumentsMatch params args substitution
  | _, _, _ => False

instance finalArgumentsMatchDecidable (params : List CheckedParam) (args : List ResultType)
    (substitution : List (ObjectRef × ObjectRef)) :
    Decidable (FinalArgumentsMatch params args substitution) := by
  cases params with
  | nil => cases args <;> simp only [FinalArgumentsMatch] <;> infer_instance
  | cons param params =>
      cases args with
      | nil => simp only [FinalArgumentsMatch]; infer_instance
      | cons arg args =>
          haveI := finalArgumentsMatchDecidable params args substitution
          simp only [FinalArgumentsMatch]
          cases param.resultType.objectRef <;> cases arg.objectRef <;> infer_instance

def SubstitutionValid (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  ∀ pair ∈ substitution,
    pair.1.baseKind = pair.2.baseKind ∧
      match pair.1 with | .local .. => True | .base _ => False

instance (substitution : List (ObjectRef × ObjectRef)) :
    Decidable (SubstitutionValid substitution) := by
  unfold SubstitutionValid
  haveI : DecidablePred (fun pair : ObjectRef × ObjectRef =>
    pair.1.baseKind = pair.2.baseKind ∧
      match pair.1 with | .local .. => True | .base _ => False) := fun pair => by
    rcases pair with ⟨ref, other⟩
    cases ref <;> dsimp <;> infer_instance
  exact List.decidableBAll (fun pair =>
    pair.1.baseKind = pair.2.baseKind ∧
      match pair.1 with | .local .. => True | .base _ => False) substitution

def CallTyping (signatures : Signatures) (id : Nat) (args : List ResultType)
    (substitution : List (ObjectRef × ObjectRef)) (result : ResultType) : Prop :=
  match lookupSignature signatures id with
  | none => False
  | some signature =>
      ArgumentsMatch signature.params args [] substitution ∧
      FinalArgumentsMatch signature.params args substitution ∧
      SubstitutionValid substitution ∧
      result.ty = signature.returnType.rename substitution ∧
      match result.ty with
      | .object base => LocalObjectResult base result
      | _ => result.objectRef = none

instance (signatures : Signatures) (id : Nat) (args : List ResultType)
    (substitution : List (ObjectRef × ObjectRef)) (result : ResultType) :
    Decidable (CallTyping signatures id args substitution result) := by
  unfold CallTyping
  split <;> rename_i signature
  · infer_instance
  · cases result.ty <;> infer_instance

mutual
  /-- The independent structural typing judgment for an annotated expression. -/
  def HasType (signatures : Signatures) (ctx : Context) (term : Term) : Prop :=
    ResultWellFormed term.resultType ∧ match term with
    | .literal ty _ => ty = .nat ∨ ty = .int
    | .boolean _ | .unit => True
    | .var symbol result => lookupBinding ctx symbol = some result
    | .call id args substitution result =>
        ArgsTyped signatures ctx args ∧
        CallTyping signatures id (args.map (·.resultType)) substitution result
    | .builtin op args result =>
        ArgsTyped signatures ctx args ∧ BuiltinTyping op (args.map (·.resultType)) result
    | .unary op arg result => HasType signatures ctx arg ∧ UnaryTyping op arg.ty result
    | .binary op left right result =>
        HasType signatures ctx left ∧ HasType signatures ctx right ∧
        BinaryTyping op left.ty right.ty result
    | .branch condition yes no result =>
        HasType signatures ctx condition ∧ condition.ty = .bool ∧
        HasType signatures ctx yes ∧ HasType signatures ctx no ∧
        BranchTyping yes.resultType no.resultType result
    | .pack base scheme point =>
        HasType signatures ctx scheme ∧ HasType signatures ctx point ∧
        scheme.ty = .object base ∧ match scheme.resultType.objectRef with
        | none => False
        | some ref => ref.baseKind = base ∧ point.ty = .point ref (.base base)
    | .letE symbol value body =>
        HasType signatures ctx value ∧ lookupBinding ctx symbol = none ∧
        HasType signatures (⟨symbol, value.resultType⟩ :: ctx) body
    | .unpack objectSymbol pointSymbol value body =>
        HasType signatures ctx value ∧ objectSymbol ≠ pointSymbol ∧
        lookupBinding ctx objectSymbol = none ∧ lookupBinding ctx pointSymbol = none ∧
        match value.ty with
        | .pointed base =>
            HasType signatures
              (⟨pointSymbol, ⟨unpackedPointType base objectSymbol, none⟩⟩ ::
               ⟨objectSymbol, ⟨.object base, some (.local base objectSymbol)⟩⟩ :: ctx) body
        | _ => False

  def ArgsTyped (signatures : Signatures) (ctx : Context) : List Term → Prop
    | [] => True
    | arg :: rest => HasType signatures ctx arg ∧ ArgsTyped signatures ctx rest
end

/-- All fresh brands introduced by syntactic allocation sites, excluding aliases. -/
def LocalRef : ObjectRef → Prop
  | .local .. => True
  | .base _ => False

def allocatedRefs : Term → List ObjectRef
  | .literal .. | .boolean .. | .unit | .var .. => []
  | .call _ args _ result => args.flatMap allocatedRefs ++ result.objectRef.toList
  | .builtin (.affine _) args result =>
      args.flatMap allocatedRefs ++ result.objectRef.toList
  | .builtin _ args _ => args.flatMap allocatedRefs
  | .unary _ arg _ => allocatedRefs arg
  | .binary _ left right _ => allocatedRefs left ++ allocatedRefs right
  | .branch condition yes no result =>
      allocatedRefs condition ++ allocatedRefs yes ++ allocatedRefs no ++
      (if yes.resultType.objectRef = no.resultType.objectRef then [] else result.objectRef.toList)
  | .pack _ scheme point => allocatedRefs scheme ++ allocatedRefs point
  | .letE _ value body => allocatedRefs value ++ allocatedRefs body
  | .unpack objectSymbol _ value body =>
      allocatedRefs value ++
      (match value.ty with | .pointed base => [ObjectRef.local base objectSymbol] | _ => []) ++
      allocatedRefs body

def ParametersWellFormed : Context → List CheckedParam → Prop
  | _, [] => True
  | previous, param :: rest =>
      lookupBinding previous param.symbol = none ∧ ResultWellFormed param.resultType ∧
      param.ty.Scoped (parameterRefs previous) ∧
      (match param.ty with
       | .object base => param.resultType.objectRef = some (.local base param.symbol)
       | _ => param.resultType.objectRef = none) ∧
      ParametersWellFormed (param :: previous) rest

def FunctionWellTyped (signatures : Signatures) (function : CheckedFunction) : Prop :=
  ParametersWellFormed [] function.params ∧
  HasType signatures function.params function.body ∧
  function.body.ty = function.returnType ∧
  function.returnType.Scoped (parameterRefs function.params)

def FreshModule (module : CheckedModule) : Prop :=
  (module.functions.flatMap fun function =>
    parameterRefs function.params ++ allocatedRefs function.body).Nodup

def ModuleWellTyped (module : CheckedModule) : Prop :=
  (module.functions.map (·.id)).Nodup ∧ FreshModule module ∧
    ∀ function ∈ module.functions,
      FunctionWellTyped (moduleSignatures module) function

end VastitasKernel.Typing
