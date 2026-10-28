import VastitasKernel.IndexedCore

namespace VastitasKernel.Indexed.Core.Typing
open VastitasKernel.Indexed.Audit

abbrev Context := List Parameter

def lookup (ctx : Context) (symbol : Nat) : Option Result :=
  (ctx.find? fun binding => binding.symbol == symbol).map Parameter.result

def contextRefs (ctx : Context) : List ObjectRef := ctx.flatMap fun binding => binding.result.refs

def Compatible (env : Declarations) (actual expected : DataType) : Prop :=
  match actual, expected with
  | .object actual, .object expected => actual.Refines env.indexed expected
  | _, _ => actual = expected

instance (env : Declarations) (actual expected : DataType) : Decidable (Compatible env actual expected) := by
  unfold Compatible
  split <;> infer_instance

instance (env : Declarations) (type : DataType) : Decidable (type.Valid env) := by
  cases type <;> unfold DataType.Valid <;> infer_instance

instance (env : Declarations) (result : Result) : Decidable (result.Valid env) := by
  unfold Result.Valid
  split <;> infer_instance

/-- Dependent calls can refine the formal finite domain, but cannot change the
coefficient marker, rewrite globals or provide conflicting substitutions. -/
def CallSubstitution (env : Declarations) (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  (substitution.map Prod.fst).Nodup ∧ ∀ pair ∈ substitution,
    pair.1.isLocal = true ∧ ∃ formal ∈ pair.1.type? env.indexed,
      ∃ actual ∈ pair.2.type? env.indexed, actual.Refines env.indexed formal

instance (env : Declarations) (substitution : List (ObjectRef × ObjectRef)) :
    Decidable (CallSubstitution env substitution) := by
  unfold CallSubstitution
  infer_instance

def LocalResult (type : ObjectType) (result : Result) : Prop :=
  result.type = .object type ∧ match result.reference with
    | some (.local actual _) => actual = type
    | _ => False

instance (type : ObjectType) (result : Result) : Decidable (LocalResult type result) := by
  unfold LocalResult
  split <;> infer_instance

structure Signature where
  id : Nat
  parameters : List Parameter
  result : DataType
  deriving Repr, Inhabited

abbrev Signatures := Std.HashMap Nat Signature

def signatureOf (function : Function) : Signature :=
  ⟨function.id, function.parameters, function.returnType⟩

def signatures (module : Module) : Signatures :=
  module.functions.foldl (fun table function => table.insert function.id (signatureOf function)) {}

def ArgumentsMatch (env : Declarations) : List Parameter → List Result →
    List (ObjectRef × ObjectRef) → List (ObjectRef × ObjectRef) → Prop
  | [], [], initial, final => final = initial
  | parameter :: rest, argument :: arguments, initial, final =>
      Compatible env argument.type (parameter.result.type.rename initial) ∧
      match parameter.result.reference, argument.reference with
      | none, _ => ArgumentsMatch env rest arguments initial final
      | some formal, some actual => ArgumentsMatch env rest arguments ((formal, actual) :: initial) final
      | some _, none => False
  | _, _, _, _ => False

instance argumentsMatchDecidable (env : Declarations) (parameters : List Parameter) (arguments : List Result)
    (initial final : List (ObjectRef × ObjectRef)) : Decidable (ArgumentsMatch env parameters arguments initial final) := by
  cases parameters with
  | nil => cases arguments <;> simp only [ArgumentsMatch] <;> infer_instance
  | cons parameter rest =>
    cases arguments with
    | nil => simp only [ArgumentsMatch]; infer_instance
    | cons argument arguments =>
      simp only [ArgumentsMatch]
      cases parameter.result.reference with
      | none =>
        haveI := argumentsMatchDecidable env rest arguments initial final
        infer_instance
      | some formal =>
        cases argument.reference with
        | none => infer_instance
        | some actual =>
          haveI := argumentsMatchDecidable env rest arguments ((formal, actual) :: initial) final
          infer_instance

def FinalArgumentsMatch (env : Declarations) (parameters : List Parameter) (arguments : List Result)
    (substitution : List (ObjectRef × ObjectRef)) : Prop :=
  parameters.length = arguments.length ∧ ∀ pair ∈ parameters.zip arguments,
    Compatible env pair.2.type (pair.1.result.type.rename substitution) ∧
    (match pair.1.result.reference, pair.2.reference with
    | none, _ => True
    | some formal, some actual => renameRef substitution formal = actual
    | some _, none => False)

instance (env : Declarations) (parameters : List Parameter) (arguments : List Result)
    (substitution : List (ObjectRef × ObjectRef)) :
    Decidable (FinalArgumentsMatch env parameters arguments substitution) := by
  haveI : DecidablePred (fun pair : Parameter × Result =>
      Compatible env pair.2.type (pair.1.result.type.rename substitution) ∧
      (match pair.1.result.reference, pair.2.reference with
       | none, _ => True | some formal, some actual => renameRef substitution formal = actual
       | some _, none => False)) := fun pair => by
    dsimp only
    cases pair.1.result.reference <;> cases pair.2.reference <;> dsimp only <;> infer_instance
  unfold FinalArgumentsMatch
  infer_instance

def CallTyping (env : Declarations) (functions : Signatures) (id : Nat) (arguments : List Result)
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) : Prop :=
  match functions[id]? with
  | none => False
  | some signature =>
      ArgumentsMatch env signature.parameters arguments [] substitution ∧
      FinalArgumentsMatch env signature.parameters arguments substitution ∧ CallSubstitution env substitution ∧
      match signature.result with
      | .object type => LocalResult type result
      | other => result = ⟨other.rename substitution, none⟩

instance (env : Declarations) (functions : Signatures) (id : Nat) (arguments : List Result)
    (substitution : List (ObjectRef × ObjectRef)) (result : Result) :
    Decidable (CallTyping env functions id arguments substitution result) := by
  unfold CallTyping
  split
  · infer_instance
  · split <;> infer_instance

def UnaryTyping (op : UnaryOp) (argument result : DataType) : Prop :=
  match op with
  | .neg => argument = .pure .int ∧ result = .pure .int
  | .not => argument = .pure .bool ∧ result = .pure .bool

instance (op : UnaryOp) (argument result : DataType) : Decidable (UnaryTyping op argument result) := by
  cases op <;> unfold UnaryTyping <;> infer_instance

def BinaryTyping (op : BinaryOp) (left right result : DataType) : Prop :=
  left = right ∧ match op with
  | .add | .sub | .mul => (left = .pure .nat ∨ left = .pure .int) ∧ result = left
  | .eq | .ne =>
      (left = .pure .nat ∨ left = .pure .int ∨ left = .pure .bool ∨ left = .pure .unit) ∧ result = .pure .bool
  | .lt | .le | .gt | .ge => (left = .pure .nat ∨ left = .pure .int) ∧ result = .pure .bool
  | .and | .or => left = .pure .bool ∧ result = .pure .bool

instance (op : BinaryOp) (left right result : DataType) : Decidable (BinaryTyping op left right result) := by
  cases op <;> unfold BinaryTyping <;> infer_instance

def BranchTyping (yes no result : Result) : Prop :=
  yes.type = no.type ∧ result.type = yes.type ∧ match yes.type with
  | .object type => if yes.reference = no.reference then result.reference = yes.reference else LocalResult type result
  | _ => result.reference = none

instance (yes no result : Result) : Decidable (BranchTyping yes no result) := by
  unfold BranchTyping
  cases yes.type <;> infer_instance

def primitiveBrand (result : Result) : Nat :=
  match result.reference with | some (.local _ brand) => brand | _ => 0

def PrimitiveTyping (env : Declarations) (ctx : Context) (id : DeclId) (arguments : List Result)
    (result : Result) : Prop :=
  match env.primitive? id, arguments.mapM Result.primitiveType?, result.primitiveType? with
  | some binding, some operands, some output =>
    PrimitiveTyped env.indexed binding (contextRefs ctx) (primitiveBrand result) operands output
  | _, _, _ => False

instance (env : Declarations) (ctx : Context) (id : DeclId) (arguments : List Result) (result : Result) :
    Decidable (PrimitiveTyping env ctx id arguments result) := by
  unfold PrimitiveTyping
  split <;> infer_instance

def indexedFields (fields : List Result) : Option (List Application) := fields.mapM fun result =>
  match result.type, result.reference with | .indexed app, none => some app | _, _ => none

def PackageTyping (env : Declarations) (id : Application) (witness : Result) (fields : List Result) : Prop :=
  match env.package? id, witness.reference, indexedFields fields with
  | some shape, some ref, some applications =>
    Compatible env witness.type (.object shape.witnessType) ∧ PackagePayload.Valid env.indexed shape ⟨ref, applications⟩
  | _, _, _ => False

instance (env : Declarations) (id : Application) (witness : Result) (fields : List Result) :
    Decidable (PackageTyping env id witness fields) := by
  unfold PackageTyping
  split <;> infer_instance

def openedContext (shape : PackageShape) (witnessSymbol : Nat) (fieldSymbols : List Nat) : Context :=
  let witness := ObjectRef.local shape.witnessType witnessSymbol
  ⟨witnessSymbol, ⟨.object shape.witnessType, some witness⟩⟩ ::
    (fieldSymbols.zip (shape.instantiate witness)).map fun (symbol, application) =>
      ⟨symbol, ⟨.indexed application, none⟩⟩

mutual
  def HasType (env : Declarations) (functions : Signatures) (ctx : Context) (term : Term) : Prop :=
    term.result.Valid env ∧ match term with
    | .natural _ | .integer _ | .boolean _ | .unit => True
    | .variable symbol result => lookup ctx symbol = some result
    | .unary op operand result => HasType env functions ctx operand ∧ UnaryTyping op operand.result.type result.type
    | .binary op left right result => HasType env functions ctx left ∧ HasType env functions ctx right ∧
        BinaryTyping op left.result.type right.result.type result.type
    | .pair element first second => HasType env functions ctx first ∧ HasType env functions ctx second ∧
        first.result.type = .pure (match element with | .nat => .nat | .int => .int) ∧ second.result = first.result
    | .project element _ value => HasType env functions ctx value ∧ value.result.type = .pure (.pair element)
    | .natToInt value => HasType env functions ctx value ∧ value.result.type = .pure .nat
    | .ascribe annotation value => HasType env functions ctx value ∧ Compatible env value.result.type annotation
    | .primitive id arguments result => ArgsTyped env functions ctx arguments ∧
        PrimitiveTyping env ctx id (arguments.map Term.result) result
    | .call id arguments substitution result => ArgsTyped env functions ctx arguments ∧
        CallTyping env functions id (arguments.map Term.result) substitution result
    | .branch condition yes no result => HasType env functions ctx condition ∧ condition.result.type = .pure .bool ∧
        HasType env functions ctx yes ∧ HasType env functions ctx no ∧ BranchTyping yes.result no.result result
    | .pack id witness fields => HasType env functions ctx witness ∧ ArgsTyped env functions ctx fields ∧
        PackageTyping env id witness.result (fields.map Term.result)
    | .letE symbol value body => HasType env functions ctx value ∧ lookup ctx symbol = none ∧
        HasType env functions (⟨symbol, value.result⟩ :: ctx) body
    | .scope body => HasType env functions ctx body ∧ body.result.type.Scoped (contextRefs ctx)
    | .unpack witnessSymbol fieldSymbols package body => HasType env functions ctx package ∧
        (witnessSymbol :: fieldSymbols).Nodup ∧
        (∀ symbol ∈ witnessSymbol :: fieldSymbols, lookup ctx symbol = none) ∧
        FreshBrand (contextRefs ctx) witnessSymbol ∧
        match package.result.type with
        | .package id => match env.package? id with
          | some shape => fieldSymbols.length = shape.fields.length ∧
              HasType env functions (openedContext shape witnessSymbol fieldSymbols ++ ctx) body ∧
              body.result.type.Scoped (contextRefs ctx)
          | none => False
        | _ => False

  def ArgsTyped (env : Declarations) (functions : Signatures) (ctx : Context) : List Term → Prop
    | [] => True
    | argument :: rest => HasType env functions ctx argument ∧ ArgsTyped env functions ctx rest
end

end VastitasKernel.Indexed.Core.Typing
