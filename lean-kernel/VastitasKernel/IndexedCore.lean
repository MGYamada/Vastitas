import VastitasKernel.Core
import VastitasKernel.IndexedContractAudit

/-! The declaration-driven Core data model. IndexedTypeAudit independently
checks complete modules and IndexedCodegen lowers them to the minimal runtime.
LegacyIndexed routes the existing public compatibility path through this audit.
Public declaration syntax/protocol 7 and whole-term evaluation proofs remain pending. -/
namespace VastitasKernel.Indexed.Core

structure NamedPackage where
  id : DeclId
  cases : List PackageShape
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

structure NamedPrimitive where
  id : DeclId
  binding : PrimitiveBinding
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- All named contracts inhabit one canonical declaration namespace. Package
and primitive IDs cannot collide with markers, classes or indexed families. -/
structure Declarations where
  indexed : Environment
  packages : List NamedPackage
  primitives : List NamedPrimitive
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Declarations.ids (env : Declarations) : List DeclId :=
  env.indexed.map Entry.id ++ env.packages.map NamedPackage.id ++ env.primitives.map NamedPrimitive.id

/-- The initial existential family has explicit domain/marker indices and a
finite declared case table. Runtime objects and dimensions are not case keys. -/
def Declarations.package? (env : Declarations) (application : Application) : Option PackageShape := do
  let [.domain domain, .marker marker] := application.indices | none
  let family ← env.packages.find? fun declaration => declaration.id == application.family
  family.cases.find? fun shape => shape.witnessType == ⟨domain, marker⟩

def NamedPackage.Valid (env : Environment) (declaration : NamedPackage) : Prop :=
  declaration.cases ≠ [] ∧ declaration.cases.length ≤ 64 ∧
    (declaration.cases.map PackageShape.witnessType).Nodup ∧
    ∀ shape ∈ declaration.cases, shape.Valid env

instance (env : Environment) (declaration : NamedPackage) : Decidable (declaration.Valid env) := by
  unfold NamedPackage.Valid
  infer_instance

def Declarations.primitive? (env : Declarations) (id : DeclId) : Option PrimitiveBinding :=
  (env.primitives.find? fun declaration => declaration.id == id).map NamedPrimitive.binding

structure Declarations.Valid (env : Declarations) : Prop where
  indexed : env.indexed.Valid
  bounded : env.ids.length ≤ 4096
  unique : env.ids.Nodup
  packages : ∀ declaration ∈ env.packages, declaration.Valid env.indexed
  primitives : ∀ declaration ∈ env.primitives, declaration.binding.Valid env.indexed

def validDeclarations (env : Declarations) : Bool :=
  validEnvironment env.indexed && env.ids.length ≤ 4096 && decide env.ids.Nodup &&
    env.packages.all (fun declaration => decide (declaration.Valid env.indexed)) &&
    env.primitives.all (fun declaration => validPrimitiveBinding env.indexed declaration.binding)

inductive PureType where
  | nat | int | bool | unit
  | pair (element : PairElem)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive DataType where
  | pure (type : PureType)
  | object (type : ObjectType)
  | indexed (application : Application)
  | package (application : Application)
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def DataType.Valid (env : Declarations) : DataType → Prop
  | .pure _ => True
  | .object type => type.Valid env.indexed
  | .indexed application => application.Valid env.indexed
  | .package id => (env.package? id).isSome = true

def validType (env : Declarations) : DataType → Bool
  | .pure _ => true
  | .object type => decide (type.Valid env.indexed)
  | .indexed application => validApplication env.indexed application
  | .package id => (env.package? id).isSome

def DataType.refs : DataType → List ObjectRef
  | .indexed application | .package application => application.refs
  | _ => []

def DataType.rename (substitution : List (ObjectRef × ObjectRef)) : DataType → DataType
  | .indexed application => .indexed (application.rename substitution)
  | .package application => .package (application.rename substitution)
  | other => other

def DataType.Scoped (allowed : List ObjectRef) (type : DataType) : Prop :=
  ∀ ref ∈ type.refs, ref.Scoped allowed

instance (allowed : List ObjectRef) (type : DataType) : Decidable (type.Scoped allowed) := by
  unfold DataType.Scoped
  infer_instance

structure Result where
  type : DataType
  reference : Option ObjectRef := none
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

def Result.refs (result : Result) : List ObjectRef := result.reference.toList ++ result.type.refs

def Result.Valid (env : Declarations) (result : Result) : Prop :=
  result.type.Valid env ∧ match result.type, result.reference with
  | .object type, some reference => WitnessFits env.indexed type reference
  | .object _, none => False
  | _, none => True
  | _, some _ => False

def validResult (env : Declarations) (result : Result) : Bool :=
  validType env result.type && match result.type, result.reference with
  | .object type, some reference => decide (WitnessFits env.indexed type reference)
  | .object _, none => false
  | _, none => true
  | _, some _ => false

/-- Only the closed primitive profile's operand/result shapes convert to its
contract. No geometric function name or inferred native implementation is used. -/
def Result.primitiveType? (result : Result) : Option ValueType :=
  match result.type, result.reference with
  | .pure .nat, none => some .natural
  | .object type, some ref => some (.object type ref)
  | .indexed application, none => some (.indexed application)
  | _, _ => none

structure Parameter where
  symbol : Nat
  result : Result
  deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Hygienic Core: names only occur as canonical declaration references. Every
node retains its result; full independent typing must check that annotation. -/
inductive Term where
  | natural (value : Nat)
  | integer (value : Int)
  | boolean (value : Bool)
  | unit
  | variable (symbol : Nat) (result : Result)
  | unary (operator : UnaryOp) (operand : Term) (result : Result)
  | binary (operator : BinaryOp) (left right : Term) (result : Result)
  | pair (element : PairElem) (first second : Term)
  | project (element : PairElem) (first : Bool) (value : Term)
  | natToInt (value : Term)
  | ascribe (annotation : DataType) (value : Term)
  | primitive (declaration : DeclId) (arguments : List Term) (result : Result)
  | call (function : Nat) (arguments : List Term) (substitution : List (ObjectRef × ObjectRef))
      (result : Result)
  | branch (condition yes no : Term) (result : Result)
  | pack (application : Application) (witness : Term) (fields : List Term)
  | unpack (witnessSymbol : Nat) (fieldSymbols : List Nat) (package body : Term)
  | scope (body : Term)
  | letE (symbol : Nat) (value body : Term)
  deriving Repr, Inhabited

def Term.result : Term → Result
  | .natural _ => ⟨.pure .nat, none⟩
  | .integer _ => ⟨.pure .int, none⟩
  | .boolean _ => ⟨.pure .bool, none⟩
  | .unit => ⟨.pure .unit, none⟩
  | .variable _ result | .unary _ _ result | .binary _ _ _ result
  | .primitive _ _ result | .call _ _ _ result | .branch _ _ _ result => result
  | .pair element _ _ => ⟨.pure (.pair element), none⟩
  | .project .nat _ _ => ⟨.pure .nat, none⟩
  | .project .int _ _ => ⟨.pure .int, none⟩
  | .natToInt _ => ⟨.pure .int, none⟩
  | .ascribe annotation value => ⟨annotation, value.result.reference⟩
  | .pack declaration _ _ => ⟨.package declaration, none⟩
  | .unpack _ _ _ body | .letE _ _ body | .scope body => body.result

def Term.callIds : Term → List Nat
  | .call id arguments _ _ => id :: arguments.flatMap Term.callIds
  | .primitive _ arguments _ => arguments.flatMap Term.callIds
  | .unary _ operand _ | .project _ _ operand | .natToInt operand | .scope operand | .ascribe _ operand => operand.callIds
  | .binary _ left right _ | .pair _ left right => left.callIds ++ right.callIds
  | .branch condition yes no _ => condition.callIds ++ yes.callIds ++ no.callIds
  | .pack _ witness fields => witness.callIds ++ fields.flatMap Term.callIds
  | .unpack _ _ value body | .letE _ value body => value.callIds ++ body.callIds
  | _ => []

structure Function where
  id : Nat
  definition : Namespace.Owner
  parameters : List Parameter
  returnType : DataType
  body : Term
  span : Span := {}
  deriving Repr, Inhabited

structure Module where
  declarations : Declarations
  functions : List Function
  main : Option Nat
  deriving Repr, Inhabited

end VastitasKernel.Indexed.Core
