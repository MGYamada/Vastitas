import Std

namespace VastitasKernel

structure Span where
  start : Nat := 0
  «end» : Nat := 0
  line : Nat := 1
  column : Nat := 1
  deriving Repr, Inhabited

structure Diagnostic where
  code : String
  message : String
  span : Span := {}
  deriving Repr, Inhabited

inductive BaseKind where
  | qq
  | cinfReal
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def BaseKind.ringName : BaseKind → String
  | .qq => "QQ"
  | .cinfReal => "CInfReal"

def BaseKind.settingName : BaseKind → String
  | .qq => "Scheme"
  | .cinfReal => "CInfScheme"

inductive ObjectRef where
  | base (base : BaseKind)
  | local (base : BaseKind) (id : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def ObjectRef.baseKind : ObjectRef → BaseKind
  | .base b | .local b _ => b

def ObjectRef.label : ObjectRef → String
  | .base b => s!"Base({b.ringName})"
  | .local b n => s!"{b.settingName}#{n}"

inductive Ty where
  | nat | int | bool | unit
  | object (base : BaseKind)
  | point (target source : ObjectRef)
  | morphism (source target : ObjectRef)
  | pointed (base : BaseKind)
  deriving Repr, DecidableEq, BEq, Inhabited

def Ty.label : Ty → String
  | .nat => "Nat"
  | .int => "Int"
  | .bool => "Bool"
  | .unit => "Unit"
  | .object b => b.settingName
  | .point x s => s!"Point<{x.label}, {s.label}>"
  | .morphism x y => s!"Morphism<{x.label}, {y.label}>"
  | .pointed b => s!"Pointed<{b.settingName}, {b.ringName}>"

def Ty.WellFormed : Ty → Prop
  | .point x s => x.baseKind = s.baseKind
  | .morphism x y => x.baseKind = y.baseKind
  | _ => True

instance (t : Ty) : Decidable t.WellFormed := by cases t <;> unfold Ty.WellFormed <;> infer_instance

def Ty.refs : Ty → List ObjectRef
  | .point x s | .morphism x s => [x, s]
  | _ => []


/-- Canonical bases are globally available; fresh local identities need an outer binding. -/
def ObjectRef.InScope (allowed : List ObjectRef) : ObjectRef → Prop
  | .base _ => True
  | .local b n => ObjectRef.local b n ∈ allowed

instance (allowed : List ObjectRef) (r : ObjectRef) : Decidable (r.InScope allowed) := by
  cases r <;> simp only [ObjectRef.InScope] <;> infer_instance

/-- A result type may mention only canonical bases and identities from its outer scope. -/
def Ty.Scoped (allowed : List ObjectRef) (ty : Ty) : Prop :=
  ∀ ref ∈ ty.refs, ref.InScope allowed

instance (allowed : List ObjectRef) (ty : Ty) : Decidable (ty.Scoped allowed) := by
  unfold Ty.Scoped
  infer_instance

/-- Return the first endpoint that would escape, preserving precise diagnostics. -/
def checkScopeRefs (allowed : List ObjectRef) : List ObjectRef → Except ObjectRef Unit
  | [] => .ok ()
  | ref :: rest =>
    if ref.InScope allowed then checkScopeRefs allowed rest else .error ref

def checkScope (allowed : List ObjectRef) (ty : Ty) : Except ObjectRef Unit :=
  checkScopeRefs allowed ty.refs

/-- The type introduced for the point when an existential package is opened. -/
def unpackedPointType (base : BaseKind) (id : Nat) : Ty :=
  .point (.local base id) (.base base)

def renameRef (substitution : List (ObjectRef × ObjectRef)) (r : ObjectRef) : ObjectRef :=
  match substitution.find? (fun pair => pair.1 == r) with
  | some pair => pair.2
  | none => r

def Ty.rename (substitution : List (ObjectRef × ObjectRef)) : Ty → Ty
  | .point x s => .point (renameRef substitution x) (renameRef substitution s)
  | .morphism x y => .morphism (renameRef substitution x) (renameRef substitution y)
  | t => t

/-- The independently specified contract of a well-typed geometric application. -/
def ApplyContract (map point result : Ty) : Prop :=
  ∃ x y s, map = .morphism x y ∧ point = .point x s ∧
    result = .point y s ∧ x.baseKind = y.baseKind ∧ x.baseKind = s.baseKind

/-- These small executable rules are shared with the proof-only oracle. -/
def checkApply (map point : Ty) : Except String Ty := do
  match map, point with
  | .morphism x y, .point target source =>
    if x = target ∧ x.baseKind = y.baseKind ∧ x.baseKind = source.baseKind then
      pure (.point y source)
    else throw "map source, point target, or geometric base mismatch"
  | _, _ => throw "apply requires a morphism and a point"

def checkCompose (g f : Ty) : Except String Ty := do
  match g, f with
  | .morphism middle target, .morphism source middle' =>
    if middle = middle' ∧ source.baseKind = middle.baseKind ∧ middle.baseKind = target.baseKind then
      pure (.morphism source target)
    else throw "compose requires matching middle endpoints and bases"
  | _, _ => throw "compose requires two morphisms"

def checkPack (object : ObjectRef) (point : Ty) : Except String Ty := do
  match point with
  | .point target source =>
    if target = object ∧ source = .base object.baseKind then
      pure (.pointed object.baseKind)
    else throw "package point must belong to its object and use the declared base object"
  | _ => throw "package requires a point"

inductive RawIndex where
  | name (name : String)
  | base (ring : String)
  deriving Repr, Inhabited

inductive RawType where
  | named (name : String)
  | point (target source : RawIndex)
  | morphism (source target : RawIndex)
  | pointed (setting base : String)
  deriving Repr, Inhabited

mutual
  inductive RawExpr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | call (callee : String) (args : List RawExpr) (span : Span)
    | unary (op : String) (operand : RawExpr) (span : Span)
    | binary (op : String) (left right : RawExpr) (span : Span)
    | ite (condition : RawExpr) (yes no : RawBlock) (span : Span)
    | block (body : RawBlock) (span : Span)
    | pack (scheme point : RawExpr) (span : Span)
    deriving Repr, Inhabited
  inductive RawStmt where
    | letE (name : String) (annotation : Option RawType) (value : RawExpr) (span : Span)
    | unpack (value : RawExpr) (scheme point : String) (span : Span)
    deriving Repr, Inhabited
  inductive RawBlock where
    | mk (statements : List RawStmt) (result : RawExpr) (span : Span)
    deriving Repr, Inhabited
end

def RawExpr.span : RawExpr → Span
  | .integer _ s | .boolean _ s | .unit s | .variable _ s | .call _ _ s
  | .unary _ _ s | .binary _ _ _ s | .ite _ _ _ s | .block _ s | .pack _ _ s => s

structure RawParam where
  name : String
  ty : RawType
  span : Span
  deriving Repr, Inhabited

structure RawFunction where
  name : String
  params : List RawParam
  returnType : RawType
  body : RawBlock
  span : Span
  deriving Repr, Inhabited

structure RawModule where
  version : Nat
  file : String
  functions : List RawFunction
  deriving Repr, Inhabited

/-- Hygienic, typed core. Source spellings are never emitted as Lean identifiers. -/
inductive Term where
  | literal (ty : Ty) (value : String)
  | boolean (value : Bool)
  | unit
  | var (symbol : Nat) (ty : Ty)
  | call (functionId : Nat) (args : List Term) (ty : Ty)
  | builtin (name : String) (base : Option BaseKind) (args : List Term) (ty : Ty)
  | unary (op : String) (arg : Term) (ty : Ty)
  | binary (op : String) (left right : Term) (ty : Ty)
  | branch (condition yes no : Term) (ty : Ty)
  | pack (base : BaseKind) (scheme point : Term)
  | letE (symbol : Nat) (value body : Term)
  | unpack (objectSymbol pointSymbol : Nat) (value body : Term)
  deriving Repr, Inhabited

def Term.ty : Term → Ty
  | .literal t _ | .var _ t | .call _ _ t | .builtin _ _ _ t
  | .unary _ _ t | .binary _ _ _ t | .branch _ _ _ t => t
  | .boolean _ => .bool
  | .unit => .unit
  | .pack b _ _ => .pointed b
  | .letE _ _ body | .unpack _ _ _ body => body.ty

/-- A finite per-function lowering budget shared by check and build. An unpack
expands to a package binding and its two projections in the emitted Lean. -/
def generatedLetLimit : Nat := 4096

def Term.generatedLetCount : Term → Nat
  | .call _ args _ | .builtin _ _ args _ => (args.map Term.generatedLetCount).sum
  | .unary _ arg _ => arg.generatedLetCount
  | .binary _ left right _ => left.generatedLetCount + right.generatedLetCount
  | .branch condition yes no _ =>
      condition.generatedLetCount + yes.generatedLetCount + no.generatedLetCount
  | .pack _ scheme point => scheme.generatedLetCount + point.generatedLetCount
  | .letE _ value body => 1 + value.generatedLetCount + body.generatedLetCount
  | .unpack _ _ value body => 3 + value.generatedLetCount + body.generatedLetCount
  | _ => 0

structure CheckedFunction where
  id : Nat
  name : String
  params : List (Nat × Ty)
  returnType : Ty
  body : Term
  span : Span := {}
  deriving Repr, Inhabited

structure CheckedModule where
  functions : List CheckedFunction
  mainId : Option Nat
  deriving Repr, Inhabited


/-- Every type annotation retained in a core term, including intermediate nodes. -/
def Term.annotatedTypes : Term → List Ty
  | t@(.literal ..) | t@(.boolean ..) | t@(.unit) | t@(.var ..) => [t.ty]
  | t@(.call _ args _) | t@(.builtin _ _ args _) => t.ty :: args.flatMap Term.annotatedTypes
  | t@(.unary _ arg _) => t.ty :: arg.annotatedTypes
  | t@(.binary _ left right _) => t.ty :: (left.annotatedTypes ++ right.annotatedTypes)
  | t@(.branch condition yes no _) => t.ty :: (condition.annotatedTypes ++ yes.annotatedTypes ++ no.annotatedTypes)
  | t@(.pack _ scheme point) => t.ty :: (scheme.annotatedTypes ++ point.annotatedTypes)
  | t@(.letE _ value body) | t@(.unpack _ _ value body) => t.ty :: (value.annotatedTypes ++ body.annotatedTypes)

/-- A final, independently decidable endpoint/type annotation invariant. -/
def CheckedModule.TypesWellFormed (m : CheckedModule) : Prop :=
  ∀ f ∈ m.functions, f.body.ty = f.returnType ∧
    ∀ t ∈ f.returnType :: (f.params.map Prod.snd ++ f.body.annotatedTypes), t.WellFormed

instance (m : CheckedModule) : Decidable m.TypesWellFormed := by
  unfold CheckedModule.TypesWellFormed
  infer_instance

/-- The code generation boundary receives a module with this checked invariant. -/
abbrev CertifiedModule := { m : CheckedModule // m.TypesWellFormed }

/-- A failed final audit is a compiler error, never silently trusted metadata. -/
def certifyModule (m : CheckedModule) : Except Diagnostic CertifiedModule :=
  if h : m.TypesWellFormed then .ok ⟨m, h⟩
  else .error { code := "E_INTERNAL_TYPE", message := "typed IR failed final endpoint/type audit" }

end VastitasKernel
