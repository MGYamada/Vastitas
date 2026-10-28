import VastitasKernel.Program
import VastitasKernel.Names

/-! Protocol-2 surface syntax. Function values never enter the preserved core. -/
namespace VastitasKernel.Surface

mutual
  inductive TypeExpr where
    | data (ty : RawType)
    | function (params : TypeList) (result : TypeExpr)
    deriving Repr, DecidableEq, Inhabited
  inductive TypeList where
    | nil
    | cons (head : TypeExpr) (tail : TypeList)
    deriving Repr, DecidableEq, Inhabited
end

def TypeList.toList : TypeList → List TypeExpr
  | .nil => []
  | .cons head tail => head :: tail.toList

instance : Coe (List TypeExpr) TypeList := ⟨fun types => types.foldr TypeList.cons .nil⟩

def TypeExpr.labelAt : Nat → TypeExpr → String
  | 0, _ => "…"
  | _ + 1, .data (.named name) => name
  | _ + 1, .data (.pair element) => s!"Pair<{element}>"
  | _ + 1, .data (.point ..) => "Point"
  | _ + 1, .data (.morphism ..) => "Morphism"
  | _ + 1, .data (.pointed ..) => "Pointed"
  | fuel + 1, .function params result =>
    "Fn<" ++ (match params.toList with
      | [param] => labelAt fuel param
      | _ => "(" ++ String.intercalate ", " (params.toList.map (labelAt fuel)) ++ ")") ++
      ", " ++ labelAt fuel result ++ ">"

def TypeExpr.label (ty : TypeExpr) : String := ty.labelAt Limits.typeNesting

-- Signature shape and declared syntax depth are separate checks. A synthetic
-- function wrapper must not consume the declared type's nesting allowance.
mutual
  def TypeExpr.callableData : TypeExpr → Bool
    | .data (.named name) => ["Nat", "Int", "Bool", "Unit"].contains name
    | .function params result => params.callableData && result.callableData
    | _ => false
  def TypeList.callableData : TypeList → Bool
    | .nil => true
    | .cons head tail => head.callableData && tail.callableData
end

def TypeExpr.withinDepth : Nat → TypeExpr → Bool
  | 0, _ => false
  | _ + 1, .data _ => true
  | fuel + 1, .function params result =>
    params.toList.all (withinDepth fuel) && withinDepth fuel result

def TypeExpr.core : TypeExpr → RawType
  | .data ty => ty
  | .function .. => .named "Unit"

def TypeExpr.isFunction : TypeExpr → Bool
  | .function .. => true
  | _ => false

structure Param where
  name : String
  ty : TypeExpr
  span : Span
  deriving Repr, DecidableEq, Inhabited

mutual
  inductive Expr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | call (callee : String) (args : List Expr) (span : Span)
    | invoke (callee : Expr) (args : List Expr) (span : Span)
    | reference (name : FunctionName) (span : Span) -- backend-only lifted lambda
    | lambda (params : List Param) (result : TypeExpr) (body : Block) (span : Span)
    | unary (op : String) (operand : Expr) (span : Span)
    | binary (op : String) (left right : Expr) (span : Span)
    | ite (condition : Expr) (yes no : Block) (span : Span)
    | block (body : Block) (span : Span)
    | pack (scheme point : Expr) (span : Span)
    deriving Repr, Inhabited
  inductive Stmt where
    | letE (name : String) (annotation : Option TypeExpr) (value : Expr) (span : Span)
    | unpack (value : Expr) (scheme point : String) (span : Span)
    deriving Repr, Inhabited
  inductive Block where
    | mk (statements : List Stmt) (result : Expr) (span : Span)
    deriving Repr, Inhabited
end

-- Nested mutual syntax requires an explicit structural equality decision.
-- Every constructor, body, annotation and span participates in provenance.
mutual
  private def equalExpr (a b : Expr) : Decidable (a = b) :=
    match a, b with
    | .integer a0 a1, .integer b0 b1 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .integer _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .unit _ => isFalse (by intro h; cases h)
    | .integer _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .block _ _ => isFalse (by intro h; cases h)
    | .integer _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .boolean a0 a1, .boolean b0 b1 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .boolean _ _, .unit _ => isFalse (by intro h; cases h)
    | .boolean _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .block _ _ => isFalse (by intro h; cases h)
    | .boolean _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .integer _ _ => isFalse (by intro h; cases h)
    | .unit _, .boolean _ _ => isFalse (by intro h; cases h)
    | .unit a0, .unit b0 =>
      decidable_of_iff (a0 = b0) (by simp)
    | .unit _, .variable _ _ => isFalse (by intro h; cases h)
    | .unit _, .call _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .reference _ _ => isFalse (by intro h; cases h)
    | .unit _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .unit _, .block _ _ => isFalse (by intro h; cases h)
    | .unit _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .unit _ => isFalse (by intro h; cases h)
    | .variable a0 a1, .variable b0 b1 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .variable _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .block _ _ => isFalse (by intro h; cases h)
    | .variable _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .call _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .call a0 a1 a2, .call b0 b1 b2 =>
      let _ : Decidable (a1 = b1) := equalListExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
    | .call _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .call _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .invoke a0 a1 a2, .invoke b0 b1 b2 =>
      let _ : Decidable (a0 = b0) := equalExpr a0 b0
      let _ : Decidable (a1 = b1) := equalListExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
    | .invoke _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .invoke _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .unit _ => isFalse (by intro h; cases h)
    | .reference _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .reference a0 a1, .reference b0 b1 =>
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .reference _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .block _ _ => isFalse (by intro h; cases h)
    | .reference _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .lambda a0 a1 a2 a3, .lambda b0 b1 b2 b3 =>
      let _ : Decidable (a2 = b2) := equalBlock a2 b2
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
    | .lambda _ _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .lambda _ _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .unary a0 a1 a2, .unary b0 b1 b2 =>
      let _ : Decidable (a1 = b1) := equalExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
    | .unary _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .unary _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .binary a0 a1 a2 a3, .binary b0 b1 b2 b3 =>
      let _ : Decidable (a1 = b1) := equalExpr a1 b1
      let _ : Decidable (a2 = b2) := equalExpr a2 b2
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
    | .binary _ _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .ite a0 a1 a2 a3, .ite b0 b1 b2 b3 =>
      let _ : Decidable (a0 = b0) := equalExpr a0 b0
      let _ : Decidable (a1 = b1) := equalBlock a1 b1
      let _ : Decidable (a2 = b2) := equalBlock a2 b2
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
    | .ite _ _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .block _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .block _ _, .unit _ => isFalse (by intro h; cases h)
    | .block _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .block _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .block _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .block _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .block a0 a1, .block b0 b1 =>
      let _ : Decidable (a0 = b0) := equalBlock a0 b0
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
    | .block _ _, .pack _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .integer _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .boolean _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .unit _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .variable _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .call _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .invoke _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .reference _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .lambda _ _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .unary _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .binary _ _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .ite _ _ _ _ => isFalse (by intro h; cases h)
    | .pack _ _ _, .block _ _ => isFalse (by intro h; cases h)
    | .pack a0 a1 a2, .pack b0 b1 b2 =>
      let _ : Decidable (a0 = b0) := equalExpr a0 b0
      let _ : Decidable (a1 = b1) := equalExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  termination_by sizeOf a
  private def equalStmt (a b : Stmt) : Decidable (a = b) :=
    match a, b with
    | .letE a0 a1 a2 a3, .letE b0 b1 b2 b3 =>
      let _ : Decidable (a2 = b2) := equalExpr a2 b2
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
    | .letE _ _ _ _, .unpack _ _ _ _ => isFalse (by intro h; cases h)
    | .unpack _ _ _ _, .letE _ _ _ _ => isFalse (by intro h; cases h)
    | .unpack a0 a1 a2 a3, .unpack b0 b1 b2 b3 =>
      let _ : Decidable (a0 = b0) := equalExpr a0 b0
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  termination_by sizeOf a
  private def equalBlock (a b : Block) : Decidable (a = b) :=
    match a, b with
    | .mk a0 a1 a2, .mk b0 b1 b2 =>
      let _ : Decidable (a0 = b0) := equalListStmt a0 b0
      let _ : Decidable (a1 = b1) := equalExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  termination_by sizeOf a
  private def equalListExpr (a b : (List Expr)) : Decidable (a = b) :=
    match a, b with
    | .nil, .nil =>
      isTrue rfl
    | .nil, .cons _ _ => isFalse (by intro h; cases h)
    | .cons _ _, .nil => isFalse (by intro h; cases h)
    | .cons a0 a1, .cons b0 b1 =>
      let _ : Decidable (a0 = b0) := equalExpr a0 b0
      let _ : Decidable (a1 = b1) := equalListExpr a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  termination_by sizeOf a
  private def equalListStmt (a b : (List Stmt)) : Decidable (a = b) :=
    match a, b with
    | .nil, .nil =>
      isTrue rfl
    | .nil, .cons _ _ => isFalse (by intro h; cases h)
    | .cons _ _, .nil => isFalse (by intro h; cases h)
    | .cons a0 a1, .cons b0 b1 =>
      let _ : Decidable (a0 = b0) := equalStmt a0 b0
      let _ : Decidable (a1 = b1) := equalListStmt a1 b1
      decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  termination_by sizeOf a
end

instance : DecidableEq Expr := equalExpr
instance : DecidableEq Stmt := equalStmt
instance : DecidableEq Block := equalBlock

def Expr.span : Expr → Span
  | .integer _ s | .boolean _ s | .unit s | .variable _ s | .call _ _ s
  | .reference _ s | .invoke _ _ s | .lambda _ _ _ s | .unary _ _ s | .binary _ _ _ s
  | .ite _ _ _ s | .block _ s | .pack _ _ s => s

structure Function where
  name : String
  params : List Param
  result : TypeExpr
  body : Block
  span : Span
  deriving Repr, DecidableEq, Inhabited

def Function.type (f : Function) : TypeExpr := .function (f.params.map (·.ty)) f.result

/-- The source name is retained for diagnostics; internal lookup uses `id`. -/
structure Definition extends Function where
  id : FunctionName
  deriving Repr, DecidableEq, Inhabited

def Definition.type (f : Definition) : TypeExpr := f.toFunction.type

def Definition.label (f : Definition) : String :=
  match f.id with
  | .source _ => f.name
  | .lambda _ => s!"lambda at {f.span.line}:{f.span.column}"
  | .method _ key => f.name ++ "(" ++ String.intercalate ", " (key.map Dispatch.nominalName) ++ ")"

structure Method extends Function where
  requirements : List String
  deriving Repr, DecidableEq, Inhabited

structure Program where
  version : Nat
  file : String
  functions : List Function
  generics : List RawGeneric
  methods : List Method
  abstractTypes : List RawAbstractType := []
  subtypes : List RawSubtype := []
  abstractMethods : List RawAbstractMethod := []
  deriving Repr, Inhabited

-- Compatibility conversion for first-order clients and fixtures. It is not a
-- separate acceptance or lowering path.
def TypeExpr.legacy : TypeExpr → Option RawType
  | .data ty => some ty
  | _ => none

def Param.legacy (p : Param) : Option RawParam := do
  pure { name := p.name, ty := ← p.ty.legacy, span := p.span }

mutual
  def Expr.legacy : Expr → Option RawExpr
    | .integer value span => some (.integer value span)
    | .boolean value span => some (.boolean value span)
    | .unit span => some (.unit span)
    | .variable name span => some (.variable name span)
    | .call name args span => do pure (.call name (← args.mapM Expr.legacy) span)
    | .unary op value span => do pure (.unary op (← value.legacy) span)
    | .binary op left right span => do pure (.binary op (← left.legacy) (← right.legacy) span)
    | .ite condition yes no span => do pure (.ite (← condition.legacy) (← yes.legacy) (← no.legacy) span)
    | .block body span => do pure (.block (← body.legacy) span)
    | .pack scheme point span => do pure (.pack (← scheme.legacy) (← point.legacy) span)
    | _ => none
  def Stmt.legacy : Stmt → Option RawStmt
    | .letE name annotation value span => do
      let annotation ← match annotation with
        | none => some none
        | some ty => some <$> ty.legacy
      pure (.letE name annotation (← value.legacy) span)
    | .unpack value scheme point span => do pure (.unpack (← value.legacy) scheme point span)
  def Block.legacy : Block → Option RawBlock
    | .mk statements result span => do
      pure (.mk (← statements.mapM Stmt.legacy) (← result.legacy) span)
end

def Function.legacy (f : Function) : Option RawFunction := do
  pure {
    name := f.name, params := ← f.params.mapM Param.legacy
    returnType := ← f.result.legacy, body := ← f.body.legacy, span := f.span }

def Program.legacy (p : Program) : Option RawProgram := do
  let methods ← p.methods.mapM fun m => do
    let f ← m.toFunction.legacy
    pure {
      name := f.name, params := f.params, returnType := f.returnType,
      body := f.body, span := f.span, requirements := m.requirements : RawMethod }
  pure {
    version := p.version, file := p.file, functions := ← p.functions.mapM Function.legacy,
    generics := p.generics, methods, abstractTypes := p.abstractTypes, subtypes := p.subtypes, abstractMethods := p.abstractMethods }

mutual
  def Expr.ofRaw : RawExpr → Expr
    | .integer value span => .integer value span
    | .boolean value span => .boolean value span
    | .unit span => .unit span
    | .variable name span => .variable name span
    | .call name args span => .call name (args.map Expr.ofRaw) span
    | .unary op value span => .unary op (Expr.ofRaw value) span
    | .binary op left right span => .binary op (Expr.ofRaw left) (Expr.ofRaw right) span
    | .ite condition yes no span => .ite (Expr.ofRaw condition) (Block.ofRaw yes) (Block.ofRaw no) span
    | .block body span => .block (Block.ofRaw body) span
    | .pack scheme point span => .pack (Expr.ofRaw scheme) (Expr.ofRaw point) span
  def Stmt.ofRaw : RawStmt → Stmt
    | .letE name annotation value span => .letE name (annotation.map TypeExpr.data) (Expr.ofRaw value) span
    | .unpack value scheme point span => .unpack (Expr.ofRaw value) scheme point span
  def Block.ofRaw : RawBlock → Block
    | .mk statements result span => .mk (statements.map Stmt.ofRaw) (Expr.ofRaw result) span
end

def Function.ofRaw (f : RawFunction) : Function := {
  name := f.name, params := f.params.map fun p => { name := p.name, ty := .data p.ty, span := p.span }
  result := .data f.returnType, body := Block.ofRaw f.body, span := f.span }

/-- First-order callers enter the same surface lowering and independent audits. -/
def Program.ofRaw (p : RawProgram) : Program := {
  version := p.version, file := p.file, functions := p.functions.map Function.ofRaw
  generics := p.generics
  methods := p.methods.map fun m => { toFunction := Function.ofRaw { name := m.name, params := m.params, returnType := m.returnType, body := m.body, span := m.span }, requirements := m.requirements }
  abstractTypes := p.abstractTypes, subtypes := p.subtypes, abstractMethods := p.abstractMethods }

end VastitasKernel.Surface
