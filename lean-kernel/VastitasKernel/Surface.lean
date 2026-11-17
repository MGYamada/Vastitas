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

-- Lean derives no `DecidableEq` for nested inductive types, so the decision is
-- written out. `equalExpr` compares the constructor indices first, so it needs
-- an arm only for two equal constructors. Every constructor, body, annotation
-- and span participates in provenance.
mutual
  private def equalExpr (a b : Expr) : Decidable (a = b) :=
    if h : a.ctorIdx = b.ctorIdx then
      match a, b, h with
      | .integer a0 a1, .integer b0 b1, _ =>
        decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
      | .boolean a0 a1, .boolean b0 b1, _ =>
        decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
      | .unit a0, .unit b0, _ =>
        decidable_of_iff (a0 = b0) (by simp)
      | .variable a0 a1, .variable b0 b1, _ =>
        decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
      | .call a0 a1 a2, .call b0 b1 b2, _ =>
        let _ : Decidable (a1 = b1) := equalListExpr a1 b1
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
      | .invoke a0 a1 a2, .invoke b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := equalExpr a0 b0
        let _ : Decidable (a1 = b1) := equalListExpr a1 b1
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
      | .reference a0 a1, .reference b0 b1, _ =>
        decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
      | .lambda a0 a1 a2 a3, .lambda b0 b1 b2 b3, _ =>
        let _ : Decidable (a2 = b2) := equalBlock a2 b2
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
      | .unary a0 a1 a2, .unary b0 b1 b2, _ =>
        let _ : Decidable (a1 = b1) := equalExpr a1 b1
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
      | .binary a0 a1 a2 a3, .binary b0 b1 b2 b3, _ =>
        let _ : Decidable (a1 = b1) := equalExpr a1 b1
        let _ : Decidable (a2 = b2) := equalExpr a2 b2
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
      | .ite a0 a1 a2 a3, .ite b0 b1 b2 b3, _ =>
        let _ : Decidable (a0 = b0) := equalExpr a0 b0
        let _ : Decidable (a1 = b1) := equalBlock a1 b1
        let _ : Decidable (a2 = b2) := equalBlock a2 b2
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
      | .block a0 a1, .block b0 b1, _ =>
        let _ : Decidable (a0 = b0) := equalBlock a0 b0
        decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
      | .pack a0 a1 a2, .pack b0 b1 b2, _ =>
        let _ : Decidable (a0 = b0) := equalExpr a0 b0
        let _ : Decidable (a1 = b1) := equalExpr a1 b1
        decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
    else isFalse (fun e => h (congrArg Expr.ctorIdx e))
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

end VastitasKernel.Surface
