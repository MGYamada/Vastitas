import VastitasKernel.Program

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

def TypeExpr.label (ty : TypeExpr) : String := ty.labelAt 64

def TypeExpr.callableDataAt : Nat → TypeExpr → Bool
  | 0, _ => false
  | _ + 1, .data (.named name) => ["Nat", "Int", "Bool", "Unit"].contains name
  | fuel + 1, .function params result => params.toList.all (callableDataAt fuel) && callableDataAt fuel result
  | _, _ => false

def TypeExpr.callableData (ty : TypeExpr) : Bool := ty.callableDataAt 64

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
  deriving Repr, Inhabited

mutual
  inductive Expr where
    | integer (value : String) (span : Span)
    | boolean (value : Bool) (span : Span)
    | unit (span : Span)
    | variable (name : String) (span : Span)
    | call (callee : String) (args : List Expr) (span : Span)
    | invoke (callee : Expr) (args : List Expr) (span : Span)
    | reference (name : String) (span : Span) -- backend-only lifted lambda
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
  deriving Repr, Inhabited

def Function.type (f : Function) : TypeExpr := .function (f.params.map (·.ty)) f.result

structure Method extends Function where
  requirements : List String
  deriving Repr, Inhabited

structure Program where
  version : Nat
  file : String
  functions : List Function
  generics : List RawGeneric
  methods : List Method
  deriving Repr, Inhabited

-- An exact adapter for unchanged first-order syntax keeps its old acceptance
-- path, budgets and proofs intact. Function syntax always goes through Stage 1b.
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
    generics := p.generics, methods }

end VastitasKernel.Surface
