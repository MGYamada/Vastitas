import VastitasKernel.Surface
import VastitasKernel.DispatchChecker

namespace VastitasKernel.Surface
open Checker.Internal

private def indexNames : RawIndex → List String
  | .name name => [name]
  | .base _ => []

mutual
  def typeNames : TypeExpr → List String
    | .data (.point target source) | .data (.morphism source target) => indexNames target ++ indexNames source
    | .function params result => typeListNames params ++ typeNames result
    | _ => []
  def typeListNames : TypeList → List String
    | .nil => []
    | .cons head tail => typeNames head ++ typeListNames tail
end

def freeType (bound : List String) (ty : TypeExpr) : List String :=
  (typeNames ty).filter (!bound.contains ·)

def signatureNames : List String → List Param → TypeExpr → List String
  | bound, [], result => freeType bound result
  | bound, param :: rest, result => freeType bound param.ty ++ signatureNames (param.name :: bound) rest result

-- Free names are computed with lexical binding order. A nested independent
-- lambda has its own scope and is audited separately.
mutual
  def freeExpr : List String → Expr → List String
    | bound, .variable name _ => if bound.contains name then [] else [name]
    | bound, .call name args _ =>
      (if bound.contains name then [] else [name]) ++ args.flatMap (freeExpr bound)
    | bound, .invoke callee args _ => freeExpr bound callee ++ args.flatMap (freeExpr bound)
    | _, .lambda .. => []
    | bound, .unary _ value _ => freeExpr bound value
    | bound, .binary _ left right _ | bound, .pack left right _ => freeExpr bound left ++ freeExpr bound right
    | bound, .ite condition yes no _ => freeExpr bound condition ++ freeBlock bound yes ++ freeBlock bound no
    | bound, .block body _ => freeBlock bound body
    | _, _ => []
  termination_by _ expr => (sizeOf expr, 0)
  def freeBlock (bound : List String) : Block → List String
    | .mk statements result _ => freeStatements bound statements result
  termination_by block => (sizeOf block, 0)
  def freeStatements (bound : List String) : List Stmt → Expr → List String
    | [], result => freeExpr bound result
    | .letE name annotation value _ :: rest, result =>
      (annotation.toList.flatMap (freeType bound)) ++ freeExpr bound value ++ freeStatements (name :: bound) rest result
    | .unpack value scheme point _ :: rest, result => freeExpr bound value ++ freeStatements (point :: scheme :: bound) rest result
  termination_by statements result => (sizeOf statements + sizeOf result, 1)
end

mutual
  def lambdaScopes : Expr → List (List String × Span)
    | .lambda params result body span =>
      (signatureNames [] params result ++ freeBlock (params.map (·.name)) body, span) :: blockScopes body
    | .call _ args _ => args.flatMap lambdaScopes
    | .invoke callee args _ => lambdaScopes callee ++ args.flatMap lambdaScopes
    | .unary _ value _ => lambdaScopes value
    | .binary _ left right _ | .pack left right _ => lambdaScopes left ++ lambdaScopes right
    | .ite condition yes no _ => lambdaScopes condition ++ blockScopes yes ++ blockScopes no
    | .block body _ => blockScopes body
    | _ => []
  def blockScopes : Block → List (List String × Span)
    | .mk statements result _ => statements.flatMap stmtScopes ++ lambdaScopes result
  def stmtScopes : Stmt → List (List String × Span)
    | .letE _ _ value _ | .unpack value _ _ _ => lambdaScopes value
end

def builtinNames : List String :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dimension", "int", "pair", "pair_first", "pair_second", "QQ", "CInfReal"]

def Program.globals (p : Program) : List String :=
  p.functions.map (·.name) ++ p.generics.map (·.name) ++ builtinNames

def Program.scopes (p : Program) : List (List String × Span) :=
  p.functions.flatMap (fun f => blockScopes f.body) ++ p.methods.flatMap (fun m => blockScopes m.body)

/-- Lexically free names in each independent lambda must be global definitions. -/
def CaptureFree (p : Program) : Prop :=
  ∀ scope ∈ p.scopes, ∀ name ∈ scope.1, name ∈ p.globals

instance (p : Program) : Decidable (CaptureFree p) := by
  unfold CaptureFree
  infer_instance

private def nameProblem (globals bound outer : List String) (name : String)
    (span : Span) : Option Diagnostic :=
  if name.startsWith "__vastitas_" then
    some { code := "E_RESERVED", span, message := s!"name '{name}' is reserved" }
  else if bound.contains name || globals.contains name then none
  else if outer.contains name then
    some { code := "E_CAPTURE", span, message := s!"independent lambda cannot capture '{name}'; pass it as an explicit parameter" }
  else some { code := "E_NAME", span, message := s!"undefined name '{name}'" }

-- This traversal only chooses the error location/message. Acceptance depends
-- on the separate total CaptureFree predicate, never on diagnostic fuel.
mutual
  private def expressionProblem : Nat → List String → List String → List String → Expr → Option Diagnostic
    | 0, _, _, _, _ => none
    | fuel + 1, globals, bound, outer, expr => Id.run do
      match expr with
      | .variable name span => return nameProblem globals bound outer name span
      | .call name args span =>
        if let some problem := nameProblem globals bound outer name span then return some problem
        return args.findSome? (expressionProblem fuel globals bound outer)
      | .invoke callee args _ =>
        if let some problem := expressionProblem fuel globals bound outer callee then return some problem
        return args.findSome? (expressionProblem fuel globals bound outer)
      | .lambda params result body span =>
        if let some problem := (signatureNames [] params result).findSome?
            (fun name => nameProblem globals [] (bound ++ outer) name span) then return some problem
        return blockProblem fuel globals (params.map (·.name)) (bound ++ outer) body
      | .unary _ value _ => return expressionProblem fuel globals bound outer value
      | .binary _ left right _ | .pack left right _ =>
        if let some problem := expressionProblem fuel globals bound outer left then return some problem
        return expressionProblem fuel globals bound outer right
      | .ite condition yes no _ =>
        if let some problem := expressionProblem fuel globals bound outer condition then return some problem
        if let some problem := blockProblem fuel globals bound outer yes then return some problem
        return blockProblem fuel globals bound outer no
      | .block body _ => return blockProblem fuel globals bound outer body
      | _ => return none
  private def blockProblem : Nat → List String → List String → List String → Block → Option Diagnostic
    | 0, _, _, _, _ => none
    | fuel + 1, globals, bound, outer, .mk statements result _ =>
      statementsProblem fuel globals bound outer statements result
  private def statementsProblem : Nat → List String → List String → List String → List Stmt → Expr → Option Diagnostic
    | 0, _, _, _, _, _ => none
    | fuel + 1, globals, bound, outer, [], result => expressionProblem fuel globals bound outer result
    | fuel + 1, globals, bound, outer, .letE name annotation value span :: rest, result =>
      ((annotation.toList.flatMap typeNames).findSome? (fun name => nameProblem globals bound outer name span)).orElse fun _ =>
      (expressionProblem fuel globals bound outer value).orElse fun _ =>
        statementsProblem fuel globals (name :: bound) outer rest result
    | fuel + 1, globals, bound, outer, .unpack value scheme point _ :: rest, result =>
      (expressionProblem fuel globals bound outer value).orElse fun _ =>
        statementsProblem fuel globals (point :: scheme :: bound) outer rest result
end

def captureDiagnostic (p : Program) : Diagnostic := Id.run do
  for f in p.functions ++ p.methods.map (·.toFunction) do
    if let some problem := blockProblem 8192 p.globals (f.params.map (·.name)) [] f.body then
      return problem
  for (names, span) in p.scopes do
    if let some name := names.find? (!p.globals.contains ·) then
      return {
        code := "E_CAPTURE", span
        message := s!"independent lambda cannot capture '{name}'; pass it as an explicit parameter" }
  return { code := "E_CAPTURE", message := "independent lambda has a non-global free name" }

-- The legacy path is exact only when no global function is used as a value.
mutual
  def valueNames : Expr → List String
    | .variable name _ => [name]
    | .call _ args _ => args.flatMap valueNames
    | .invoke callee args _ => valueNames callee ++ args.flatMap valueNames
    | .lambda _ _ body _ | .block body _ => blockValueNames body
    | .unary _ value _ => valueNames value
    | .binary _ left right _ | .pack left right _ => valueNames left ++ valueNames right
    | .ite condition yes no _ => valueNames condition ++ blockValueNames yes ++ blockValueNames no
    | _ => []
  def blockValueNames : Block → List String
    | .mk statements result _ => statements.flatMap stmtValueNames ++ valueNames result
  def stmtValueNames : Stmt → List String
    | .letE _ _ value _ | .unpack value _ _ _ => valueNames value
end

def Program.legacyExact (p : Program) : Option RawProgram :=
  if (p.functions.flatMap (fun f => blockValueNames f.body) ++
      p.methods.flatMap (fun m => blockValueNames m.body)).any
      (fun name => (p.functions.map (·.name) ++ p.generics.map (·.name)).contains name) then none
  else p.legacy

end VastitasKernel.Surface
