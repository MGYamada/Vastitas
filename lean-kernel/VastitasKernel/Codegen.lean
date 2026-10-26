import VastitasKernel.Core

/-!
Hygienic Lean generation from the checked Stage 0 term language. Nothing from
the user's source is inserted as an identifier or executable Lean fragment.
The emitted module imports only the runtime, not this compiler module.
-/
namespace VastitasKernel.Codegen

private def renderType : Ty → String
  | .nat => "Nat"
  | .int => "Int"
  | .bool => "Bool"
  | .unit => "Unit"
  | .object _ => "VastitasKernel.Runtime.Object"
  | .point _ _ => "VastitasKernel.Runtime.Point"
  | .morphism _ _ => "VastitasKernel.Runtime.Morphism"
  | .pointed _ => "VastitasKernel.Runtime.Pointed"

private def renderBase : BaseKind → String
  | .qq => "VastitasKernel.Runtime.Base.qq"
  | .cinfReal => "VastitasKernel.Runtime.Base.cinfReal"

private def variableName (symbol : Nat) : String := s!"v_{symbol}"
private def functionName (symbol : Nat) : String := s!"f_{symbol}"

private def application (name : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (name :: args) ++ ")"

private def renderBuiltin (name : String) (base : Option BaseKind)
    (args : List String) : Except String String :=
  match name, base, args with
  | "Affine", some base, [n] =>
      .ok (application "VastitasKernel.Runtime.affine" [renderBase base, n])
  | "Base", some base, [] =>
      .ok (application "VastitasKernel.Runtime.baseObject" [renderBase base])
  | "origin", _, [x] => .ok (application "VastitasKernel.Runtime.origin" [x])
  | "id", _, [x] => .ok (application "VastitasKernel.Runtime.idMap" [x])
  | "compose", _, [g, f] =>
      .ok (application "VastitasKernel.Runtime.composeMap" [g, f])
  | "apply", _, [f, p] =>
      .ok (application "VastitasKernel.Runtime.applyMap" [f, p])
  | "dimension", _, [x] => .ok s!"({x}).dimension"
  | _, _, _ => .error "invalid builtin in checked term"

private def renderUnary (op operand : String) : Except String String :=
  match op with
  | "-" => .ok s!"(-{operand})"
  | "!" => .ok s!"(!{operand})"
  | _ => .error "invalid unary operation in checked term"

private def renderBinary (op left right : String) : Except String String :=
  match op with
  | "+" | "-" | "*" | "==" | "!=" | "&&" | "||" =>
      .ok s!"({left} {op} {right})"
  | "<" | "<=" | ">" | ">=" =>
      .ok s!"(decide ({left} {op} {right}))"
  | _ => .error "invalid binary operation in checked term"

private partial def renderTerm : Term → Except String String
  | .literal ty value => do
      unless !value.isEmpty && value.toList.all Char.isDigit do
        throw "invalid integer literal in checked term"
      unless ty == .nat || ty == .int do
        throw "non-integer type on checked integer literal"
      return s!"({value} : {renderType ty})"
  | .boolean value => .ok (if value then "true" else "false")
  | .unit => .ok "()"
  | .var symbol _ => .ok (variableName symbol)
  | .call functionId args _ => do
      return application (functionName functionId) (← args.mapM renderTerm)
  | .builtin name base args _ => do
      renderBuiltin name base (← args.mapM renderTerm)
  | .unary op arg _ => do renderUnary op (← renderTerm arg)
  | .binary op left right _ => do
      renderBinary op (← renderTerm left) (← renderTerm right)
  | .branch condition yes no _ => do
      return s!"(if {← renderTerm condition} then {← renderTerm yes} else {← renderTerm no})"
  | .pack _ scheme point => do
      return application "VastitasKernel.Runtime.Pointed.mk"
        [← renderTerm scheme, ← renderTerm point]
  | .letE symbol value body => do
      return s!"(let {variableName symbol} := {← renderTerm value}; {← renderTerm body})"
  | .unpack objectSymbol pointSymbol value body => do
      let package := s!"packed_{objectSymbol}"
      return s!"(let {package} := {← renderTerm value}; let {variableName objectSymbol} := {package}.scheme; let {variableName pointSymbol} := {package}.point; {← renderTerm body})"

private def renderFunction (function : CheckedFunction) : Except String String := do
  let parameters := function.params.map fun (symbol, ty) =>
    s!"({variableName symbol} : {renderType ty})"
  let parameterText := if parameters.isEmpty then "" else " " ++ String.intercalate " " parameters
  return s!"def {functionName function.id}{parameterText} : {renderType function.returnType} :=\n  {← renderTerm function.body}\n"

/-- Emit a standalone Lean module, with an IO boundary only for the entrypoint. -/
def generate (certified : CertifiedModule) : Except String String := do
  let module := certified.val
  let some mainId := module.mainId
    | throw "native compilation requires fn main() -> Int"
  let functions ← module.functions.mapM renderFunction
  return "import VastitasKernel.Runtime\n\nset_option maxRecDepth 32768\nset_option maxHeartbeats 2000000\nset_option linter.unusedVariables false\n\nnamespace VastitasGenerated\n\n" ++
    String.intercalate "\n" functions ++
    "\nend VastitasGenerated\n\ndef main : IO Unit :=\n  IO.println (" ++
    "VastitasGenerated." ++ functionName mainId ++ ")\n"

end VastitasKernel.Codegen
