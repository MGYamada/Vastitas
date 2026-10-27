import VastitasKernel.Checker
import VastitasKernel.Declaration

/-! Source correspondence is distinct from type safety. These relations state
which checked syntax represents a raw expression under explicit name tables.
They do not define correspondence as success of the executable elaborator. -/
namespace VastitasKernel.Elaboration

open Checker.Internal

inductive Ring : RawExpr → BaseKind → Prop
  | qq (span) : Ring (.variable "QQ" span) .qq
  | cinfReal (span) : Ring (.variable "CInfReal" span) .cinfReal

def Annotation (ctx : Context) (annotation : Option RawType) (ty : Ty) : Prop :=
  match annotation with
  | none => True
  | some raw => Declaration.TypeAnnotation ctx raw ty

def Scope (ctx : Context) (value : Term) : Prop :=
  value.ty.Scoped (ctx.flatMap fun binding => binding.objectRef.toList ++ binding.ty.refs)

mutual
  inductive Expr (signatures : Signatures) : Context → RawExpr → Term → Prop
    | integer {value span ty n} : value.toNat? = some n →
        (ty = .nat ∨ ty = .int) → Expr signatures ctx (.integer value span) (.literal ty n)
    | boolean (value span) : Expr signatures ctx (.boolean value span) (.boolean value)
    | unit (span) : Expr signatures ctx (.unit span) .unit
    | variable {name span binding} : ctx.find? (fun b => b.name == name) = some binding →
        Expr signatures ctx (.variable name span) (.var binding.symbol binding.resultType)
    | neg {raw span value} : Expr signatures ctx raw value →
        Expr signatures ctx (.unary "-" raw span) (.unary .neg value .int)
    | not {raw span value} : Expr signatures ctx raw value →
        Expr signatures ctx (.unary "!" raw span) (.unary .not value .bool)
    | binary {rawOp op left right span a b ty} : BinaryOp.ofString? rawOp = some op →
        Expr signatures ctx left a → Expr signatures ctx right b →
        Expr signatures ctx (.binary rawOp left right span) (.binary op a b ty)
    | branch {condition yes no span c y n result} :
        Expr signatures ctx condition c → Block signatures ctx yes y → Block signatures ctx no n →
        Expr signatures ctx (.ite condition yes no span) (.branch c y n result)
    | block {raw span value} : Block signatures ctx raw value →
        Expr signatures ctx (.block raw span) value
    | pack {scheme point span x p base} : Expr signatures ctx scheme x →
        Expr signatures ctx point p →
        Expr signatures ctx (.pack scheme point span) (.pack base x p)
    | call {name args span value} : Call signatures ctx name args value →
        Expr signatures ctx (.call name args span) value

  inductive Block (signatures : Signatures) : Context → RawBlock → Term → Prop
    | mk {statements result span value} : Statements signatures ctx statements result value → Scope ctx value →
        Block signatures ctx (.mk statements result span) value

  inductive Statements (signatures : Signatures) : Context → List RawStmt → RawExpr → Term → Prop
    | nil {raw value} : Expr signatures ctx raw value → Statements signatures ctx [] raw value
    | letE {name annotation raw span rest result symbol value body} :
        Annotation ctx annotation value.ty → Expr signatures ctx raw value →
        Statements signatures
          ({ name, symbol, ty := value.ty, objectRef := value.resultType.objectRef } :: ctx)
          rest result body →
        Statements signatures ctx (.letE name annotation raw span :: rest) result (.letE symbol value body)
    | unpack {raw scheme point span rest result value base objectSymbol pointSymbol body} :
        Expr signatures ctx raw value → value.ty = .pointed base →
        Statements signatures
          ({ name := point, symbol := pointSymbol, ty := unpackedPointType base objectSymbol } ::
           { name := scheme, symbol := objectSymbol, ty := .object base,
             objectRef := some (.local base objectSymbol) } :: ctx) rest result body →
        Statements signatures ctx (.unpack raw scheme point span :: rest) result
          (.unpack objectSymbol pointSymbol value body)

  inductive Arguments (signatures : Signatures) : Context → List RawExpr → List Term → Prop
    | nil : Arguments signatures ctx [] []
    | cons {raw raws value values} : Expr signatures ctx raw value → Arguments signatures ctx raws values →
        Arguments signatures ctx (raw :: raws) (value :: values)

  inductive Call (signatures : Signatures) : Context → String → List RawExpr → Term → Prop
    | int {raw value} : Expr signatures ctx raw value →
        Call signatures ctx "int" [raw] (.builtin .int [value] ⟨.int, none⟩)
    | affine {ring base raw value result} : Ring ring base → Expr signatures ctx raw value →
        Call signatures ctx "Affine" [ring, raw] (.builtin (.affine base) [value] result)
    | base {ring base result} : Ring ring base →
        Call signatures ctx "Base" [ring] (.builtin (.base base) [] result)
    | origin {raw value result} : Expr signatures ctx raw value →
        Call signatures ctx "origin" [raw] (.builtin .origin [value] result)
    | identity {raw value result} : Expr signatures ctx raw value →
        Call signatures ctx "id" [raw] (.builtin .identity [value] result)
    | dimension {raw value result} : Expr signatures ctx raw value →
        Call signatures ctx "dimension" [raw] (.builtin .dimension [value] result)
    | compose {left right a b result} : Expr signatures ctx left a → Expr signatures ctx right b →
        Call signatures ctx "compose" [left, right] (.builtin .compose [a, b] result)
    | apply {left right a b result} : Expr signatures ctx left a → Expr signatures ctx right b →
        Call signatures ctx "apply" [left, right] (.builtin .apply [a, b] result)
    | function {name raws signature values substitutions objectRef} : signatures[name]? = some signature →
        Arguments signatures ctx raws values →
        Call signatures ctx name raws (.call signature.id values substitutions
          ⟨signature.result.rename substitutions, objectRef⟩)
    | pair {left right a b element} : Expr signatures ctx left a → Expr signatures ctx right b →
        Call signatures ctx "pair" [left, right] (.builtin (.pair element) [a, b] ⟨.pair element, none⟩)
    | pairFirst {raw value element} : Expr signatures ctx raw value →
        Call signatures ctx "pair_first" [raw] (.builtin (.pairFirst element) [value] ⟨element.ty, none⟩)
    | pairSecond {raw value element} : Expr signatures ctx raw value →
        Call signatures ctx "pair_second" [raw] (.builtin (.pairSecond element) [value] ⟨element.ty, none⟩)
end

/-- Parameters retain both the executable symbol and their nominal index. -/
inductive Parameters : List Binding → List CheckedParam → Prop
  | nil : Parameters [] []
  | cons {binding param source checked} :
      binding.symbol = param.symbol → binding.ty = param.ty →
      binding.objectRef = param.resultType.objectRef → Parameters source checked →
      Parameters (binding :: source) (param :: checked)

/-- The signature retains the original declaration; the function body relates
its raw names and blocks to the emitted symbols and checked syntax. -/
structure Function (signatures : Signatures) (signature : Signature)
    (checked : CheckedFunction) : Prop where
  id : checked.id = signature.id
  name : checked.name = signature.raw.name
  parameters : Parameters signature.params checked.params
  result : checked.returnType = signature.result
  body : Block signatures signature.params signature.raw.body checked.body

end VastitasKernel.Elaboration
