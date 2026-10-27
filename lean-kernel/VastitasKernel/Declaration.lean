import VastitasKernel.Checker

/-! Independent source-declaration correspondence. Source annotation spellings
and index lookup are retained, separately from checked-term type safety. -/
namespace VastitasKernel.Declaration

open Checker.Internal

inductive Base : String → BaseKind → Prop
  | qq : Base "QQ" .qq
  | cinfReal : Base "CInfReal" .cinfReal

inductive Index (ctx : Context) : RawIndex → ObjectRef → Prop
  | base {ring base} : Base ring base → Index ctx (.base ring) (.base base)
  | name {name binding ref} : ctx.find? (fun b => b.name == name) = some binding →
      binding.objectRef = some ref → Index ctx (.name name) ref

inductive TypeAnnotation (ctx : Context) : RawType → Ty → Prop
  | nat : TypeAnnotation ctx (.named "Nat") .nat
  | int : TypeAnnotation ctx (.named "Int") .int
  | bool : TypeAnnotation ctx (.named "Bool") .bool
  | unit : TypeAnnotation ctx (.named "Unit") .unit
  | pairNat : TypeAnnotation ctx (.pair "Nat") (.pair .nat)
  | pairInt : TypeAnnotation ctx (.pair "Int") (.pair .int)
  | scheme : TypeAnnotation ctx (.named "Scheme") (.object .qq)
  | cinfScheme : TypeAnnotation ctx (.named "CInfScheme") (.object .cinfReal)
  | point {rawTarget rawSource target source} :
      Index ctx rawTarget target → Index ctx rawSource source →
      TypeAnnotation ctx (.point rawTarget rawSource) (.point target source)
  | morphism {rawSource rawTarget source target} :
      Index ctx rawSource source → Index ctx rawTarget target →
      TypeAnnotation ctx (.morphism rawSource rawTarget) (.morphism source target)
  | pointed {setting ring base} : Base ring base → setting = base.settingName →
      TypeAnnotation ctx (.pointed setting ring) (.pointed base)

structure Parameter (ctx : Context) (raw : RawParam) (binding : Binding) : Prop where
  name : binding.name = raw.name
  annotation : TypeAnnotation ctx raw.ty binding.ty
  objectRef : binding.objectRef =
    match binding.ty with
    | .object base => some (.local base binding.symbol)
    | _ => none

/-- The final context is the initial context followed by the resolved parameters. -/
inductive Parameters : Context → List RawParam → Context → Prop
  | nil (ctx) : Parameters ctx [] ctx
  | cons {ctx raw raws binding final} : Parameter ctx raw binding →
      Parameters (ctx ++ [binding]) raws final → Parameters ctx (raw :: raws) final

structure Signature (raw : RawFunction) (checked : Checker.Internal.Signature) : Prop where
  source : checked.raw = raw
  parameters : Parameters [] raw.params checked.params
  result : TypeAnnotation checked.params raw.returnType checked.result

end VastitasKernel.Declaration
