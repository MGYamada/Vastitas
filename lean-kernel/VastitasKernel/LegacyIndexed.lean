import VastitasKernel.IndexedTypeAudit
import VastitasKernel.TypeAudit

/-! Compatibility translation for the closed pre-protocol-7 geometric profile.
All geometric cases live at this adapter boundary; indexed acceptance and
native lowering use declaration contracts. These reserved IDs are constructed
here and cannot be selected by a source filename or an import spelling. -/
namespace VastitasKernel.LegacyIndexed

def id (name : String) : Indexed.DeclId :=
  ⟨⟨⟨"vastitas:compat:2-6", "legacy-profile", "1"⟩, []⟩, name⟩

def marker : BaseKind → Indexed.DeclId
  | .qq => id "QQ" | .cinfReal => id "CInfReal"

def implementation : BaseKind → Indexed.DeclId
  | .qq => id "AffineQQ" | .cinfReal => id "AffineCInf"

def baseObject : BaseKind → Indexed.DeclId
  | .qq => id "BaseQQ" | .cinfReal => id "BaseCInf"

/-- Legacy Scheme/CInfScheme each admit exactly one implementation. This is
the explicit finite compatibility profile, not a universal class assumption. -/
def objectType (base : BaseKind) : Indexed.ObjectType := ⟨implementation base, marker base⟩

def ref : ObjectRef → Indexed.ObjectRef
  | .base base => .global (baseObject base)
  | .local base serial => .local (objectType base) serial

def package (base : BaseKind) : Indexed.Application :=
  ⟨id "Pointed", [.domain (implementation base), .marker (marker base)]⟩

def dataType : Ty → Indexed.Core.DataType
  | .nat => .pure .nat | .int => .pure .int | .bool => .pure .bool | .unit => .pure .unit
  | .pair element => .pure (.pair element)
  | .object base => .object (objectType base)
  | .point target source => .indexed ⟨id "Point", [.object (ref target), .object (ref source)]⟩
  | .morphism source target => .indexed ⟨id "Morphism", [.object (ref source), .object (ref target)]⟩
  | .pointed base => .package (package base)

def result (result : ResultType) : Indexed.Core.Result := ⟨dataType result.ty, result.objectRef.map ref⟩

def primitiveId (name : String) (base : BaseKind) : Indexed.DeclId :=
  id (name ++ match base with | .qq => "QQ" | .cinfReal => "CInf")

def declarations : Indexed.Core.Declarations := {
  indexed := [.qq, .cinfReal].flatMap (fun base =>
    [⟨marker base, .marker⟩,
     ⟨implementation base, .implementation (marker base) .affineDescriptor [.origin, .dimension]⟩,
     ⟨baseObject base, .global (implementation base)⟩]) ++
    [⟨id "Objects", .classification [] [implementation .qq, implementation .cinfReal]⟩,
     ⟨id "Point", .family ⟨[.object (id "Objects"), .object (id "Objects")], [.sameBase 0 1], .point⟩⟩,
     ⟨id "Morphism", .family ⟨[.object (id "Objects"), .object (id "Objects")], [.sameBase 0 1], .morphism⟩⟩]
  packages := [⟨id "Pointed", [.qq, .cinfReal].map fun base =>
    ⟨objectType base, [⟨id "Point", [.witness, .global (baseObject base)]⟩]⟩⟩]
  primitives := [.qq, .cinfReal].flatMap (fun base =>
    [⟨primitiveId "affine" base, .descriptor (implementation base)⟩,
     ⟨primitiveId "base" base, .global (baseObject base)⟩,
     ⟨primitiveId "origin" base, .origin (objectType base) (id "Point") (baseObject base)⟩,
     ⟨primitiveId "identity" base, .identity (objectType base) (id "Morphism")⟩,
     ⟨primitiveId "dimension" base, .dimension (objectType base)⟩]) ++
    [⟨id "compose", .compose (id "Morphism")⟩, ⟨id "apply", .apply (id "Morphism") (id "Point")⟩] }

private def invalid {α : Type} : Except Diagnostic α :=
  .error { code := "E_INTERNAL_TYPE", message := "invalid legacy Core shape in indexed compatibility adapter" }

private def unaryPrimitive (name : String) (arguments : List Term) : Except Diagnostic Indexed.DeclId :=
  match arguments with
  | [argument] => match argument.ty with | .object base => .ok (primitiveId name base) | _ => invalid
  | _ => invalid

def term : Term → Except Diagnostic Indexed.Core.Term
  | .literal .nat value => .ok (.natural value)
  | .literal .int value => .ok (.integer (Int.ofNat value))
  | .literal _ _ => invalid
  | .boolean value => .ok (.boolean value)
  | .unit => .ok .unit
  | .var symbol annotation => .ok (.variable symbol (result annotation))
  | .unary operator value type => do return .unary operator (← term value) ⟨dataType type, none⟩
  | .binary operator left right type => do return .binary operator (← term left) (← term right) ⟨dataType type, none⟩
  | .call function arguments substitution annotation => do
      return .call function (← arguments.mapM term) (substitution.map fun (a, b) => (ref a, ref b)) (result annotation)
  | .builtin op arguments annotation => do
      let values ← arguments.mapM term
      match op, values with
      | .int, [value] => return .natToInt value
      | .pair element, [first, second] => return .pair element first second
      | .pairFirst element, [value] => return .project element true value
      | .pairSecond element, [value] => return .project element false value
      | .affine base, _ => return .primitive (primitiveId "affine" base) values (result annotation)
      | .base base, _ => return .primitive (primitiveId "base" base) values (result annotation)
      | .origin, _ => return .primitive (← unaryPrimitive "origin" arguments) values (result annotation)
      | .identity, _ => return .primitive (← unaryPrimitive "identity" arguments) values (result annotation)
      | .dimension, _ => return .primitive (← unaryPrimitive "dimension" arguments) values (result annotation)
      | .compose, _ => return .primitive (id "compose") values (result annotation)
      | .apply, _ => return .primitive (id "apply") values (result annotation)
      | _, _ => invalid
  | .branch condition yes no annotation => do
      return .branch (← term condition) (← term yes) (← term no) (result annotation)
  | .pack base witness point => do return .pack (package base) (← term witness) [← term point]
  | .unpack objectSymbol pointSymbol package body => do
      return .unpack objectSymbol [pointSymbol] (← term package) (← term body)
  | .letE symbol value body => do return .letE symbol (← term value) (← term body)

def function (function : CheckedFunction) : Except Diagnostic Indexed.Core.Function := do
  return {
    id := function.id
    definition := id s!"function_{function.id}"
    parameters := function.params.map fun parameter => ⟨parameter.symbol, result parameter.resultType⟩
    returnType := dataType function.returnType
    body := ← term function.body
    span := function.span }

def module (module : CheckedModule) : Except Diagnostic Indexed.Core.Module := do
  return ⟨declarations, ← module.functions.mapM function, module.mainId⟩

/-- Both legacy structural acceptance and the translated common Core audit
are required; an annotation-only CertifiedModule never bypasses either. -/
def check (input : CheckedModule) (requireMain : Bool := false) :
    Except Diagnostic (Indexed.Core.Typing.CheckedModule requireMain) := do
  unless Dependency.auditModule input && Typing.auditModule input do
    throw { code := "E_INTERNAL_TYPE", message := "legacy Core failed independent typing or dependency audit" }
  Indexed.Core.Typing.checkModule (← module input) requireMain

end VastitasKernel.LegacyIndexed
