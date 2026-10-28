import VastitasKernel.Program
import VastitasKernel.Names
import VastitasKernel.Dispatch
import VastitasKernel.Abstract
import VastitasKernel.Contracts
import VastitasKernel.Checker

/-! Stage 1 dispatch is a typed lowering adapter. Every ordinary and
monomorphized body is checked by the independently audited core
after generic calls have been resolved by the finite dispatch checker. -/
namespace VastitasKernel.DispatchChecker
open Checker.Internal

def privatePrefix := "__vastitas_"

def sourceReserved : List String :=
  ["generic", "method", "domain", "requires", "Any", "Number", "Fn", "abstract", "type", "subtype"]

def checkSourceName (name : String) (span : Span) : CheckM Unit := do
  checkName name span
  if name.startsWith privatePrefix || sourceReserved.contains name then
    fail span "E_RESERVED" s!"'{name}' is reserved for the compiler or static dispatch"

def checkReference (name : String) (span : Span) : CheckM Unit := do
  if name.startsWith privatePrefix then
    fail span "E_RESERVED" s!"'{privatePrefix}' is reserved for compiler-generated names"

def validateIndex (index : RawIndex) (span : Span) : CheckM Unit :=
  match index with
  | .name name => checkReference name span
  | .base _ => pure ()

def validateType (ty : RawType) (span : Span) : CheckM Unit := do
  match ty with
  | .named name => checkReference name span
  | .point target source | .morphism target source =>
    validateIndex target span
    validateIndex source span
  | .pointed _ _ | .pair _ => pure ()

def checkBinder (globals : Std.HashSet String) (name : String) (span : Span) : CheckM Unit := do
  checkSourceName name span
  if globals.contains name then
    fail span "E_SHADOW" s!"binding '{name}' conflicts with a function or generic name"

mutual
  def validateExpr : Nat → Std.HashSet String → RawExpr → CheckM Unit
    | 0, _, expr => fail expr.span "E_LIMIT" "source validation exceeds the supported nesting limit"
    | fuel + 1, globals, expr => do
      match expr with
      | .integer .. | .boolean .. | .unit .. => pure ()
      | .variable name span => checkReference name span
      | .call name args span =>
        checkReference name span
        args.forM (validateExpr fuel globals)
      | .unary _ value _ => validateExpr fuel globals value
      | .binary _ left right _ | .pack left right _ =>
        validateExpr fuel globals left
        validateExpr fuel globals right
      | .ite condition yes no _ =>
        validateExpr fuel globals condition
        validateBlock fuel globals yes
        validateBlock fuel globals no
      | .block body _ => validateBlock fuel globals body
  def validateBlock : Nat → Std.HashSet String → RawBlock → CheckM Unit
    | 0, _, .mk _ _ span => fail span "E_LIMIT" "source validation exceeds the supported nesting limit"
    | fuel + 1, globals, .mk statements result _ => do
      for statement in statements do
        match statement with
        | .letE name annotation value span =>
          checkBinder globals name span
          annotation.forM (fun ty => validateType ty span)
          validateExpr fuel globals value
        | .unpack value scheme point span =>
          checkBinder globals scheme span
          checkBinder globals point span
          validateExpr fuel globals value
      validateExpr fuel globals result
end

def scalar (raw : RawType) (span : Span) : CheckM Nat :=
  match raw with
  | .named name =>
    match Dispatch.parseScalar name with
    | some code => pure code
    | none => fail span "E_TYPE" s!"dispatch domains require Nat, Int, Bool, or Unit; found {name}"
  | _ => fail span "E_TYPE" "dispatch domains require a concrete scalar type"

/-- Result annotations do not participate in the finite key nominals or selection. -/
def methodResult (raw : RawType) (span : Span) : CheckM Unit :=
  match raw with
  | .named "Nat" | .named "Int" | .named "Bool" | .named "Unit"
  | .pair "Nat" | .pair "Int" => pure ()
  | _ => fail span "E_TYPE" "method results require a concrete scalar, Pair<Nat>, or Pair<Int>"

def keyLabel (key : Dispatch.Key) : String :=
  "(" ++ String.intercalate ", " (key.map Dispatch.nominalName) ++ ")"

def monoName (method : Nat) (key : Dispatch.Key) : String :=
  (FunctionName.method method key).render

/-- The executable dispatch acceptance equation is retained as erased evidence.
It connects every selected table to the oracle's finite-selection theorem. -/
structure Family where
  nominals : Abstract.Checked
  raw : RawGeneric
  domain : List Dispatch.Key
  methods : List Dispatch.Method
  sourceMethods : List RawMethod
  contracts : List (Contracts.Contract nominals.hierarchy)
  included : contracts.all (fun contract => contract.domain.all domain.contains) = true
  checked : Dispatch.Checked
  accepted : Dispatch.checkWith nominals.hierarchy raw.params.length domain methods = .ok checked
  fulfilled : contracts.all (Contracts.satisfied sourceMethods checked) = true

abbrev Families := Std.HashMap String Family

private def requirementLabel (requirements : List Dispatch.Capability) : String :=
  if requirements.contains .hasOrder then "HasOrder"
  else if requirements.contains .hasEq then "HasEq" else ""

private def signatureLabel (nominals : Abstract.Checked) (name : String) (method : Dispatch.NormalizedMethod) : String :=
  name ++ "(" ++ String.intercalate ", " (method.selectors.map (fun id => nominals.names[id]!)) ++ ")" ++
    (if method.requirements.isEmpty then "" else s!" requires ({requirementLabel method.requirements})")

private def diagnosticCandidate (nominals : Abstract.Checked) (program : RawProgram) (id : Nat) : Option (RawMethod × Dispatch.NormalizedMethod) := do
  let raw ← program.methods[id]?
  let selectors ← raw.params.mapM fun param => match param.ty with
    | .named name => if nominals.names.contains name then some (nominals.names.idxOf name) else none
    | _ => none
  let requirements ← raw.requirements.mapM Dispatch.parseCapability
  pure (raw, { id, selectors, requirements := Dispatch.normalizeCapabilities requirements })

private def ambiguityNotes (nominals : Abstract.Checked) (program : RawProgram) (generic : RawGeneric) (ids : List Nat) : List DiagnosticNote := Id.run do
  let candidates := ids.filterMap (diagnosticCandidate nominals program)
  let mut notes := []
  for (raw, candidate) in candidates do
    let mut message := s!"candidate method `{signatureLabel nominals generic.name candidate}` declared here"
    for (_, other) in candidates do
      if candidate.id != other.id then
        let narrower := Dispatch.nominalBelow nominals.hierarchy candidate.selectors other.selectors
        let reverse := Dispatch.nominalBelow nominals.hierarchy other.selectors candidate.selectors
        let missing := other.requirements.filter (!candidate.requirements.contains ·)
        let extra := candidate.requirements.filter (!other.requirements.contains ·)
        if narrower && !reverse then message := message ++ "; has narrower selectors"
        if !narrower then message := message ++ "; selectors are not narrower in every argument"
        if !extra.isEmpty then message := message ++ s!"; has stronger requirements ({requirementLabel extra})"
        if !missing.isEmpty then message := message ++ s!"; does not require {requirementLabel missing}"
    notes := notes ++ [{ message, span := raw.span }]
  if let some (_, first) := candidates.head? then
    let mut meet := some first
    for (_, candidate) in candidates.tail do
      meet := meet.bind fun current => do
        let selectors ← (current.selectors.zip candidate.selectors).mapM fun (a, b) =>
          if nominals.hierarchy.subtype a b then some a
          else if nominals.hierarchy.subtype b a then some b else none
        pure { current with
          selectors := selectors
          requirements := Dispatch.normalizeCapabilities (current.requirements ++ candidate.requirements) }
    if let some resolving := meet then
      notes := notes ++ [{
        span := generic.span
        message := s!"help: declare `{signatureLabel nominals generic.name resolving}` to resolve this key; recheck the entire family after editing" }]
  return notes

def dispatchDiagnostic (nominals : Abstract.Checked) (program : RawProgram) (generic : RawGeneric) (error : Dispatch.Error) : Diagnostic :=
  let code := match error.code with
    | "E_DISPATCH_ARITY" => "E_ARITY"
    | "E_DISPATCH_SELECTOR" => "E_TYPE"
    | "E_DISPATCH_CAPABILITY" | "E_DISPATCH_UNREALIZABLE" => "E_CAPABILITY"
    | "E_DISPATCH_DUPLICATE_ID" | "E_DISPATCH_DUPLICATE" => "E_DUPLICATE"
    | "E_DISPATCH_LIMIT" => "E_LIMIT"
    | other => other
  let notes := if error.code == "E_DISPATCH_AMBIGUOUS" then ambiguityNotes nominals program generic error.methods
    else error.methods.filterMap fun id =>
      (program.methods[id]?).map fun method =>
        { message := s!"candidate method for generic '{generic.name}' declared here", span := method.span : DiagnosticNote }
  { code, span := generic.span
    message := s!"generic '{generic.name}': {error.message}" ++
      (error.key.map (fun key => s!" at key {keyLabel key}")).getD ""
    notes }

def prepareFamilies (program : RawProgram) : CheckM (List Family) := do
  let nominals ← Abstract.prepare program.abstractTypes program.subtypes
  let mut result := []
  for generic in program.generics do
    let base ← generic.domain.mapM (fun key => key.mapM (fun ty => scalar ty generic.span))
    let mut seen : Std.HashSet Dispatch.Key := {}
    for key in base do
      if seen.contains key then fail generic.span "E_DUPLICATE" s!"duplicate domain key {keyLabel key}"
      seen := seen.insert key
    let mut methods := []
    for (id, method) in program.methods.zipIdx.map (fun pair => (pair.2, pair.1)) do
      if method.name == generic.name then
        let selectors ← method.params.mapM fun param => Abstract.selector nominals param.ty param.span
        methodResult method.returnType method.span
        methods := methods ++ [{ id, selectors, requirements := method.requirements }]
    if generic.params.length > Limits.dispatchArity then fail generic.span "E_LIMIT" s!"dispatch key space exceeds {Limits.dispatchKeys}"
    let allKeys := Dispatch.keys nominals.hierarchy.concrete generic.params.length
    unless base.all allKeys.contains do
      fail generic.span "E_DISPATCH_DOMAIN" "domain contains a nonconcrete key or wrong arity"
    let contracts ← (program.abstractMethods.filter (·.name == generic.name)).mapM fun contract => do
      methodResult contract.returnType contract.span
      Contracts.prepare nominals generic.params.length contract
    let domain := Contracts.effectiveDomain nominals.hierarchy generic.params.length base contracts
    if included : contracts.all (fun contract => contract.domain.all domain.contains) = true then
      match accepted : Dispatch.checkWith nominals.hierarchy generic.params.length domain methods with
      | .error error => throw (dispatchDiagnostic nominals program generic error)
      | .ok checked =>
        if fulfilled : contracts.all (Contracts.satisfied program.methods checked) = true then
          result := result ++ [{
            nominals, raw := generic, domain, methods, sourceMethods := program.methods
            contracts, included, checked, accepted, fulfilled }]
        else
          let contract := contracts.find? (fun contract => !Contracts.satisfied program.methods checked contract)
          fail (contract.map (·.raw.span) |>.getD generic.span) "E_CONTRACT_RESULT"
            "selected concrete method does not satisfy the abstract contract result type"
    else fail generic.span "E_INTERNAL_DISPATCH" "contract domain union lost a key"

  pure result

def validateProgram (program : RawProgram) : CheckM Unit := do
  unless program.version == 2 || program.version == 4 do
    fail {} "E_PROTOCOL" "unsupported IR protocol version; expected 2 or 4"
  if program.version == 2 && (!program.abstractTypes.isEmpty || !program.subtypes.isEmpty || !program.abstractMethods.isEmpty) then
    fail {} "E_PROTOCOL" "abstract declarations require protocol 4"
  let mut globals : Std.HashSet String := {}
  for function in program.functions do
    checkSourceName function.name function.span
    if globals.contains function.name then fail function.span "E_DUPLICATE" s!"duplicate function '{function.name}'"
    globals := globals.insert function.name
  let mut genericNames : Std.HashSet String := {}
  for generic in program.generics do
    checkSourceName generic.name generic.span
    if generic.name == "main" then fail generic.span "E_MAIN" "main must be an ordinary fn main() -> Int"
    if globals.contains generic.name then fail generic.span "E_DUPLICATE" s!"duplicate function or generic '{generic.name}'"
    globals := globals.insert generic.name
    genericNames := genericNames.insert generic.name
  for declaration in program.abstractTypes do
    checkSourceName declaration.name declaration.span
    if globals.contains declaration.name then fail declaration.span "E_DUPLICATE" "duplicate declaration name"
    globals := globals.insert declaration.name
  for generic in program.generics do
    let mut params : Std.HashSet String := {}
    for param in generic.params do
      checkBinder globals param.name param.span
      if params.contains param.name then fail param.span "E_DUPLICATE" s!"duplicate generic parameter '{param.name}'"
      params := params.insert param.name
  for function in program.functions do
    for param in function.params do
      checkBinder globals param.name param.span
      validateType param.ty param.span
    validateType function.returnType function.span
    validateBlock Limits.sourceNesting globals function.body
  for method in program.methods do
    checkSourceName method.name method.span
    unless genericNames.contains method.name do
      fail method.span "E_NAME" s!"method refers to undeclared generic '{method.name}'"
    for param in method.params do
      checkBinder globals param.name param.span
    validateBlock Limits.sourceNesting globals method.body

  for contract in program.abstractMethods do
    checkSourceName contract.name contract.span
    unless genericNames.contains contract.name do
      fail contract.span "E_NAME" s!"abstract method refers to undeclared generic '{contract.name}'"
    let mut params : Std.HashSet String := {}
    for param in contract.params do
      checkBinder globals param.name param.span
      if params.contains param.name then fail param.span "E_DUPLICATE" "duplicate abstract method parameter"
      params := params.insert param.name

/-- A successful lookup carries the actual checked row equation. -/
structure Target (family : Family) (key : Dispatch.Key) where
  method : Nat
  admitted : key ∈ family.domain
  selected : family.checked.winner key = some method

def selectTarget (family : Family) (key : Dispatch.Key) (span : Span) : CheckM (Target family key) := do
  if admitted : key ∈ family.domain then
    match selected : family.checked.winner key with
    | none => fail span "E_INTERNAL_DISPATCH" "validated dispatch domain has no selected method"
    | some method => pure { method, admitted, selected }
  else
    fail span "E_DISPATCH_DOMAIN" s!"generic '{family.raw.name}' does not admit call key {keyLabel key}"

/-- Lowering metadata is never sent to the final core checker. In particular,
integer expressions remain unresolved until their actual expected type is known.
ResultType retains nominal object references, not just the coarse Ty. -/
structure LoweredExpr where
  raw : RawExpr
  known : Option ResultType := none
  deriving Inhabited

def LoweredExpr.infer (value : LoweredExpr) (signatures : Signatures) (ctx : Context)
    (expected : Option Ty := none) : CheckM ResultType := do
  match value.known with
  | some info =>
    let _ ← expectedResult ctx expected ⟨.var 0 info⟩ value.raw.span
    return info
  | none => return (← checkExpr Limits.bodyChecking signatures ctx value.raw expected).term.resultType

def LoweredExpr.atom (raw : RawExpr) (ctx : Context) : LoweredExpr :=
  { raw, known := match raw with
    | .boolean .. => some ⟨.bool, none⟩
    | .unit .. => some ⟨.unit, none⟩
    | .variable name _ => (ctx.find? (·.name == name)).map (·.resultType)
    | _ => none }

def scalarKey (value : ResultType) (span : Span) : CheckM Nat :=
  match value.ty with
  | .nat => pure 0 | .int => pure 1 | .bool => pure 2 | .unit => pure 3
  | ty => fail span "E_TYPE" s!"generic dispatch requires concrete scalar arguments; found {ty.label}"

def independentData : Ty → Bool
  | .nat | .int | .bool | .unit | .pair _ => true
  | _ => false

/-- Calls have an expected-type-independent result. Scalar/Pair signatures reuse
already inferred operands; geometric calls keep the core's dependent argument
substitution and fresh-object construction. Both paths retain their ResultType. -/
def lowerCall (signatures : Signatures) (ctx : Context) (name : String)
    (args : List LoweredExpr) (span : Span) : CheckM LoweredExpr := do
  let raw := RawExpr.call name (args.map (·.raw)) span
  if let some signature := signatures[name]? then
    if signature.params.all (fun p => independentData p.ty) && independentData signature.result then
      arity name (args.map (·.raw)) signature.params.length span
      for (param, arg) in signature.params.zip args do
        let _ ← arg.infer signatures ctx (some param.ty)
      return { raw, known := some ⟨signature.result, none⟩ }
  let info := (← checkExpr Limits.bodyChecking signatures ctx raw none).term.resultType
  return { raw, known := some info }

/-- Reusing a result across a block still checks its original escape boundary.
The original statements are preserved for the final independent core check. -/
def lowerBlockResult (ctx : Context) (statements : List RawStmt) (result : LoweredExpr)
    (span : Span) : CheckM LoweredExpr := do
  if let some info := result.known then checkEscape ctx ⟨.var 0 info⟩ span
  return { result with raw := .block (.mk statements result.raw span) span }

def loweredBlock (value : LoweredExpr) (span : Span) : RawBlock :=
  match value.raw with
  | .block body _ => body
  | raw => .mk [] raw span

/-- Private names never become the user-facing cycle's method names. -/
def describeDiagnostic (program : RawProgram) (diagnostic : Diagnostic) : Diagnostic := Id.run do
  let render (token : String) : String := Id.run do
    if !token.startsWith s!"{privatePrefix}m" then return token
    let parts := (token.drop (privatePrefix.length + 1)).toString.splitOn "_"
    let idText := parts.head!
    let some id := idText.toNat? | return token
    let some method := program.methods[id]? | return token
    let codes := parts.tail!
    let codes := if codes == [""] then [] else codes
    let some key := codes.mapM String.toNat? | return token
    if key.length != method.params.length || key.any (· > 3) || monoName id key != token then
      return token
    return s!"{method.name}{keyLabel key}"
  let mut message := ""
  let mut token := ""
  for char in diagnostic.message.toList do
    if char.isAlphanum || char == '_' then
      token := token.push char
    else
      message := (message ++ render token).push char
      token := ""
  return { diagnostic with message := message ++ render token }

end VastitasKernel.DispatchChecker
