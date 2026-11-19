import VastitasKernel.FiniteStaticIndex
import VastitasKernel.IndexedFunctionSource
import VastitasKernel.NamespaceChecker
import VastitasKernel.IndexedTypeAudit

set_option autoImplicit false

namespace VastitasKernel.Indexed.FunctionSource

/-- Static parameters are ordered. An object slot refers to its preceding model slot. -/
inductive IndexParam where
  | category (schema : DeclId)
  | monad (schema : DeclId)
  | monadObject (monad : Nat)
  | object (category : Nat)
  deriving Repr, Inhabited, DecidableEq, BEq

/-- A static object of the selected category, possibly acted on by T repeatedly. -/
inductive Endpoint where
  | slot (object : Nat)
  | action (input : Endpoint)
  deriving Repr, Inhabited, DecidableEq, BEq

def Endpoint.tag (category : DeclId) (objects : FiniteCategories.Table) (key : List StaticIndex) :
    Endpoint → Option String
  | .slot i => do
    let .object owner tag ← key[i]? | none
    guard (owner == category)
    return tag
  | .action e => do FiniteFunctors.image objects (← e.tag category objects key)

inductive TemplateType where
  | hom (category source target : Nat)
  | monadHom (monad : Nat) (source target : Endpoint)
  | bool
  deriving Repr, Inhabited, DecidableEq, BEq

def TemplateType.realize (t : TemplateType) (key : List StaticIndex) (env : Environment := []) : Option Core.DataType :=
  match t with
  | .bool => some (.pure .bool)
  | .hom c x y => do
    let .category cat ← key[c]? | none
    let .object cx src ← key[x]? | none
    let .object cy dst ← key[y]? | none
    guard (cx == cat && cy == cat)
    return .finite (.hom cat src dst)
  | .monadHom i x y => do
    let .monad owner ← key[i]? | none
    let (fields,m) ← FiniteSort.monad? env owner
    return .finite (.hom fields.category (← x.tag fields.category m.objects key) (← y.tag fields.category m.objects key))

/-- Lexical value slots are distinct from static binder slots. Case arms and
let expressions retain ordinary evaluation order during specialization. -/
inductive TemplateExpr where
  | variable (slot : Nat)
  | boolean (value : Bool)
  | compare (equal : Bool) (left right : TemplateExpr)
  | compose (category : Nat) (after before : TemplateExpr)
  | monadCompose (monad : Nat) (after before : TemplateExpr)
  | monadMap (monad : Nat) (arrow : TemplateExpr)
  | component (monad object : Nat) (multiplication : Bool)
  | branch (condition yes no : TemplateExpr)
  | letE (value body : TemplateExpr)
  deriving Inhabited

private def TemplateExpr.generatedLets : TemplateExpr → Nat
  | .variable _ | .boolean _ | .component .. => 0
  | .compare _ a b => a.generatedLets + b.generatedLets
  | .monadMap _ f => 1 + f.generatedLets
  | .compose _ g f | .monadCompose _ g f => 2 + g.generatedLets + f.generatedLets
  | .branch c a b => c.generatedLets + a.generatedLets + b.generatedLets
  | .letE a b => 1 + a.generatedLets + b.generatedLets

structure FiniteTemplate where
  binders : List IndexParam
  inputs : List TemplateType
  result : TemplateType
  body : TemplateExpr
  references : List Source.Reference
  span : Span
  deriving Inhabited

structure ForwardMethod where
  span : Span
  callee : Source.Path
  deriving Inhabited

namespace FiniteTemplate

private structure Bindings (α : Type) where
  ordered : Array α := #[]
  names : Std.HashMap String (Nat × α) := {}

private def Bindings.push {α : Type} (s : Bindings α) (name : String) (value : α) : Bindings α :=
  ⟨s.ordered.push value, s.names.insert name (s.ordered.size, value)⟩

private abbrev Slots := Bindings IndexParam
private abbrev Locals := Bindings TemplateType
private abbrev Typed := TemplateType × TemplateExpr

private def binderList (index : Namespace.Indexed) (env : Core.Declarations)
    (scope : Namespace.Scope) (source : List StaticBinder) : Namespace.Result (Slots × List Source.Reference) := do
  let mut slots : Slots := {}
  let mut refs := []
  for b in source do
    let (name, span) := match b with
      | .category n _ s | .object n _ s | .monadObject n _ s => (n,s)
    let _ ← Namespace.binder index scope name span
    if slots.names.contains name then Namespace.problem span "E_DUPLICATE" "duplicate finite index parameter"
    let sort ← match b with
      | .category _ schema _ => do
        let found ← Namespace.resolve index scope schema.path schema.span
        unless found.kind == .indexedDeclaration do Namespace.problem schema.span "E_CATEGORY" "expected a finite schema"
        let kind ← match lookup env.indexed found.owner with
          | some .categorySchema => pure (IndexParam.category found.owner)
          | some .monadSchema => pure (IndexParam.monad found.owner)
          | _ => Namespace.problem schema.span "E_CATEGORY" "expected a finite category or Monad schema"
        refs := ⟨scope, schema, found⟩ :: refs
        pure kind
      | .monadObject _ parent _ => do
        let some (i, .monad _) := slots.names[parent]?
          | Namespace.problem span "E_MONAD" "Obj<M::category> requires an earlier Monad parameter"
        pure (.monadObject i)
      | .object _ parent _ => do
        let some (i, .category _) := slots.names[parent]?
          | Namespace.problem span "E_CATEGORY" "Obj requires an earlier category parameter"
        pure (.object i)
    slots := slots.push name sort
  return (slots,refs.reverse)

private def slot (slots : Slots) (p : Source.Path) : Namespace.Result (Nat × IndexParam) := do
  let [name] := p.path | Namespace.problem p.span "E_TYPE" "expected a static index parameter"
  let some found := slots.names[name]? | Namespace.problem p.span "E_NAME" s!"unbound static index parameter '{name}'"
  return found

private def monadEndpoint (slots : Slots) (model : String) (index : Nat) (path : Source.Path) :
    Namespace.Result Endpoint := do
  if path.path.length > 2 * Limits.typeNesting + 1 then
    Namespace.problem path.span "E_LIMIT" "Monad object action exceeds the type nesting limit"
  parse path.path
where
  parse : List String → Namespace.Result Endpoint
    | [name] => do
      let some (i,.monadObject parent) := slots.names[name]?
        | Namespace.problem path.span "E_TYPE" "expected an object of the Monad category"
      unless parent == index do Namespace.problem path.span "E_TYPE" "object belongs to a different Monad parameter"
      return .slot i
    | m :: "T<>" :: rest => do
      unless m == model do Namespace.problem path.span "E_TYPE" "object action requires the same Monad parameter"
      return .action (← parse rest)
    | _ => Namespace.problem path.span "E_TYPE" "expected a static object or a finite Monad object action"

private def typeOf (slots : Slots) (t : FnType) (span : Span) : Namespace.Result TemplateType := do
  match t with
  | .data (.pure .bool) => return .bool
  | .data (.finiteHom cat src dst) => do
    if let [model, "category"] := cat.path then
      let some (i,.monad _) := slots.names[model]?
        | Namespace.problem cat.span "E_MONAD" "expected a Monad category projection"
      return .monadHom i (← monadEndpoint slots model i src) (← monadEndpoint slots model i dst)
    let (c, .category _) ← slot slots cat | Namespace.problem cat.span "E_TYPE" "Hom requires a category parameter"
    let endpoint (p : Source.Path) := do
      let (x, .object owner) ← slot slots p | Namespace.problem p.span "E_TYPE" "Hom requires an object parameter"
      unless owner == c do Namespace.problem p.span "E_TYPE" "Hom endpoint belongs to a different category parameter"
      return x
    return .hom c (← endpoint src) (← endpoint dst)
  | _ => Namespace.problem span "E_TYPE" "expected a Hom or Bool type in this finite template"

private def bindLocal (index : Namespace.Indexed) (scope : Namespace.Scope) (slots : Slots) (locals : Locals)
    (name : String) (span : Span) : Namespace.Result Unit := do
  let _ ← Namespace.binder index scope name span
  if slots.names.contains name || locals.names.contains name then
    Namespace.problem span "E_DUPLICATE" "a finite function binding cannot shadow a parameter or a local"

private def lookupExpr (slots : Slots) (path : Source.Path) (args : List Expr) (span : Span)
    (visit : Expr → Namespace.Result Typed) : Namespace.Result Typed := do
  match path.path with
  | [model, "category", "composition"] =>
    let some (m,.monad _) := slots.names[model]? | Namespace.problem path.span "E_MONAD" "expected a Monad category"
    let [after,before] := args | Namespace.problem span "E_ARITY" "composition takes two arrows"
    let (.monadHom a y z,g) ← visit after | Namespace.problem after.span "E_TYPE" "expected a Monad-category Hom"
    let (.monadHom b x y',f) ← visit before | Namespace.problem before.span "E_TYPE" "expected a Monad-category Hom"
    unless a == m && b == m && y == y' do Namespace.problem span "E_TYPE" "the Monad category and middle endpoints must agree"
    return (.monadHom m x z,.monadCompose m g f)
  | [model,field] =>
    match slots.names[model]? with
    | some (m,.monad _) =>
      if field == "arrows" then
        let [arg] := args | Namespace.problem span "E_ARITY" "the arrow map takes one Hom"
        let (.monadHom a x y,f) ← visit arg | Namespace.problem arg.span "E_TYPE" "expected a Monad-category Hom"
        unless a == m do Namespace.problem span "E_TYPE" "arrow belongs to a different Monad category"
        return (.monadHom m (.action x) (.action y),.monadMap m f)
      unless field == "unit" || field == "multiplication" do Namespace.problem path.span "E_MONAD" "unknown Monad table projection"
      let [.variable object pos] := args | Namespace.problem span "E_TYPE" "a component takes one static object parameter"
      let some (x,.monadObject parent) := slots.names[object]? | Namespace.problem pos "E_TYPE" "expected a static Monad object parameter"
      unless parent == m do Namespace.problem pos "E_TYPE" "object belongs to a different Monad parameter"
      let tx := Endpoint.action (.slot x)
      let mul := field == "multiplication"
      return (.monadHom m (if mul then .action tx else .slot x) tx, .component m x mul)
    | some (c,.category _) =>
      unless field == "composition" do Namespace.problem path.span "E_CATEGORY" "expected a category composition table"
      let [after,before] := args | Namespace.problem span "E_ARITY" "composition takes two arrows"
      let (.hom ca y z,g) ← visit after | Namespace.problem after.span "E_TYPE" "expected a Hom after arrow"
      let (.hom cb x y',f) ← visit before | Namespace.problem before.span "E_TYPE" "expected a Hom before arrow"
      unless ca == c && cb == c && y == y' do Namespace.problem span "E_TYPE" "the symbolic Hom category and middle endpoints must agree"
      return (.hom c x z,.compose c g f)
    | _ => Namespace.problem path.span "E_CATEGORY" "projection requires a finite model parameter"
  | _ => Namespace.problem path.span "E_CATEGORY" "expected a finite table projection"

mutual
  private def expression : Nat → Namespace.Indexed → Namespace.Scope → Slots → Locals → Expr → Namespace.Result Typed
    | 0, _, _, _, _, e => Namespace.problem e.span "E_LIMIT" "finite function exceeds the body checking limit"
    | fuel+1, index, scope, slots, locals, e => do
      let visit := expression fuel index scope slots locals
      match e with
      | .variable name span =>
        let some (i,t) := locals.names[name]? | Namespace.problem span "E_NAME" s!"unknown finite function value '{name}'"
        return (t,.variable i)
      | .boolean x _ => return (.bool,.boolean x)
      | .binary op a b span =>
        unless op == "==" || op == "!=" do Namespace.problem span "E_OPERATOR" "expected finite equality"
        let (ta, a) ← visit a
        let (tb, b) ← visit b
        unless ta == tb do Namespace.problem span "E_TYPE" "finite comparison requires identical symbolic types"
        return (.bool,.compare (op == "==") a b)
      | .finiteLookup path args span => lookupExpr slots path args span visit
      | .branch cond yes no span =>
        let (.bool,test) ← visit cond | Namespace.problem cond.span "E_TYPE" "branch condition must be Bool"
        let (ty,y) ← block fuel index scope slots locals yes
        let (tn,n) ← block fuel index scope slots locals no
        unless ty == tn do Namespace.problem span "E_TYPE" "branch arms have different symbolic result types"
        return (ty,.branch test y n)
      | .block b _ => block fuel index scope slots locals b
      | _ => Namespace.problem e.span "E_TYPE" "unsupported expression in finite function template"

  private def block : Nat → Namespace.Indexed → Namespace.Scope → Slots → Locals → Block → Namespace.Result Typed
    | 0, _, _, _, _, .mk _ _ span => Namespace.problem span "E_LIMIT" "finite function exceeds the body checking limit"
    | fuel+1, index, scope, slots, initial, .mk statements last _ => do
      let mut locals := initial
      let mut values := []
      -- Each preceding statement consumes one unit on the path to the
      -- expression, including the final expression of the block.
      if statements.length + 1 > fuel then
        Namespace.problem last.span "E_LIMIT" "finite function exceeds the body checking limit"
      for (stmt, i) in statements.zipIdx do
        match stmt with
        | .letE name annotation e span =>
          bindLocal index scope slots locals name span
          let (t, val) ← expression (fuel - (i+1)) index scope slots locals e
          if let some explicit := annotation then
            unless (← typeOf slots explicit span) == t do Namespace.problem span "E_TYPE" "wrong symbolic let annotation"
          values := val :: values
          locals := locals.push name t
        | .unpack _ _ _ span => Namespace.problem span "E_TYPE" "a finite arrow cannot be unpacked"
      let (t,e) ← expression (fuel - (statements.length+1)) index scope slots locals last
      return (t,values.foldl (fun body value => .letE value body) e)
end

/-- The body is checked while all model and endpoint variables are distinct
symbolic slots, even when no concrete instance inhabits a binder's schema. -/
def check (index : Namespace.Indexed) (env : Core.Declarations) (owner : DeclId)
    (fn : Function) : Namespace.Result FiniteTemplate := do
  let (slots,refs) ← binderList index env owner.scope fn.finiteBinders
  let mut locals : Locals := {}
  for p in fn.params do
    bindLocal index owner.scope slots locals p.name p.span
    locals := locals.push p.name (← typeOf slots p.type p.span)
  let result ← typeOf slots fn.result fn.span
  let (actual,body) ← block Limits.bodyChecking index owner.scope slots locals fn.body
  if body.generatedLets > Limits.generatedLets then
    Namespace.problem fn.span "E_LIMIT" "finite function exceeds the generated-let budget"
  unless actual == result do Namespace.problem fn.span "E_TYPE" "finite function body has the wrong symbolic result type"
  return ⟨slots.ordered.toList, locals.ordered.toList, result, body, refs, fn.span⟩

/-- A forwarding overload evaluates its declared nullary Hom producers
once in written parameter order, then calls the represented method of the
same family and static substitution. Validate it even without any callers. -/
def checkForwarder (index : Namespace.Indexed) (env : Core.Declarations) (owner : DeclId)
    (primary : Function) (t : FiniteTemplate) (fn : Function) :
    Namespace.Result (List Bool × ForwardMethod × List Source.Reference) := do
  unless fn.isPublic == primary.isPublic do
    Namespace.problem fn.span "E_OWNER" "all finite methods of one family must have the same visibility"
  let (slots,refs) ← binderList index env owner.scope fn.finiteBinders
  unless slots.ordered.toList == t.binders && fn.params.length == t.inputs.length do
    Namespace.problem fn.span "E_TYPE" "finite forwarding method requires the same model binders and arity"
  unless (← typeOf slots fn.result fn.span) == t.result do
    Namespace.problem fn.span "E_TYPE" "finite forwarding method changes the symbolic result"
  let .mk [] (.finiteCall callee indices args _) _ := fn.body
    | Namespace.problem fn.span "E_TYPE" "finite forwarding body must call the represented method with explicit indices"
  let binderNames := fn.finiteBinders.map fun
    | .category n .. | .object n .. | .monadObject n .. => [n]
  unless indices.map (·.path) == binderNames && args.length == fn.params.length do
    Namespace.problem callee.span "E_TYPE" "finite forwarding must preserve static indices and argument order"
  let selected ← Namespace.resolve index owner.scope callee.path callee.span
  unless selected.kind == .function && selected.owner == owner do
    Namespace.problem callee.span "E_OWNER" "finite forwarding must select the represented method of this family"
  let mut locals : Locals := {}
  let mut mask := []
  for ((p,expected),arg) in (fn.params.zip t.inputs).zip args do
    bindLocal index owner.scope slots locals p.name p.span
    let (invoked,ty) ← match p.type with
      | .function (.function .nil (.data ty@(.finiteHom ..))) => pure (true,FnType.data ty)
      | ty@(.data _) => pure (false,ty)
      | _ => Namespace.problem p.span "E_TYPE" "finite forwarding expects a capture-free nullary Fn returning Hom"
    unless (← typeOf slots ty p.span) == expected do
      Namespace.problem p.span "E_TYPE" "finite forwarding parameter changes the represented type"
    let matchesParam := match invoked, arg with
      | true, .call path [] _ => path.path == [p.name]
      | false, .variable name _ => name == p.name
      | _, _ => false
    unless matchesParam do
      Namespace.problem arg.span "E_TYPE" "forward each parameter in order, calling each declared producer exactly once"
    locals := locals.push p.name expected
    mask := invoked :: mask
  unless mask.contains true do Namespace.problem fn.span "E_TYPE" "finite forwarding requires a callable parameter"
  return (mask.reverse, ⟨fn.span,callee⟩, refs)

def validKey (t : FiniteTemplate) (env : Environment) (key : List StaticIndex) : Bool :=
  let bySlot := key.toArray
  t.binders.length == key.length && (t.binders.zip key).all fun
    | (.category schema, .category owner) =>
      match lookup env owner with | some (.finiteCategory s _) => s == schema | _ => false
    | (.monad schema, .monad owner) =>
      match lookup env owner with | some (.finiteMonad s _) => s == schema | _ => false
    | (.monadObject i, .object owner name) => Id.run do
      let some (.monad monad) := bySlot[i]? | return false
      let some (.finiteMonad _ fields) := lookup env monad | return false
      let some (.finiteCategory _ graph) := lookup env fields.category | return false
      return fields.category == owner && (FiniteTables.carrier env graph.objects).any (·.contains name)
    | (.object c, .object owner name) =>
      bySlot[c]? == some (.category owner) && match lookup env owner with
        | some (.finiteCategory _ fields) => (FiniteTables.carrier env fields.objects).any (·.contains name)
        | _ => false
    | _ => false

private abbrev Emit := StateT Nat Option

private def fresh : Emit Nat := do
  let n ← get
  set (n+1)
  return n

private def emit (env : Core.Declarations) (key : List StaticIndex) (locals : Array Core.Parameter) :
    TemplateExpr → Emit Core.Term
  | .variable i => do
    let param ← liftM locals[i]?
    return .variable param.symbol param.result
  | .boolean b => return .boolean b
  | .compare eq a b => do
    return .binary (if eq then .eq else .ne) (← emit env key locals a) (← emit env key locals b) ⟨.pure .bool, none⟩
  | .branch condition yes no => do
    let test ← emit env key locals condition
    let y ← emit env key locals yes
    return .branch test y (← emit env key locals no) y.result
  | .letE value body => do
    let v ← emit env key locals value
    let s ← fresh
    return .letE s v (← emit env key (locals.push ⟨s,v.result⟩) body)
  | .component i x mul => do
    let some (.monad owner) := key[i]? | failure
    let (fields,m) ← liftM (FiniteSort.monad? env.indexed owner)
    let some (.object category tag) := key[x]? | failure
    guard (category == fields.category)
    let tx ← liftM (FiniteFunctors.image m.objects tag)
    let source ← if mul then liftM (FiniteFunctors.image m.objects tx) else pure tag
    let arrow ← liftM (FiniteFunctors.image (if mul then m.multiplication else m.unit) tag)
    return .finiteTag (.hom category source tx) arrow
  | .monadMap i input => do
    let some (.monad owner) := key[i]? | failure
    let f ← emit env key locals input
    let .finite t := f.result.type | failure
    let (table,out,_) ← liftM (FiniteSort.monadMap? env.indexed owner t)
    let symbol ← fresh
    return .letE symbol f (.finiteLookup ⟨table,some owner,[t],out⟩ [symbol])
  | .monadCompose i after before => do
    let some (.monad owner) := key[i]? | failure
    let some (.finiteMonad _ fields) := lookup env.indexed owner | failure
    let a ← emit env key locals after
    let b ← emit env key locals before
    let .finite ta := a.result.type | failure
    let .finite tb := b.result.type | failure
    let (table,out,_) ← liftM (FiniteSort.composition? env.indexed fields.category ta tb)
    let i ← fresh
    let j ← fresh
    return .letE i a (.letE j b (.finiteLookup ⟨table,some fields.category,[ta,tb],out⟩ [i,j]))
  | .compose c after before => do
    let some (.category owner) := key[c]? | failure
    let a ← emit env key locals after
    let b ← emit env key locals before
    let .finite ta := a.result.type | failure
    let .finite tb := b.result.type | failure
    let (table, result, _) ← liftM (FiniteSort.composition? env.indexed owner ta tb)
    let i ← fresh
    let j ← fresh
    return .letE i a (.letE j b (.finiteLookup ⟨table,some owner,[ta,tb],result⟩ [i,j]))

/-- The parameter symbols are supplied by the ordinary function compiler.
Each Hom index is substituted by its nominal model and two endpoint tags. -/
def signature (t : FiniteTemplate) (key : List StaticIndex) (symbols : List Nat) (env : Environment := []) :
    Option (List Core.Parameter × Core.DataType) := do
  guard (symbols.length == t.inputs.length)
  let params ← (symbols.zip t.inputs).mapM fun (s,ty) => do
    return (⟨s,⟨← ty.realize key env, none⟩⟩ : Core.Parameter)
  return (params, ← t.result.realize key env)

/-- All successful specializations carry the correspondence between their
static key, concrete signature and independently checked first-order Core. -/
structure Specialization (t : FiniteTemplate) (env : Core.Declarations) (key : List StaticIndex)
    (symbols : List Nat) where
  params : List Core.Parameter
  result : Core.DataType
  term : Core.Term
  keyValid : t.validKey env.indexed key = true
  signatureExact : t.signature key symbols env.indexed = some (params,result)
  parametersValid : Core.Typing.ParametersValid env [] params
  resultExact : term.result.type = result
  typed : Core.Typing.HasType env {} params term

def specialize (t : FiniteTemplate) (env : Core.Declarations) (key : List StaticIndex)
    (symbols : List Nat) : Namespace.Result (Specialization t env key symbols) := do
  if valid : t.validKey env.indexed key = true then
    match sig : t.signature key symbols env.indexed with
    | none => Namespace.problem t.span "E_TYPE" "invalid finite function signature instantiation"
    | some (params,result) =>
      let some (term, _) := (emit env key params.toArray t.body).run (symbols.foldl max 0 + 1)
        | Namespace.problem t.span "E_TYPE" "cannot instantiate the finite function body"
      if ok : Core.Typing.ParametersValid env [] params ∧ term.result.type = result ∧
             Core.Typing.HasType env {} params term then
        return ⟨params, result, term, valid, sig, ok.1, ok.2.1, ok.2.2⟩
      else Namespace.problem t.span "E_TYPE" "finite function specialization failed Core typing"
  else Namespace.problem t.span "E_TYPE" "invalid static category or object substitution"

def instantiate (t : FiniteTemplate) (env : Core.Declarations) (key : List StaticIndex)
    (symbols : List Nat) : Namespace.Result (List Core.Parameter × Core.DataType × Core.Term) := do
  let i ← t.specialize env key symbols
  return (i.params, i.result, i.term)

end FiniteTemplate
end VastitasKernel.Indexed.FunctionSource
