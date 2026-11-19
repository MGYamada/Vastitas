import VastitasKernel.IndexedSource
import VastitasKernel.NamespaceChecker

namespace VastitasKernel.Indexed.Source

abbrev ResolveM := StateT (List Reference) Namespace.Result

def resolveId (p : Namespace.Indexed) (scope : Namespace.Scope) (path : Path) : ResolveM DeclId := do
  let target ← Namespace.resolve p scope path.path path.span
  if target.kind != .indexedDeclaration then
    Namespace.problem path.span "E_TYPE" "expected an indexed declaration"
  modify (⟨scope, path, target⟩ :: ·)
  return target.owner

/-- Source fields keyed by the full identity of their *instance*, before
walking declarations. This index cannot discover an instance by spelling. -/
inductive InstanceFields where
  | category (graph : GraphFields Path)
  | opposite (base : Path)
  | functor (maps : FunctorFields Path)
  | iso (fields : IsoFields Path)
  | transformation (fields : NatTransFields Path)
  | monad (fields : MonadFields Path)
  | kleisli (monad : Path)

abbrev GraphSources := Std.HashMap DeclId InstanceFields

def graphSources (declarations : List (DeclId × Declaration)) : GraphSources :=
  declarations.foldl (init := {}) fun index (owner, d) => match d.body with
    | .finiteOpposite _ base => index.insert owner (.opposite base)
    | .finiteCategory _ graph => index.insert owner (.category graph)
    | .finiteMonad _ m => index.insert owner (.monad m)
    | .finiteKleisli _ _ m => index.insert owner (.kleisli m)
    | .finiteIso _ i => index.insert owner (.iso i)
    | .finiteNatTrans _ n => index.insert owner (.transformation n)
    | .finiteFunctor _ maps => index.insert owner (.functor maps)
    | _ => index

def InstanceFields.projections : InstanceFields → List (String × Path)
  | .opposite base => ["objects", "arrows", "source", "target", "identities", "composition"].map fun name => (name, base)
  | .category g => [("objects", g.objects), ("arrows", g.arrows), ("source", g.src),
      ("target", g.dst), ("identities", g.ids), ("composition", g.comp)]
  | .monad m => [("unit", m.unit), ("multiplication", m.multiplication),
      ("category", m.category), ("arrows", m.functor)]
  | .kleisli m => [("unit", m), ("multiplication", m), ("category", m), ("arrows", m)]
  | .iso i => [("source", i.source), ("target", i.target), ("forward", i.forward), ("inverse", i.inverse)]
  | .transformation n => [("components", n.components)]
  | .functor f => [("objects", f.objects), ("arrows", f.arrows)]

def InstanceFields.unknown (fields : InstanceFields) (name : String) : String × String :=
  match fields with
  | .category _ | .opposite _ => ("E_CATEGORY", s!"unknown finite category projection '{name}'")
  | .monad _ => ("E_MONAD", s!"unknown finite Monad projection '{name}'")
  | .kleisli _ => ("E_KLEISLI", s!"unknown Kleisli view projection '{name}'")
  | .iso _ => ("E_ISO", s!"unknown finite isomorphism projection '{name}'")
  | .transformation _ => ("E_NAT_TRANS", s!"unknown finite natural transformation projection '{name}'")
  | .functor _ => ("E_FUNCTOR", s!"unknown finite functor projection '{name}'")

abbrev ProjectionKey := DeclId × String
structure Projected where
  id : DeclId
  depth : Nat
  reversedComposition : Bool := false

abbrev ProjectionCache := Std.HashMap ProjectionKey Projected

/-- Discover a projection only when the visible prefix resolves to an actual
named instance. Module paths (including private or cyclic reexports) remain
subject to the ordinary namespace checker. -/
private def projected? (index : Namespace.Indexed) (graphs : GraphSources)
    (here : Namespace.Scope) (path : Path) : ResolveM (Option (ProjectionKey × Path)) := do
  let field :: owner :: rest := path.path.reverse | return none
  let base : Path := ⟨(owner :: rest).reverse, path.span⟩
  let .ok target := Namespace.resolve index here base.path base.span | return none
  if target.kind != .indexedDeclaration then return none
  let some graph := graphs[target.owner]? | return none
  let some (_, next) := graph.projections.find? (·.1 == field)
    | let (code, message) := graph.unknown field
      Namespace.problem path.span code message
  modify (⟨here, base, target⟩ :: ·)
  return some ((target.owner, field), next)

/-- Expand each associated field once, in its declaring scope. A chain
stores its checked name-resolution edges once, rather than copying a trace
for every use in a table or instance. -/
def buildProjectionCache (index : Namespace.Indexed) (graphs : GraphSources)
    (decls : List (DeclId × Declaration)) : ResolveM ProjectionCache := do
  let work : StateT ProjectionCache ResolveM Unit := do
    for (owner, _) in decls do
      let some fields := graphs[owner]? | continue
      for (field, path) in fields.projections do
        let _ ← visit Limits.namespaceResolution (owner, field) path {}
  return (← work {}).2
where
  visit : Nat → ProjectionKey → Path → Std.HashSet ProjectionKey → StateT ProjectionCache ResolveM Projected
    | 0, _, path, _ => Namespace.problem path.span "E_LIMIT" "finite projection chain exceeds the resolution budget"
    | fuel + 1, key, path, active => do
      if let some found := (← get)[key]? then
        if found.depth > fuel + 1 then
          Namespace.problem path.span "E_LIMIT" "finite projection chain exceeds the resolution budget"
        return found
      if active.contains key then Namespace.problem path.span "E_CYCLE" "cyclic finite category projection"
      -- Each nominal hop resolves in its declaring scope and remains in the
      -- reference audit, even when the selected table or Monad is private.
      let next? ← do
        match graphs[key.1]? with
        | some (.opposite _) =>
          let owner ← liftM (resolveId index key.1.scope path)
          let field := match key.2 with
            | "source" => "target"
            | "target" => "source"
            | other => other
          let some target := graphs[owner]?
            | Namespace.problem path.span "E_CATEGORY" "Opposite requires a named category"
          match target with
          | .category _ | .opposite _ =>
            let some (_, slot) := target.projections.find? (·.1 == field)
              | Namespace.problem path.span "E_CATEGORY" "unknown Opposite projection"
            pure (some ((owner, field), slot))
          | _ => Namespace.problem path.span "E_CATEGORY" "Opposite requires a named category"
        | some (.kleisli _) =>
          let owner ← liftM (resolveId index key.1.scope path)
          let some (model@(.monad _)) := graphs[owner]?
            | Namespace.problem path.span "E_KLEISLI" "view requires a named finite Monad"
          let some (_, slot) := model.projections.find? (·.1 == key.2)
            | Namespace.problem path.span "E_KLEISLI" "unknown selected Monad projection"
          pure (some ((owner, key.2), slot))
        | some (.monad _) =>
          if key.2 == "category" then pure none
          else if key.2 == "arrows" then
            let owner ← liftM (resolveId index key.1.scope path)
            let some (.functor maps) := graphs[owner]?
              | Namespace.problem path.span "E_MONAD" "expected the selected finite endofunctor"
            pure (some ((owner, "arrows"), maps.arrows))
          else
            let owner ← liftM (resolveId index key.1.scope path)
            let some (.transformation trans) := graphs[owner]?
              | Namespace.problem path.span "E_MONAD" s!"{key.2} must name a finite natural transformation"
            pure (some ((owner, "components"), trans.components))
        | _ => liftM (projected? index graphs key.1.scope path)
      let resolved : Projected ← match next? with
        | some (next, nextPath) => do
            let found ← visit fuel next nextPath (active.insert key)
            let flips := key.2 == "composition" && match graphs[key.1]? with
              | some (.opposite _) => true
              | _ => false
            pure ⟨found.id, found.depth + 1, if flips then !found.reversedComposition else found.reversedComposition⟩
        | none => pure ⟨← liftM (resolveId index key.1.scope path), 1, false⟩
      modify (·.insert key resolved)
      return resolved

/-- Resolve a finite signature or graph slot to a nominal ID in the same
environment as the instance's laws. Caller scope only selects the instance.
Its field never opens an editable namespace. -/
def resolveFinitePath (index : Namespace.Indexed) (graphs : GraphSources)
    (cache : ProjectionCache) (scope : Namespace.Scope) (path : Path) : ResolveM DeclId := do
  if let some (key, _) ← projected? index graphs scope path then
    let some target := cache[key]? | Namespace.problem path.span "E_CATEGORY" "unresolved finite category field"
    if target.reversedComposition then
      Namespace.problem path.span "E_CATEGORY" "a reversed composition requires lookup through its named view"
    return target.id
  resolveId index scope path

end VastitasKernel.Indexed.Source
