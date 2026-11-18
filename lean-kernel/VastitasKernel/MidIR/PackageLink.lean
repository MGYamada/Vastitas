import VastitasKernel.MidIR.Checked

set_option autoImplicit false

namespace VastitasKernel.MidIR.PackageLink

open Indexed

abbrev Request := ResourceSource.Wire.CheckedInput

abbrev core {json main} (req : Request json main) := req.checked.pureProgram.compiled.core.module

/-- Static references can name a family even when the callee ignores the
argument. Recover them from the same executable pass as the direct calls. -/
abbrev StaticEdges := Std.HashMap FunctionSource.Compiler.Key (List DeclId)

def staticEdges {json main} (req : Request json main) : Option StaticEdges := do
  let src := req.checked.pureProgram
  let pass := src.executable.lowered
  let keys := Std.HashSet.ofList pass.origins.toList
  let mut edges : StaticEdges := {}
  for ref in pass.familyRefs do
    let caller ← src.compiler.input.prepared[ref.caller.definition]?
    guard (keys.contains ref.caller && caller.definition.bodyScope == ref.scope)
    edges := edges.alter ref.caller (fun ids => some (ref.target.owner :: ids.getD []))
  for use in pass.staticUses do
    let caller ← use.caller
    let .concrete defId := use.target.name | none
    let target ← src.compiler.input.prepared[defId]?
    guard (keys.contains caller)
    edges := edges.alter caller (fun ids => some (target.definition.owner :: ids.getD []))
  return edges

/-- Start from every root function and every family edited or explicitly
sealed by the root. Reaching one specialization retains its whole emitted
family, including methods whose definition and edit owners differ. -/
private def closure (m : Core.Module) (root : String) (rootEdited : Std.HashSet DeclId)
    (origins : Array FunctionSource.Compiler.Key) (edges : StaticEdges) :
    Std.HashSet Nat := Id.run do
  let functions := m.functions.toArray
  let mut siblings : Std.HashMap DeclId (List Nat) := {}
  let mut work := []
  let mut seen : Std.HashSet Nat := {}
  for f in functions do
    siblings := siblings.alter f.definition (fun ids => some (f.id :: ids.getD []))
    if f.definition.scope.package.source == root || rootEdited.contains f.definition then
      work := f.id :: work
      seen := seen.insert f.id
  let mut expanded : Std.HashSet DeclId := {}
  for _ in [:functions.size] do
    let id :: rest := work | break
    work := rest
    let some f := functions[id]? | continue
    let mut nextIds := f.body.callIds
    for owner in f.definition :: ((origins[id]?).bind (edges[·]?)).getD [] do
      unless expanded.contains owner do
        nextIds := (siblings[owner]?.getD []) ++ nextIds
        expanded := expanded.insert owner
    for next in nextIds do
      if !seen.contains next then
        seen := seen.insert next
        work := next :: work
  return seen

/-- The original symbol, nominal owner, exact method or template key and its
concrete static indices survive linkage even for an excluded dependency. -/
structure Disposition where
  original : Nat
  owner : DeclId
  bodyScope : Namespace.Scope
  specialization : FunctionSource.Compiler.Key
  indices : List FunctionSource.StaticIndex
  localId : Option Nat

def selected (m : Core.Module) (originals : Array Nat) : Core.Module :=
  {m with functions := m.functions.filter (fun f => originals.contains f.id)}

def closed (m : Core.Module) (originals : Array Nat) : Bool :=
  (selected m originals).functions.all (fun f => f.body.callIds.all originals.contains)

def rootCovered (m : Core.Module) (root : String) (originals : Array Nat) : Bool :=
  m.functions.all fun f => f.definition.scope.package.source != root || originals.contains f.id

/-- Every callable declared by the root and every family explicitly sealed
by its assembly needs a retained concrete definition. -/
def sourceCovered {json main} (req : Request json main) (originals : Array Nat) : Bool :=
  let src := req.checked.pureProgram
  let owners := Std.HashSet.ofList ((selected (core req) originals).functions.filterMap fun f => do
    let key ← src.executable.lowered.origins[f.id]?
    let prepared ← src.compiler.input.prepared[key.definition]?
    guard (!prepared.definition.isLambda)
    return f.definition)
  req.checked.pureProgram.authority.headers.assembled.state.sealed.toList.all owners.contains &&
    req.input.pureProgram.source.headers.indexed.declarations.all (fun d =>
    d.owner.scope.package.source != req.input.root || !(d.kind == .function || d.kind == .generic) ||
      owners.contains d.owner) &&
    req.input.packages.all (fun pkg => pkg.id.source != req.input.root || pkg.modules.all (·.functions.isEmpty))

/-- Check every applied concrete definition in an explicitly sealed family
and every applied root implementation, including uncalled and nonwinning
instances. The separate unapplied audit has no executable instance to retain. -/
def rootMethodsCovered {json main} (req : Request json main) (originals : Array Nat) : Bool :=
  let src := req.checked.pureProgram
  let kept := Std.HashSet.ofList (originals.toList.filterMap fun i =>
    src.executable.lowered.origins[i]?.map (·.definition))
  src.authority.applied.all fun method =>
    (method.scope.package.source != req.input.root &&
      !src.authority.headers.assembled.state.sealed.contains method.owner) ||
      src.dispatcher.definitions[(method.method,method.key)]?.any kept.contains

def familiesCovered (m : Core.Module) (originals : Array Nat) : Bool := Id.run do
  let mut owners : Std.HashMap DeclId Bool := {}
  for f in m.functions do
    let keep := originals.contains f.id
    if let some prior := owners[f.definition]? then
      if prior != keep then return false
    owners := owners.insert f.definition keep
  return true

private def callIds (f : Function .optimization) : List Nat :=
  f.blocks.toList.flatMap fun b => b.ops.toList.filterMap fun op =>
    match op.code with | .call target => some target.symbol | _ => none

/-- Every emitted sibling of a static reference must survive linkage. An
unused higher-order declaration may have only its separate source audit. -/
def staticClosed {json main} (req : Request json main) (ids : Array Nat) : Bool :=
  let src := req.checked.pureProgram
  let pass := src.executable.lowered
  let keep := Std.HashSet.ofList ids.toList
  let keys := Std.HashSet.ofList (ids.toList.filterMap (pass.origins[·]?))
  let excluded := Std.HashSet.ofList ((core req).functions.filterMap fun f =>
    if keep.contains f.id then none else some f.definition)
  let covered caller owner := !keys.contains caller || !excluded.contains owner
  pass.familyRefs.all (fun ref => covered ref.caller ref.target.owner) &&
    pass.staticUses.all fun use => match use.caller, use.target.name with
      | some caller, .concrete defId => (src.compiler.input.prepared[defId]?).any fun target =>
        covered caller target.definition.owner
      | _, _ => false

/-- Structural witness on every local symbol, including original call edge
multiplicity and finite-template origin. Calls can be spelled in a different
order by A-normalization, so the CFG also remains part of the artifact. -/
def aligned {json main} (req : Request json main) (originals : Array Nat)
    (opt : Module .optimization) : Bool := Id.run do
  let src := req.checked.pureProgram
  let fs := (core req).functions.toArray
  unless originals.size == opt.functions.size do return false
  for (f, i) in opt.functions.toList.zipIdx do
    let some id := originals[i]? | return false
    let some orig := fs[id]? | return false
    let some key := src.executable.lowered.origins[id]? | return false
    let some target := CallTarget.ofCore orig key | return false
    let some called := (callIds f).mapM (originals[·]?) | return false
    unless orig.id == id && validOrigin src orig key &&
      decide (f.target = {target with symbol := i}) && Finite.sameCounts called orig.body.callIds do
      return false
  return true

/-- Run structural lowering over each retained original body; the resolver
remaps only checked direct calls. Every actual call must also occur in the
source compiler's emitted-call multiset. -/
def lowerFunctions {json main} (req : Request json main) (originals : Array Nat) :
    Option (Array (Function .optimization)) := do
  let locals := Std.HashMap.ofList originals.toList.zipIdx
  let src := req.checked.pureProgram
  let fs := (core req).functions.toArray
  let env := (core req).declarations.indexed
  let resolve (id : Nat) : Option CallTarget := do
    let localId ← locals[id]?
    let f ← fs[id]?
    guard (f.id == id)
    let t ← CallTarget.ofCore f (← src.executable.lowered.origins[id]?)
    return {t with symbol := localId}
  let functions ← originals.mapM fun id => do
    let orig ← fs[id]?
    let key ← src.executable.lowered.origins[id]?
    lowerLinkedFunction env key {orig with id := ← locals[id]?} resolve
  let keys := Std.HashSet.ofList (functions.toList.map (·.specialization))
  let recorded ← (src.executable.lowered.emittedCalls.filter (fun e => keys.contains e.caller)).mapM fun e => do
    return {e with id := ← locals[e.id]?}
  guard (exactCalls functions.toList recorded)
  return functions

/-- One disposition in original order for each accepted Core symbol. -/
def ledger {json main} (req : Request json main) (originals : Array Nat) :
    Option (Array Disposition) := do
  let src := req.checked.pureProgram
  let locals := Std.HashMap.ofList originals.toList.zipIdx
  guard (locals.size == originals.size)
  (core req).functions.toArray.zipIdx.mapM fun (f,i) => do
    let key ← src.executable.lowered.origins[i]?
    let prep ← src.compiler.input.prepared[key.definition]?
    guard (f.id == i && validOrigin src f key)
    return ⟨i, f.definition, prep.definition.bodyScope, key, prep.finiteKey, locals[i]?⟩

/-- Program link for a closed executable, with dense local addresses and the
exact original addresses and source identities for every emitted function. -/
structure Artifact {json main} (req : Request json main) where
  originals : Array Nat
  dispositions : Array Disposition
  sourceEntry : Nat
  entry : Nat
  opt : Module .optimization
  exe : Module .execution
  originalEntry : (core req).main = some sourceEntry
  entryMap : originals[entry]? = some sourceEntry
  accounted : ledger req originals = some dispositions
  allRoots : rootCovered (core req) req.input.root originals = true
  rootSources : sourceCovered req originals = true
  rootMethods : rootMethodsCovered req originals = true
  allSiblings : familiesCovered (core req) originals = true
  staticTargets : staticClosed req originals = true
  allCalls : closed (core req) originals = true
  bodies : lowerFunctions req originals = some opt.functions
  lowering : aligned req originals opt = true
  optEntry : opt.entry = some entry
  revision : opt.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) req.checked
  environment : opt.env = (core req).declarations.indexed
  executed : opt.execute = some exe

private def takeChecked {α : Type} (x : Option α) : Option {y // x = some y} :=
  match x with | some y => some ⟨y,rfl⟩ | none => none

private def certify (P : Prop) [Decidable P] : Option (PLift P) := if h : P then some ⟨h⟩ else none

def compile {json main} (req : Request json main) : Option (Artifact req) := do
  let checked := req.checked
  let src := checked.pureProgram
  guard (checked.lowered.functions.isEmpty && checked.observations.isEmpty &&
    req.input.pureFragments.isEmpty && src.compiled.entries.isEmpty)
  let m := core req
  let some sourceEntry := m.main | none
  let fs := m.functions.toArray
  let mainFn ← fs[sourceEntry]?
  guard (mainFn.id == sourceEntry && mainFn.definition.scope.package.source == req.input.root &&
    mainFn.definition.name == "main" && mainFn.definition.scope.path.isEmpty)
  let rootEdited := src.authority.applied.foldl (init := src.authority.headers.assembled.state.sealed)
    fun owners method => if method.scope.package.source == req.input.root then owners.insert method.owner else owners
  let edges ← staticEdges req
  let keep := closure m req.input.root rootEdited src.executable.lowered.origins edges
  let originals := (fs.filter (fun f => keep.contains f.id)).map (·.id)
  let locals := Std.HashMap.ofList originals.toList.zipIdx
  let entry ← locals[sourceEntry]?
  let ⟨functions,bodies⟩ ← takeChecked (lowerFunctions req originals)
  let rev := ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) checked
  guard (ResourceSource.FunctionRevision.bounded rev)
  let opt := Module.mk rev m.declarations.indexed functions (some entry)
  let ⟨originalEntry⟩ ← certify (m.main = some sourceEntry)
  let ⟨entryMap⟩ ← certify (originals[entry]? = some sourceEntry)
  let ⟨allRoots⟩ ← certify (rootCovered m req.input.root originals = true)
  let ⟨sourceRoots⟩ ← certify (sourceCovered req originals = true)
  let ⟨rootMethods⟩ ← certify (rootMethodsCovered req originals = true)
  let ⟨allSiblings⟩ ← certify (familiesCovered m originals = true)
  let ⟨staticTargets⟩ ← certify (staticClosed req originals = true)
  let ⟨allCalls⟩ ← certify (closed m originals = true)
  let ⟨lowering⟩ ← certify (aligned req originals opt = true)
  match h : opt.execute, recorded : ledger req originals with
  | some exe, some dispositions =>
    return ⟨originals,dispositions,sourceEntry,entry,opt,exe,originalEntry,entryMap,
      recorded,allRoots,sourceRoots,rootMethods,allSiblings,staticTargets,
      allCalls,bodies,lowering,rfl,rfl,rfl,h⟩
  | _, _ => none

end VastitasKernel.MidIR.PackageLink
