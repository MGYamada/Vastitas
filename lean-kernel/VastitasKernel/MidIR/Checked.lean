import VastitasKernel.MidIR.Lower
import VastitasKernel.ResourceProtocol

set_option autoImplicit false

namespace VastitasKernel.MidIR

/-- Count every call occurrence against the compiler's selected specialization
record, including calls selected from the current assembled method table. -/
def exactCalls (functions : List (Function .optimization))
    (recorded : List Indexed.FunctionSource.Compiler.EmittedCall) : Bool := Id.run do
  let mut actual := []
  for f in functions do
    for b in f.blocks do
      for op in b.ops do
        if let .call target := op.code then
          actual := (f.specialization, target.symbol, target.key) :: actual
  return recorded.all (fun e => e.key == e.origin) &&
    Finite.sameCounts actual (recorded.map fun e => (e.caller, e.id, e.origin))

/-- Match the checked source owner for every specialization. The assembler
numbers applied method instances after the source functions. Its reconstructed
method/key map, never a spelling or expected return type, fixes that offset. -/
def validOrigin {p : Indexed.DispatchSource.Program} {main : Bool}
    (s : Indexed.AuthoritySource.CheckedProgram p main) (f : Indexed.Core.Function)
    (key : Indexed.FunctionSource.Compiler.Key) : Bool :=
  Id.run do
    let input := s.compiler.input
    let some entry := input.prepared[key.definition]? | return false
    let d := entry.definition
    unless Indexed.FunctionSource.Compiler.validKey input false key && d.id == key.definition &&
        d.owner == f.definition && entry.parameters == f.parameters && entry.result == f.returnType do
      return false
    if let some body := entry.finiteBody then
      return Indexed.Core.Reverse.termEq body f.body &&
        Indexed.FunctionSource.Compiler.validFinitePrepared input entry key.definition
    -- Lifted lambdas retain their containing ordinary function or applied method.
    let some parent := input.prepared[d.origin]? | return false
    unless !parent.definition.isLambda && parent.definition.id == d.origin &&
        parent.definition.owner == d.owner && parent.definition.bodyScope == d.bodyScope &&
        (d.isLambda || d.origin == d.id) do return false
    if let some named := input.named[f.definition]? then return named == d.origin
    let offset := p.source.functions.length
    return offset ≤ d.origin && (s.authority.applied[d.origin - offset]?).any fun inst =>
      inst.owner == f.definition && s.dispatcher.definitions[(inst.method,inst.key)]? == some d.origin

/-- Consume the same public wire certificate and exact checked, reverse-compiled
Core as code generation. Monomorphic functions include statically selected
family methods. Every emitted body must lower. Resource functions,
reverse sites and source observations require their own lowering. -/
def lowerChecked {json : Lean.Json} {main : Bool}
    (input : ResourceSource.Wire.CheckedInput json main) : Option (Module .optimization) := do
  let checked := input.checked
  guard (checked.lowered.functions.isEmpty && checked.observations.isEmpty &&
    input.input.pureFragments.isEmpty && checked.pureProgram.compiled.entries.isEmpty)
  let source := checked.pureProgram
  guard (source.compiler.input.templates.isEmpty && source.executable.lowered.staticUses.isEmpty &&
    source.executable.lowered.familyRefs.isEmpty)
  let core := source.compiled.core.module
  let targets ← core.functions.mapM fun f => do
    CallTarget.ofCore f (← source.executable.lowered.origins[f.id]?)
  let functions ← core.functions.mapM fun f => do
    let key ← source.executable.lowered.origins[f.id]?
    guard (validOrigin source f key)
    lowerFunction core.declarations.indexed key f targets.toArray
  guard (exactCalls functions source.executable.lowered.emittedCalls)
  let revision := ResourceSource.FunctionRevision.artifact
    (ResourceSource.Wire.revisionInput json) checked
  guard (ResourceSource.FunctionRevision.boundedDerived revision)
  let out := Module.mk revision core.declarations.indexed functions.toArray core.main
  guard (validSymbols out)
  return out

/-- The checked environment and complete revision come directly from this
request. Later specializations can transport them without comparing or
reserializing the revision. -/
theorem lowerChecked_identity {json : Lean.Json} {main : Bool}
    (input : ResourceSource.Wire.CheckedInput json main) (m : Module .optimization)
    (h : lowerChecked input = some m) :
    m.env = input.checked.pureProgram.compiled.core.module.declarations.indexed ∧
    m.revision = ResourceSource.FunctionRevision.artifact (ResourceSource.Wire.revisionInput json) input.checked := by
  simp only [lowerChecked, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ho⟩ := h
  cases Option.some.inj ho
  exact ⟨rfl, rfl⟩

theorem execute_identity (m : Module .optimization) (out : Module .execution) (h : m.execute = some out) :
    out.env = m.env ∧ out.revision = m.revision := by
  simp only [Module.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, ho⟩ := h
  cases Option.some.inj ho
  exact ⟨rfl, rfl⟩

end VastitasKernel.MidIR
