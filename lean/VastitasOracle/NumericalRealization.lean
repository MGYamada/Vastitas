import VastitasOracle.ExactAffine

set_option autoImplicit false

/-! Standard charts of smooth real affines and exact complex affines. The
public identity interpretation copies between two checked resource points.
The chart and the literal graph are recovered from the accepted request. -/
namespace VastitasOracle.NumericalRealization
open VastitasKernel VastitasKernel.ResourceSource VastitasKernel.Indexed

inductive Representation where
  | real32 | real64 | complex32 | complex64
  deriving DecidableEq, Repr

/-- Valid only for canonical smooth affines: the standard coordinate chart
is nominally indexed by the existing object. No chart is inferred for gluings. -/
structure RealChart where
  subject : DeclId
  deriving DecidableEq, Repr

/-- Retain the smooth site by construction and its concrete implementation:
the coefficient *marker* does not stand for a geometric base object. -/
structure Descriptor (env : Environment) (rep : Representation) (subject : DeclId) (chart : RealChart) where
  implementation : DeclId
  realMarker : DeclId
  coordinates : List String
  exactSubject : Indexed.lookup env subject = some (.smoothAffine implementation coordinates)
  exactImplementation : Indexed.lookup env implementation = some (.implementation realMarker .smoothAffine [])
  exactChart : chart.subject = subject
  real : rep = .real32 ∨ rep = .real64

def construct (env : Environment) (rep : Representation)
    (subject : DeclId) (chart : RealChart) : Option (Descriptor env rep subject chart) := do
  if h : chart.subject = subject then
    if r : rep = .real32 ∨ rep = .real64 then
      match hs : Indexed.lookup env subject with
      | some (.smoothAffine impl coordinates) =>
        match hi : Indexed.lookup env impl with
        | some (.implementation marker .smoothAffine []) =>
          return ⟨impl, marker, coordinates, hs, hi, h, r⟩
        | _ => none
      | _ => none
    else none
  else none

/-- No caller-supplied declaration table, chart dimension or coefficient
type becomes evidence: the environment is the accepted public input's. -/
def fromChecked {json : Lean.Json} {main : Bool} (input : Wire.CheckedInput json main)
    (rep : Representation) (subject : DeclId) (chart : RealChart) :=
  construct (numericalEnvironment input.checked.pureProgram) rep subject chart

/-- Original source matters: the existing smooth-map normalizer can turn
floating-distinct programs into identical exact polynomials. Only an explicit
identity declaration denotes this graph; inspecting its exact map alone would
wrongly accept a pullback that merely simplifies to identity. -/
def declaredIdentity (p : Source.Program) (owner : DeclId) : Bool :=
  (p.owned.find? (fun pair => pair.1 == owner)).any fun pair =>
    match pair.2.body with | .morphism _ _ .identity => true | _ => false

structure IdentityPlan {json : Lean.Json} {main : Bool} (input : Wire.CheckedInput json main)
    (rep : Representation) (subject graph : DeclId) (chart : RealChart) where
  descriptor : Descriptor (numericalEnvironment input.checked.pureProgram) rep subject chart
  sourceIdentity : declaredIdentity input.input.pureProgram.source.headers graph = true
  family : DeclId
  checkedMap : input.checked.pureProgram.authority.headers.declarations.resolved.declarations.primitive? graph =
    some (.smoothConstant ⟨family, [.object (.global subject), .object (.global subject)]⟩
      (SmoothRuntime.identity descriptor.coordinates.length))

/-- Check the selected computation from the same source and mathematical
environment as the realization's descriptor. Comparing the whole map also
binds its source arity. This finite graph has no floating arithmetic. -/
def interpretIdentity {json : Lean.Json} {main : Bool} (input : Wire.CheckedInput json main)
    (rep : Representation) (subject graph : DeclId) (chart : RealChart) :
    Option (IdentityPlan input rep subject graph chart) := do
  let d ← fromChecked input rep subject chart
  if h : declaredIdentity input.input.pureProgram.source.headers graph = true then
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations
    let some (.smoothConstant app _) := env.primitive? graph | none
    if hc : env.primitive? graph =
        some (.smoothConstant ⟨app.family, [.object (.global subject), .object (.global subject)]⟩
          (SmoothRuntime.identity d.coordinates.length)) then
      return ⟨d, h, app.family, hc⟩
    else none
  else none

/-- A denotationally equal polynomial is insufficient: every selected
presentation is the identity as actually declared, and the checked Core
constant has the same two nominal endpoints. -/
theorem identity_presentation {json : Lean.Json} {main : Bool}
    {input : Wire.CheckedInput json main} {rep : Representation} {subject graph : DeclId} {chart : RealChart}
    (plan : IdentityPlan input rep subject graph chart) :
    declaredIdentity input.input.pureProgram.source.headers graph = true ∧
    input.checked.pureProgram.authority.headers.declarations.resolved.declarations.primitive? graph =
      some (.smoothConstant ⟨plan.family, [.object (.global subject), .object (.global subject)]⟩
        (SmoothRuntime.identity plan.descriptor.coordinates.length)) :=
  ⟨plan.sourceIdentity, plan.checkedMap⟩

theorem foreign_chart_impossible {env : Environment} {rep : Representation} {subject : DeclId} {chart : RealChart}
    (d : Descriptor env rep subject chart) (foreignChart : chart.subject ≠ subject) : False :=
  foreignChart d.exactChart

theorem complex_on_smooth_real_impossible {env : Environment} {subject : DeclId} {chart : RealChart}
    (d : Descriptor env .complex64 subject chart) : False := by
  cases d.real <;> contradiction

theorem dimension_from_subject {env : Environment} {rep : Representation} {subject : DeclId} {chart : RealChart}
    (d : Descriptor env rep subject chart) :
    smoothDimension? env subject = some d.coordinates.length := by
  simp [smoothDimension?, smoothCoordinates?, d.exactSubject]

/-- Every site, including one in an uncalled library function, resolved in
its source namespace and passed the chart and graph check of this very request. -/
theorem checked_site {json main} (input : Wire.CheckedInput json main)
    (site : RealizationSite) (member : site ∈ input.checked.lowered.realizationSites) :
    site.resolves input.input.pureProgram.source.headers.indexed = true ∧
    site.valid (declaredIdentities input.input.pureProgram.source.headers)
      input.checked.pureProgram.authority.headers.declarations.resolved.declarations = true := by
  have h := input.checked.realizations
  generalize he : input.checked.lowered.realizationSites = sites at h member
  cases sites with
  | nil => contradiction
  | cons s rest =>
    simp only [validRealizations, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at h
    simpa only [Bool.and_eq_true] using h site member

/-- A written wrapper produces the canonical realize operation on its fresh
subject. Its dimension is recovered from the accepted mathematical environment. -/
theorem checked_affine_realization {json main} (input : Wire.CheckedInput json main)
    (s : RealizationSite) (member : s ∈ input.checked.lowered.realizationSites)
    (written : AffineRealizationProfile.Site) (wrapper : s.affine = some written) :
    s.operation = .realize written.descriptor ∧
    s.functionId.owner = ⟨Namespace.floatScope, "realize"⟩ ∧
    ∃ profile, written.descriptor.profile (numericalEnvironment input.checked.pureProgram) = some profile ∧
      profile.coordinates.length = written.dimension := by
  obtain ⟨resolved, valid⟩ := checked_site input s member
  simp only [RealizationSite.resolves, wrapper, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at resolved
  obtain ⟨⟨_, op⟩, family⟩ := resolved
  refine ⟨op, family, ?_⟩
  unfold numericalEnvironment
  simp only [RealizationSite.valid, op, Storage.Realization.Operation.descriptor,
    Storage.Realization.Operation.family, family, wrapper] at valid
  repeat' (split at valid <;> try contradiction)
  exact ⟨_, by assumption, by simpa using valid⟩

/-- Distinct physical constructor occurrences, including occurrences of the
same representation and dimension, have different nominal subjects. -/
theorem affine_subjects_distinct (a b : AffineRealizationProfile.Site)
    (different : a.span.start ≠ b.span.start) : a.subject ≠ b.subject := by
  intro equal
  have names := congrArg Namespace.Owner.name equal
  change "AffineAt" ++ Nat.repr a.span.start = "AffineAt" ++ Nat.repr b.span.start at names
  exact different (Nat.repr_injective ((String.append_right_inj "AffineAt").mp names))

/-- The point selects a physical allocation with exactly its descriptor's
representation, including when two distinct scalar types occupy eight bytes. -/
theorem point_scalar {env : Indexed.Environment} {d : Storage.Realization.Descriptor}
    {s : Storage.State} {name : Storage.Symbol}
    (valid : Storage.Realization.pointValid env d s name = true) :
    ∃ l a, s.loan? name = some l ∧ s.allocation? l.allocation = some a ∧
      a.scalar = d.representation.scalar := by
  cases hp : d.profile env with
  | none => simp [Storage.Realization.pointValid, hp] at valid
  | some profile =>
    cases hl : s.loan? name with
    | none => simp [Storage.Realization.pointValid, hp, hl] at valid
    | some loan =>
      cases ha : s.allocation? loan.allocation with
      | none => simp [Storage.Realization.pointValid, hp, hl, ha] at valid
      | some allocation =>
        simp [Storage.Realization.pointValid, hp, hl, ha] at valid
        have same : ∀ x y : Storage.Scalar, (x == y) = true → x = y := by
          intro x y
          cases x <;> cases y <;> decide
        exact ⟨loan, allocation, rfl, ha, same _ _ valid.1.1.2⟩

/-- A chart is backed by declarations of the same accepted environment. -/
def ChartEquations (env : Environment) (d : Storage.Realization.Descriptor)
    (p : Storage.Realization.ChartProfile) : Prop :=
  match p.base with
  | .smooth impl marker =>
    d.representation.isReal = true ∧
    Indexed.lookup env d.subject = some (.smoothAffine impl p.coordinates) ∧
    Indexed.lookup env impl = some (.implementation marker .smoothAffine [])
  | .exactComplex model carrier realModel realCarrier =>
    d.representation.isReal = false ∧
    (∃ n, Indexed.lookup env d.subject = some (.exactGeometry (.affine model n p.coordinates))) ∧
    (exactView env model).bind (·.model? (exactView env)) = some (.pairs carrier realModel realCarrier)

/-- Exact IDs and coordinate order follow from the descriptor that the public
checker actually used. The two kinds of chart require different component counts. -/
theorem profile_equations {env : Environment} {d : Storage.Realization.Descriptor}
    {p : Storage.Realization.ChartProfile} (h : d.profile env = some p) :
    d.chart = d.subject ∧ ChartEquations env d p := by
  unfold Storage.Realization.Descriptor.profile at h
  split at h
  · contradiction
  next same =>
    refine ⟨?_, ?_⟩
    · exact (Classical.not_not.mp (fun ne => same (bne_iff_ne.mpr ne))).symm
    · split at h
      next real =>
        split at h <;> try contradiction
        split at h <;> try contradiction
        cases h
        exact ⟨real, by assumption, by assumption⟩
      next complex =>
        split at h <;> try contradiction
        dsimp only at h
        split at h <;> try contradiction
        cases h
        exact ⟨Bool.eq_false_iff.mpr complex, ⟨_, by assumption⟩, by assumption⟩

def IdentityGraph (env : Indexed.Core.Declarations) (plan : Storage.Realization.Plan)
    (p : Storage.Realization.ChartProfile) : Prop :=
  match p.base with
  | .smooth .. => ∃ family, env.primitive? plan.graph = some (.smoothConstant
      ⟨family,[.object (.global plan.descriptor.subject),.object (.global plan.descriptor.subject)]⟩
      (SmoothRuntime.identity p.coordinates.length))
  | .exactComplex .. => exactView env.indexed plan.graph = some (.identity plan.descriptor.subject)

theorem matches_identity {env : Indexed.Core.Declarations} {plan : Storage.Realization.Plan}
    {p : Storage.Realization.ChartProfile} (h : matchesIdentity plan env p = true) : IdentityGraph env plan p := by
  cases base : p.base with
  | smooth impl marker =>
    simp only [ResourceSource.matchesIdentity, base] at h
    split at h <;> try contradiction
    simp only [Id.run, pure, beq_iff_eq] at h
    exact (show IdentityGraph env plan p from by rw [IdentityGraph, base]; exact ⟨_, h⟩)
  | exactComplex model carrier realModel realCarrier =>
    simpa [ResourceSource.matchesIdentity, IdentityGraph, base] using h

theorem checked_run_identity {json main} (input : Wire.CheckedInput json main)
    (site : RealizationSite) (member : site ∈ input.checked.lowered.realizationSites)
    {plan : Storage.Realization.Plan} {src dst : Storage.Symbol} (op : site.operation = .run plan src dst) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations
    ∃ profile, plan.descriptor.profile env.indexed = some profile ∧
      (declaredIdentities input.input.pureProgram.source.headers).contains (plan.graph,profile.base.kind) = true ∧
      IdentityGraph env plan profile := by
  have h := (checked_site input site member).2
  dsimp only
  simp only [RealizationSite.valid, op, Storage.Realization.Operation.descriptor,
    Storage.Realization.Operation.family] at h
  repeat' (split at h <;> try contradiction)
  simp only [Id.run, pure, Bool.and_eq_true] at h
  exact ⟨_, by assumption, h.1, matches_identity h.2⟩

/-- The executable receipt contains the real before/after states, both live
point checks and the physical copy at this call's position in the schedule. -/
theorem executed_copy {json main} (input : Wire.CheckedInput json main)
    (entry : Nat) (selected : input.input.entry = some entry)
    (r : Storage.Functions.RealizationRunReceipt)
    (member : r ∈ (input.checked.execution entry selected).checked.context.realizationRuns.toList) :
    r.environment = numericalEnvironment input.checked.pureProgram ∧
    sourceRun input.checked.lowered.functions r.location.source = some r.plan ∧
    Storage.Realization.pointValid r.environment r.plan.descriptor r.before r.input = true ∧
    Storage.Realization.pointValid r.environment r.plan.descriptor r.before r.output = true ∧
    Storage.checkAction r.before (.copy r.input r.output) = .ok r.after ∧
    r.priorCode ++ [.action (.copy r.input r.output)] = r.code := by
  have h := (input.checked.execution entry selected).realizationOrigins r member
  exact ⟨h.1,h.2,r.inputValid,r.outputValid,r.transitioned,r.emitted⟩

/-- Membership in the source identity index yields the original declaration
and its literal presentation, before any polynomial normalization. -/
theorem declared_identity_member {p : Source.Program} {graph : DeclId} {kind : Storage.Realization.GraphKind}
    (selected : (declaredIdentities p).contains (graph,kind) = true) :
    ∃ decl, (graph,decl) ∈ p.owned ∧ declaredIdentityKind decl.body = some kind := by
  simp only [declaredIdentities, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_filterMap] at selected
  obtain ⟨⟨owner,decl⟩,member,h⟩ := selected
  cases hk : declaredIdentityKind decl.body with
  | none => simp [hk] at h
  | some k =>
    simp [hk] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨decl,member,hk⟩

private theorem plan_eq_of_beq {a b : Storage.Realization.Plan} (h : (a == b) = true) : a = b := by
  obtain ⟨x,f,pa⟩ := a
  obtain ⟨y,g,pb⟩ := b
  cases pa
  cases pb
  change (x == y && (f == g && true)) = true at h
  simp only [Bool.and_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl,rfl⟩ := h
  rfl

/-- Every executed receipt points back to the lexical run, the original
identity declaration and the exact checked morphism on the selected subject.
The caller need only provide an actual receipt of the public execution. -/
theorem executed_source_identity {json main} (input : Wire.CheckedInput json main)
    (entry : Nat) (selected : input.input.entry = some entry) (r : Storage.Functions.RealizationRunReceipt)
    (member : r ∈ (input.checked.execution entry selected).checked.context.realizationRuns.toList) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations
    ∃ site ∈ input.checked.lowered.realizationSites, ∃ src dst,
      (r.location.source.function.bind (input.checked.lowered.owners.toArray[·]?)) = some site.owner ∧
      site.position = r.location.source.path ∧ site.operation = .run r.plan src dst ∧
      ∃ profile, r.plan.descriptor.profile env.indexed = some profile ∧
        (∃ decl, (r.plan.graph,decl) ∈ input.input.pureProgram.source.headers.owned ∧
          declaredIdentityKind decl.body = some profile.base.kind) ∧ IdentityGraph env r.plan profile := by
  dsimp only
  obtain ⟨site,original,same⟩ := input.checked.runSources entry selected r member
  simp only [RealizationSite.matchesRun, Bool.and_eq_true, beq_iff_eq] at same
  obtain ⟨⟨owner,path⟩,op⟩ := same
  split at op <;> try contradiction
  rename_i plan src dst h
  have eqPlan : plan = r.plan := plan_eq_of_beq op
  subst plan
  obtain ⟨profile,chart,graph,eq⟩ := checked_run_identity input site original h
  exact ⟨site,original,src,dst,owner,path,h,profile,chart,declared_identity_member graph,eq⟩

/-- An actual complex identity copy recovers its chart, the four declarations
of its paired field, and its graph on this very affine. -/
theorem executed_complex_model {json main} (input : Wire.CheckedInput json main)
    (entry : Nat) (selected : input.input.entry = some entry) (r : Storage.Functions.RealizationRunReceipt)
    (member : r ∈ (input.checked.execution entry selected).checked.context.realizationRuns.toList)
    (complex : r.plan.descriptor.representation.isReal = false) :
    let env := input.checked.pureProgram.authority.headers.declarations.resolved.declarations.indexed
    let named := exactView env
    let d := r.plan.descriptor
    d.chart = d.subject ∧ ∃ model carrier realModel realCarrier dim coords,
      Indexed.lookup env d.subject = some (.exactGeometry (.affine model dim coords)) ∧
      named model = some (.complexMeadow carrier realModel) ∧ named carrier = some (.complexPairs realCarrier) ∧
      named realCarrier = some .cauchyQQ ∧ named realModel = some (.realMeadow realCarrier) ∧
      named r.plan.graph = some (.identity d.subject) := by
  dsimp only
  obtain ⟨_,_,_,_,_,_,_,p,h,_,graph⟩ := executed_source_identity input entry selected r member
  obtain ⟨chart,eqs⟩ := profile_equations h
  refine ⟨chart, ?_⟩
  cases hb : p.base with
  | smooth impl marker =>
    rw [ChartEquations, hb] at eqs
    simp [complex] at eqs
  | exactComplex model carrier realModel realCarrier =>
    rw [ChartEquations, hb] at eqs
    rw [IdentityGraph, hb] at graph
    obtain ⟨_,⟨dim,affine⟩,pair⟩ := eqs
    obtain ⟨meadow,parts,real,base⟩ := ExactAffine.paired_selection pair
    exact ⟨model,carrier,realModel,realCarrier,dim,p.coordinates,affine,meadow,parts,real,base,graph⟩

end VastitasOracle.NumericalRealization
