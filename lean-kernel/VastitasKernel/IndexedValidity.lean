import VastitasKernel.FrameDeclarations
import VastitasKernel.NatureDimension

/-! The validity of indexed declaration entries (`Entry.Valid`, `validEntry`)
and of the whole declaration environment (`Environment.Valid`,
`validEnvironment`), over the data model of `Indexed`.

The checks of the frame declarations (`FrameDeclarations`) and of the nature
declarations (`NatureDimension`) of Stage 4 (#759) read the environment
through the views of `Indexed`, so this module imports them and they import
`Indexed`. -/
namespace VastitasKernel.Indexed

/-- A presented object: its implementation is a presented representation, its
base chain is finite and stays within presented objects of the same marker,
and its stored data verifies against its base's stored data. -/
def validAffine (env : Environment) (id implementation : DeclId)
    (data : AlgebraDeclarations.AffineData) : Bool :=
  presentedImplementation env implementation &&
  (match chainOf env id with | some chain => decide chain.Nodup | none => false) &&
  (match data.base with
    | none => true
    | some base => match lookup env base with
      | some (.affine baseImplementation _) =>
          implementationMarker env baseImplementation == implementationMarker env implementation
      | _ => false) &&
  AlgebraDeclarations.validAffineData data (data.base.bind (affineData? env)) &&
  AlgebraDeclarations.validConstruction data (affineData? env)

/-- A smooth object: its implementation is a smooth representation and its
coordinates are distinct and within the generator limit. -/
def validSmoothAffine (env : Environment) (implementation : DeclId) (coordinates : List String) : Bool :=
  smoothImplementation env implementation && decide (coordinates.length ≤ Limits.algebraGenerators) &&
    decide coordinates.Nodup

/-! ## Metrics (Stage 3) -/

/-- A metric `MetricForm<object>`: an application of a `metric_form` family
to a declared smooth object, and a Gram matrix that `checkGram` accepts at the
object's dimension, with entries within `Limits.metricEntryBits` and the whole
matrix within `Limits.metricMatrixBits`. The matrix bound is the last
conjunct: it is computed for a square matrix with bounded entries. -/
def validMetric (env : Environment) (family object : DeclId) (gram : SmoothRuntime.Matrix) : Bool :=
  isMetricFamily env family && validApplication env ⟨family, [.object (.global object)]⟩ &&
    SmoothDeclarations.gramBounded gram &&
    (match smoothDimension? env object with
    | some n => (SmoothDeclarations.checkGram n gram).isOk
    | none => false) &&
    SmoothDeclarations.matrixBounded gram

/-- The exact identities of a certificate for an `n × n` Gram matrix. -/
def MetricEvidence.check (n : Nat) (gram : SmoothRuntime.Matrix) : MetricEvidence → Bool
  | .nondegenerate inverse => SmoothDeclarations.checkNondegenerate n gram inverse
  | .riemannian lower pivots lowerInverse =>
      SmoothDeclarations.checkRiemannian n gram lower pivots lowerInverse

/-- Evidence for a declared metric, checked against that metric's Gram matrix. -/
def validMetricEvidence (env : Environment) (metric : DeclId) (evidence : MetricEvidence) : Bool :=
  match metricData? env metric with
  | some (_, n, gram) => evidence.check n gram
  | none => false

def Entry.Valid (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Prop :=
  match entry.declaration with
  | .marker => True
  | .implementation marker representation capabilities =>
      isMarker env marker = true ∧ capabilities.Nodup ∧ representation.Valid env marker capabilities
  | .classification parents implementations =>
      parents.Nodup ∧ implementations.Nodup ∧ implementations ≠ [] ∧
      implementations.length ≤ 64 ∧
      (∀ id ∈ implementations, (implementationMarker env id).isSome = true) ∧
      (∀ parent ∈ parents, ∃ ps ds,
        lookup env parent = some (.classification ps ds) ∧
        (∀ id ∈ implementations, id ∈ ds) ∧
        classRank ranks parent < classRank ranks entry.id)
  | .global implementation => (implementationMarker env implementation).isSome = true ∧
      presentedImplementation env implementation = false ∧ smoothImplementation env implementation = false
  | .family f => f.Valid env
  | .affine implementation data => validAffine env entry.id implementation data = true
  | .smoothAffine implementation coordinates => validSmoothAffine env implementation coordinates = true
  | .metric family object gram => validMetric env family object gram = true
  | .metricEvidence metric evidence => validMetricEvidence env metric evidence = true
  | .frame family object matrix inverse =>
      FrameDeclarations.checkFrame env family object matrix inverse = true
  | .baseDimension => NatureDimension.checkBaseDimension env = true
  | .quantity dimension => NatureDimension.checkQuantity env dimension = true
  | .reading family object quantities => NatureDimension.checkReading env family object quantities = true
  | .scale quantity magnitude => NatureDimension.checkScale env quantity magnitude = true
  | .physicalMetric family object metric reading value entries =>
      NatureDimension.checkPhysicalMetric env family object metric reading value entries = true

/-- A separately structured executable parent check, avoiding unbounded search
for a classification record in the finite validation procedure. -/
def validParents (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry)
    (parents implementations : List DeclId) : Bool := parents.all fun parent =>
  match lookup env parent with
  | some (.classification _ ds) =>
      implementations.all (fun id => ds.contains id) &&
      classRank ranks parent < classRank ranks entry.id
  | _ => false

def validEntry (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Bool :=
  match entry.declaration with
  | .marker => true
  | .implementation marker representation capabilities =>
      isMarker env marker && decide capabilities.Nodup && decide (representation.Valid env marker capabilities)
  | .classification parents implementations =>
      decide parents.Nodup && decide implementations.Nodup && !implementations.isEmpty &&
      implementations.length ≤ 64 &&
      implementations.all (fun id => (implementationMarker env id).isSome) &&
      validParents env ranks entry parents implementations
  | .global implementation => (implementationMarker env implementation).isSome &&
      !presentedImplementation env implementation && !smoothImplementation env implementation
  | .family f => decide (f.Valid env)
  | .affine implementation data => validAffine env entry.id implementation data
  | .smoothAffine implementation coordinates => validSmoothAffine env implementation coordinates
  | .metric family object gram => validMetric env family object gram
  | .metricEvidence metric evidence => validMetricEvidence env metric evidence
  | .frame family object matrix inverse => FrameDeclarations.checkFrame env family object matrix inverse
  | .baseDimension => NatureDimension.checkBaseDimension env
  | .quantity dimension => NatureDimension.checkQuantity env dimension
  | .reading family object quantities => NatureDimension.checkReading env family object quantities
  | .scale quantity magnitude => NatureDimension.checkScale env quantity magnitude
  | .physicalMetric family object metric reading value entries =>
      NatureDimension.checkPhysicalMetric env family object metric reading value entries

structure Environment.Valid (env : Environment) : Prop where
  bounded : env.length ≤ 4096
  unique : (env.map Entry.id).Nodup
  declarations : ∀ entry ∈ env, entry.Valid env (classRanks env)

def validEnvironment (env : Environment) : Bool :=
  decide (env.length ≤ 4096) && decide (env.map Entry.id).Nodup && env.all (validEntry env (classRanks env))

/-! ### One check for each distinct evidence declaration

The check of an evidence declaration multiplies its certificate with the Gram
matrix of its metric. Evidence declarations that repeat one metric and one
kind carry one certificate, so the compiled audit runs that check once and
accepts an equal declaration by comparison. `validEnvironment` above stays the
definition that `Entry.Valid` and every theorem read;
`validEnvironment_eq_once` proves that the compiled audit computes it. -/

/-- An evidence declaration: the declarations that `validEntriesOnce` checks
once. -/
def Declaration.isEvidence : Declaration → Bool
  | .metricEvidence .. => true
  | _ => false

/-- `entries.all (validEntry env ranks)`, where an evidence declaration equal
to one in `accepted` is accepted without its check. `accepted` holds the
evidence declarations that passed. -/
def validEntriesOnce (env : Environment) (ranks : List (DeclId × Nat)) :
    List Declaration → List Entry → Bool
  | _, [] => true
  | accepted, entry :: rest =>
    if entry.declaration.isEvidence then
      if accepted.contains entry.declaration then validEntriesOnce env ranks accepted rest
      else validEntry env ranks entry && validEntriesOnce env ranks (entry.declaration :: accepted) rest
    else validEntry env ranks entry && validEntriesOnce env ranks accepted rest

/-- The check of an evidence entry reads its declaration, not its id. -/
theorem validEntry_evidence (env : Environment) (ranks : List (DeclId × Nat)) {entry other : Entry}
    (evidence : entry.declaration.isEvidence = true) (same : other.declaration = entry.declaration) :
    validEntry env ranks other = validEntry env ranks entry := by
  cases h : entry.declaration <;> simp [h, Declaration.isEvidence] at evidence
  simp [validEntry, h, same]

theorem validEntriesOnce_eq_all (env : Environment) (ranks : List (DeclId × Nat)) :
    ∀ (entries : List Entry) (accepted : List Declaration),
      (∀ entry : Entry, entry.declaration ∈ accepted → validEntry env ranks entry = true) →
      validEntriesOnce env ranks accepted entries = entries.all (validEntry env ranks)
  | [], _, _ => rfl
  | entry :: rest, accepted, invariant => by
    simp only [validEntriesOnce, List.all_cons]
    by_cases evidence : entry.declaration.isEvidence = true
    · simp only [evidence, ite_true]
      by_cases seen : accepted.contains entry.declaration = true
      · simp only [seen, ite_true]
        rw [invariant entry (List.contains_iff_mem.mp seen), Bool.true_and]
        exact validEntriesOnce_eq_all env ranks rest accepted invariant
      · simp only [seen]
        cases valid : validEntry env ranks entry with
        | false => simp
        | true =>
          simp only [Bool.true_and]
          refine validEntriesOnce_eq_all env ranks rest _ fun other member => ?_
          cases List.mem_cons.mp member with
          | inl same => rw [validEntry_evidence env ranks evidence same, valid]
          | inr member => exact invariant other member
    · simp only [evidence]
      rw [validEntriesOnce_eq_all env ranks rest accepted invariant]
      simp

/-- `validEnvironment`, with one check for each distinct evidence declaration. -/
def validEnvironmentOnce (env : Environment) : Bool :=
  decide (env.length ≤ 4096) && decide (env.map Entry.id).Nodup &&
    validEntriesOnce env (classRanks env) [] env

/-- The compiled audit is `validEnvironment`. -/
@[csimp] theorem validEnvironment_eq_once : @validEnvironment = @validEnvironmentOnce := by
  funext env
  simp only [validEnvironment, validEnvironmentOnce]
  rw [validEntriesOnce_eq_all env (classRanks env) env [] (fun _ member => nomatch member)]

/-- Backend checks, tied to the exact input. No public wire reader accepts a
frontend-authored CheckedEnvironment or CheckedApplication. -/
structure CheckedEnvironment where
  environment : Environment
  accepted : validEnvironment environment = true

def checkEnvironment (env : Environment) : Except String CheckedEnvironment :=
  if accepted : validEnvironment env = true then .ok ⟨env, accepted⟩
  else .error "invalid indexed declaration environment"

structure CheckedApplication (env : CheckedEnvironment) where
  application : Application
  accepted : validApplication env.environment application = true

def checkApplication (env : CheckedEnvironment) (app : Application) :
    Except String (CheckedApplication env) :=
  if accepted : validApplication env.environment app = true then .ok ⟨app, accepted⟩
  else .error "invalid indexed family application"

end VastitasKernel.Indexed
