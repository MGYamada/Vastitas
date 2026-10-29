import VastitasOracle.GeometryCompatibility
import VastitasOracle.IndexedSemantics
import VastitasKernel.Runtime

/-! Finite geometry result compatibility at the actual declared primitive
boundary. The erased results agree with the retained Stage 0 runtime operations.
This does not identify nominal objects, assert arbitrary geometric axioms, or
prove whole-source rewriting or native compiler correctness. -/
namespace VastitasOracle.GeometryResults
open VastitasKernel VastitasKernel.Indexed Core.Semantics

def eraseObject (object : Runtime.Object) : IndexedRuntime.Object := ⟨object.dimension⟩
def erasePoint (point : Runtime.Point) : IndexedRuntime.Point :=
  ⟨eraseObject point.target, eraseObject point.source⟩
def eraseMorphism (map : Runtime.Morphism) : IndexedRuntime.Morphism :=
  ⟨eraseObject map.source, eraseObject map.target⟩

/-- Resolve the actual declaration, then use the runtime operation already
related to logical evaluation by `primitive_runtime_erasure`. -/
def declaredRuntime (env : Core.Declarations) (id : DeclId)
    (inputs : List PrimitiveRuntimeValue) : Option PrimitiveRuntimeValue :=
  (env.primitive? id).bind fun binding => evalRuntimePrimitive binding inputs

/-- This composition uses the exact binding looked up by the Core evaluator.
Typed totality supplies successful evaluation; this lemma identifies its erased
result, without postulating a second source evaluator. -/
theorem declared_primitive_erasure {env : Core.Declarations} {id : DeclId}
    {values : List Value} {value : Value}
    (evaluated : ((env.primitive? id).bind fun binding =>
      evalPrimitive env.indexed binding values) = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧
      erasePrimitiveValue value = some output ∧ declaredRuntime env id inputs = some output := by
  cases found : env.primitive? id with
  | none => simp [found] at evaluated
  | some binding =>
      simp only [found, Option.bind_some] at evaluated
      obtain ⟨inputs, output, erasedInputs, erasedOutput, runtime⟩ :=
        IndexedSemantics.primitive_runtime_erasure evaluated
      exact ⟨inputs, output, erasedInputs, erasedOutput, by simpa [declaredRuntime, found] using runtime⟩

variable {env : Core.Declarations} {profile : GeometryProfile DeclId}

/-- Every admitted profile, including coherently renamed and multi-implementation
profiles, binds Affine to descriptor construction. No library spelling occurs in
the statement. -/
theorem affine_result (accepted : profile.valid env = true) (base : BaseKind)
    (oldBase : Runtime.Base) (dimension : Nat) :
    declaredRuntime env (profile.setting base).affine [.natural dimension] =
      some (.object (eraseObject (Runtime.affine oldBase dimension))) := by
  have contract := GeometryCompatibility.setting_contracts accepted base
  simp only [GeometrySetting.valid, Bool.and_eq_true] at contract
  have descriptor := contract.1.1.1.1.1.2
  cases found : env.primitive? (profile.setting base).affine with
  | none => simp [found] at descriptor
  | some binding =>
      cases binding <;> simp [found] at descriptor
      case descriptor implementation =>
        simp [declaredRuntime, found, evalRuntimePrimitive, eraseObject,
          Runtime.affine, IndexedRuntime.descriptor]

theorem base_result (accepted : profile.valid env = true) (base : BaseKind)
    (oldBase : Runtime.Base) :
    declaredRuntime env (profile.setting base).base [] =
      some (.object (eraseObject (Runtime.baseObject oldBase))) := by
  have contract := GeometryCompatibility.setting_contracts accepted base
  simp only [GeometrySetting.valid, Bool.and_eq_true, beq_iff_eq] at contract
  simp [declaredRuntime, contract.1.1.1.1.2, evalRuntimePrimitive,
    eraseObject, Runtime.baseObject, Runtime.affine, IndexedRuntime.baseObject,
    IndexedRuntime.descriptor]

theorem origin_result (accepted : profile.valid env = true) (base : BaseKind)
    (object : Runtime.Object) :
    declaredRuntime env (profile.setting base).origin [.object (eraseObject object)] =
      some (.point (erasePoint (Runtime.origin object))) := by
  have contract := (GeometryCompatibility.origin_and_package accepted base).1
  simp [declaredRuntime, contract, evalRuntimePrimitive, erasePoint, eraseObject,
    Runtime.origin, Runtime.baseObject, Runtime.affine, IndexedRuntime.origin,
    IndexedRuntime.baseObject, IndexedRuntime.descriptor]

theorem identity_result (accepted : profile.valid env = true) (base : BaseKind)
    (object : Runtime.Object) :
    declaredRuntime env (profile.setting base).identity [.object (eraseObject object)] =
      some (.morphism (eraseMorphism (Runtime.idMap object))) := by
  have contract := GeometryCompatibility.setting_contracts accepted base
  simp only [GeometrySetting.valid, Bool.and_eq_true, beq_iff_eq] at contract
  simp [declaredRuntime, contract.1.1.2, evalRuntimePrimitive, eraseMorphism,
    Runtime.idMap, IndexedRuntime.identity]

theorem dimension_result (accepted : profile.valid env = true) (base : BaseKind)
    (object : Runtime.Object) :
    declaredRuntime env (profile.setting base).dimension [.object (eraseObject object)] =
      some (.natural object.dimension) := by
  have contract := GeometryCompatibility.setting_contracts accepted base
  simp only [GeometrySetting.valid, Bool.and_eq_true, beq_iff_eq] at contract
  simp [declaredRuntime, contract.1.2, evalRuntimePrimitive, eraseObject]

theorem compose_result (accepted : profile.valid env = true) (after before : Runtime.Morphism) :
    declaredRuntime env profile.compose [.morphism (eraseMorphism after), .morphism (eraseMorphism before)] =
      some (.morphism (eraseMorphism (Runtime.composeMap after before))) := by
  simp only [GeometryProfile.valid, Bool.and_eq_true, beq_iff_eq] at accepted
  simp [declaredRuntime, accepted.1.2, evalRuntimePrimitive, eraseMorphism,
    Runtime.composeMap, IndexedRuntime.compose]

theorem apply_result (accepted : profile.valid env = true) (map : Runtime.Morphism) (point : Runtime.Point) :
    declaredRuntime env profile.apply [.morphism (eraseMorphism map), .point (erasePoint point)] =
      some (.point (erasePoint (Runtime.applyMap map point))) := by
  simp only [GeometryProfile.valid, Bool.and_eq_true, beq_iff_eq] at accepted
  simp [declaredRuntime, accepted.2, evalRuntimePrimitive, eraseMorphism, erasePoint,
    Runtime.applyMap, IndexedRuntime.apply]

/-- The profile premise above comes from the actual public checker. Its runtime
equations can therefore be used with the exact accepted declaration environment.
Protocols 2–6 have the corresponding `LegacySource.checked_profile` theorem. -/
theorem wire_dimension_result {json : Lean.Json} (accepted : Wire.CheckedInput json requireMain)
    (profile : GeometryProfile DeclId)
    (selected : accepted.checked.authority.headers.declarations.resolved.geometry = some profile)
    (base : BaseKind) (object : Runtime.Object) :
    declaredRuntime accepted.checked.authority.headers.declarations.resolved.declarations
      (profile.setting base).dimension [.object (eraseObject object)] = some (.natural object.dimension) :=
  dimension_result (GeometryCompatibility.checked_profile
    accepted.checked.authority.headers.declarations profile selected).2 base object

end VastitasOracle.GeometryResults
