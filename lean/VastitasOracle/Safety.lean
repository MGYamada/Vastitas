import VastitasKernel.Semantics
import VastitasOracle.Core

/-!
Semantic lemmas for the actual runtime values and nominal type indices.

This module deliberately does not yet assert whole-term or checker soundness.
Those obligations additionally require a typing derivation from the actual
checker and a well-founded evaluation of acyclic function calls.
-/
namespace VastitasOracle.Safety

open VastitasKernel VastitasKernel.Semantics

theorem unary_total_and_typed (world : World) (op : UnaryOp)
    (argTy resultTy : Ty) (operand : Value)
    (rule : Typing.UnaryTyping op argTy resultTy)
    (typed : ValueHasType world operand argTy) :
    ∃ value, evalUnary op operand = some value ∧ ValueHasType world value resultTy := by
  cases op <;> obtain ⟨rfl, rfl⟩ := rule <;>
    cases operand <;> simp_all [ValueHasType, evalUnary]

theorem binary_total_and_typed (world : World) (op : BinaryOp)
    (leftTy rightTy resultTy : Ty) (left right : Value)
    (rule : Typing.BinaryTyping op leftTy rightTy resultTy)
    (leftTyped : ValueHasType world left leftTy)
    (rightTyped : ValueHasType world right rightTy) :
    ∃ value, evalBinary op left right = some value ∧ ValueHasType world value resultTy := by
  have same : leftTy = rightTy := rule.1
  subst rightTy
  cases leftTy <;> cases left <;> simp only [ValueHasType] at leftTyped <;> try contradiction
  all_goals
    cases right <;> simp only [ValueHasType] at rightTyped <;> try contradiction
  all_goals
    cases op <;> simp_all [Typing.BinaryTyping, evalBinary, evalNatBinary, evalIntBinary,
      ValueHasType]

theorem runtimeBase_injective : Function.Injective runtimeBase := by
  intro left right equal
  cases left <;> cases right <;> simp_all [runtimeBase]

theorem affine_has_base (base : BaseKind) (dimension : Nat) :
    ObjectHasBase (Runtime.affine (runtimeBase base) dimension) base := by
  exact ⟨rfl, rfl⟩

theorem base_denotes (world : World) (base : BaseKind) :
    RefDenotes world (.base base) (Runtime.baseObject (runtimeBase base)) := by
  exact ⟨rfl, affine_has_base base 0⟩

theorem denotes_unique (world : World) (ref : ObjectRef) (left right : Runtime.Object)
    (hl : RefDenotes world ref left) (hr : RefDenotes world ref right) :
    left = right := Option.some.inj (hl.1.symm.trans hr.1)

theorem worldExtends_refl (world : World) : WorldExtends world world := by
  intro _ _ h
  exact h

theorem worldExtends_trans (first second third : World)
    (h₁ : WorldExtends first second) (h₂ : WorldExtends second third) :
    WorldExtends first third := by
  intro ref object h
  exact h₂ ref object (h₁ ref object h)

theorem bindLocal_denotes (world : World) (base : BaseKind) (id : Nat)
    (object : Runtime.Object) (typed : ObjectHasBase object base) :
    RefDenotes (bindLocal world base id object) (.local base id) object := by
  exact ⟨by simp [interpretRef, bindLocal], typed⟩

theorem bindLocal_fresh_extends (world : World) (base : BaseKind) (id : Nat)
    (object : Runtime.Object) (fresh : interpretRef world (.local base id) = none) :
    WorldExtends world (bindLocal world base id object) := by
  intro ref previous found
  cases ref with
  | base b => exact found
  | «local» b n =>
      by_cases equal : ObjectRef.local b n = ObjectRef.local base id
      · rw [equal] at found
        rw [fresh] at found
        contradiction
      · simpa [interpretRef, bindLocal, equal] using found

theorem denotes_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (ref : ObjectRef) (object : Runtime.Object)
    (denotes : RefDenotes before ref object) : RefDenotes after ref object :=
  ⟨extension ref object denotes.1, denotes.2⟩

theorem valueHasType_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (value : Value) (ty : Ty)
    (typed : ValueHasType before value ty) : ValueHasType after value ty := by
  cases value <;> cases ty <;> simp only [ValueHasType] at typed ⊢
  all_goals first
    | contradiction
    | trivial
    | exact typed
    | exact ⟨denotes_of_worldExtends before after extension _ _ typed.1,
        denotes_of_worldExtends before after extension _ _ typed.2⟩

theorem valueHasObjectRef_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (value : Value) (ref : Option ObjectRef)
    (typed : ValueHasObjectRef before value ref) : ValueHasObjectRef after value ref := by
  cases ref with
  | none => trivial
  | some ref =>
      obtain ⟨object, equal, denotes⟩ := typed
      exact ⟨object, equal, denotes_of_worldExtends before after extension ref object denotes⟩

theorem valueHasResultType_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (value : Value) (result : ResultType)
    (typed : ValueHasResultType before value result) :
    ValueHasResultType after value result :=
  ⟨valueHasType_of_worldExtends before after extension value result.ty typed.1,
    valueHasObjectRef_of_worldExtends before after extension value result.objectRef typed.2⟩

theorem contextHasType_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (env : Environment) (ctx : Typing.Context)
    (typed : ContextHasType before env ctx) : ContextHasType after env ctx := by
  intro binding member
  obtain ⟨value, found, valid⟩ := typed binding member
  exact ⟨value, found, valueHasResultType_of_worldExtends before after extension value _ valid⟩

theorem lookupBinding_member (ctx : Typing.Context) (symbol : Nat) (result : ResultType)
    (found : Typing.lookupBinding ctx symbol = some result) :
    ∃ binding ∈ ctx, binding.symbol = symbol ∧ binding.resultType = result := by
  unfold Typing.lookupBinding at found
  cases lookup : ctx.find? (fun binding => binding.symbol == symbol) with
  | none => simp [lookup] at found
  | some binding =>
      simp only [lookup, Option.map_some, Option.some.injEq] at found
      exact ⟨binding, List.mem_of_find?_eq_some lookup,
        eq_of_beq (List.find?_some (p := fun b : CheckedParam => b.symbol == symbol) lookup), found⟩

theorem lookupBinding_none (ctx : Typing.Context) (symbol : Nat)
    (absent : Typing.lookupBinding ctx symbol = none) :
    ∀ binding ∈ ctx, binding.symbol ≠ symbol := by
  unfold Typing.lookupBinding at absent
  have none : ctx.find? (fun binding => binding.symbol == symbol) = none := by
    cases found : ctx.find? (fun binding => binding.symbol == symbol) with
    | none => rfl
    | some binding => simp [found] at absent
  intro binding member equal
  have different := List.find?_eq_none.mp none binding member
  exact different (by simp [equal])

theorem variable_value_exists (world : World) (env : Environment) (ctx : Typing.Context)
    (symbol : Nat) (result : ResultType)
    (context : ContextHasType world env ctx)
    (found : Typing.lookupBinding ctx symbol = some result) :
    ∃ value, env symbol = some value ∧ ValueHasResultType world value result := by
  obtain ⟨binding, member, symbolEq, resultEq⟩ := lookupBinding_member ctx symbol result found
  obtain ⟨value, bound, typed⟩ := context binding member
  exact ⟨value, symbolEq ▸ bound, resultEq ▸ typed⟩

theorem context_bindValue (world : World) (env : Environment) (ctx : Typing.Context)
    (symbol : Nat) (result : ResultType) (value : Value)
    (context : ContextHasType world env ctx)
    (fresh : Typing.lookupBinding ctx symbol = none)
    (typed : ValueHasResultType world value result) :
    ContextHasType world (bindValue env symbol value) (⟨symbol, result⟩ :: ctx) := by
  intro binding member
  simp only [List.mem_cons] at member
  obtain rfl | member := member
  · exact ⟨value, by simp [bindValue], typed⟩
  · obtain ⟨old, found, oldTyped⟩ := context binding member
    exact ⟨old, by simpa [bindValue, lookupBinding_none ctx symbol fresh binding member] using found,
      oldTyped⟩

theorem valueHasType_references_defined (world : World) (value : Value) (ty : Ty)
    (typed : ValueHasType world value ty) : WorldDefinedOn world ty.refs := by
  cases value <;> cases ty <;> simp only [ValueHasType] at typed <;> try contradiction
  all_goals
    intro ref member
    simp only [Ty.refs, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals
    obtain rfl | rfl := member
    · exact ⟨_, typed.1.1⟩
    · exact ⟨_, typed.2.1⟩

theorem context_references_defined (world : World) (env : Environment) (ctx : Typing.Context)
    (context : ContextHasType world env ctx) : WorldDefinedOn world (Typing.contextRefs ctx) := by
  intro ref member
  obtain ⟨binding, inCtx, inRefs⟩ := List.mem_flatMap.mp member
  obtain ⟨value, _, typed⟩ := context binding inCtx
  simp only [Typing.resultRefs, List.mem_append] at inRefs
  obtain inRef | inTy := inRefs
  · cases h : binding.resultType.objectRef with
    | none => simp [h] at inRef
    | some obj =>
        have equal : ref = obj := by simpa [h] using inRef
        subst ref
        have known := typed.2
        rw [h] at known
        obtain ⟨object, _, denotes⟩ := known
        exact ⟨object, denotes.1⟩
  · exact valueHasType_references_defined world value binding.ty typed.1 ref inTy

theorem valuesHaveTypes_of_worldExtends (before after : World)
    (extension : WorldExtends before after) (values : List Value) (results : List ResultType)
    (typed : ValuesHaveTypes before values results) : ValuesHaveTypes after values results := by
  induction values generalizing results with
  | nil => cases results <;> exact typed
  | cons value values ih =>
      cases results with
      | nil => exact typed
      | cons result results =>
          exact ⟨valueHasResultType_of_worldExtends before after extension value result typed.1,
            ih results typed.2⟩

theorem worldUnchangedOutside_refl (world : World) (changed : List ObjectRef) :
    WorldUnchangedOutside world world changed := by
  intro _ _
  rfl

theorem worldUnchangedOutside_trans (first second third : World)
    (left right : List ObjectRef)
    (h₁ : WorldUnchangedOutside first second left)
    (h₂ : WorldUnchangedOutside second third right) :
    WorldUnchangedOutside first third (left ++ right) := by
  intro ref absent
  have pair : ref ∉ left ∧ ref ∉ right := by simpa using absent
  exact (h₂ ref pair.2).trans (h₁ ref pair.1)

theorem worldUnchangedOutside_mono (before after : World)
    (small large : List ObjectRef)
    (subset : ∀ ref ∈ small, ref ∈ large)
    (unchanged : WorldUnchangedOutside before after small) :
    WorldUnchangedOutside before after large := by
  intro ref absent
  exact unchanged ref (fun member => absent (subset ref member))

theorem bindLocal_unchangedOutside (world : World) (base : BaseKind) (id : Nat)
    (object : Runtime.Object) :
    WorldUnchangedOutside world (bindLocal world base id object) [.local base id] := by
  intro ref absent
  have different : ref ≠ .local base id := by simpa using absent
  cases ref <;> simp [interpretRef, bindLocal, different]

theorem fresh_after_unchanged (before after : World) (changed later : List ObjectRef)
    (unchanged : WorldUnchangedOutside before after changed)
    (fresh : WorldFreshFor before later)
    (disjoint : ∀ ref ∈ later, ref ∉ changed) : WorldFreshFor after later := by
  intro ref member
  exact (unchanged ref (disjoint ref member)).trans (fresh ref member)

/-- Object aliases refer to one descriptor even when reached by different terms. -/
theorem aliased_object_values_agree (world : World) (ref : ObjectRef)
    (left right : Runtime.Object)
    (hl : ValueHasObjectRef world (.object left) (some ref))
    (hr : ValueHasObjectRef world (.object right) (some ref)) : left = right := by
  obtain ⟨left', heql, hl⟩ := hl
  obtain ⟨right', heqr, hr⟩ := hr
  cases heql
  cases heqr
  exact denotes_unique world ref _ _ hl hr

theorem origin_has_type (world : World) (ref : ObjectRef) (object : Runtime.Object)
    (denotes : RefDenotes world ref object) :
    ValueHasType world (.point (Runtime.origin object))
      (.point ref (.base ref.baseKind)) := by
  refine ⟨denotes, ?_⟩
  simpa [Runtime.origin, denotes.2.1] using base_denotes world ref.baseKind

theorem identity_has_type (world : World) (ref : ObjectRef) (object : Runtime.Object)
    (denotes : RefDenotes world ref object) :
    ValueHasType world (.morphism (Runtime.idMap object)) (.morphism ref ref) :=
  ⟨denotes, denotes⟩

theorem application_has_type (world : World) (x y s : ObjectRef)
    (map : Runtime.Morphism) (point : Runtime.Point)
    (hm : ValueHasType world (.morphism map) (.morphism x y))
    (hp : ValueHasType world (.point point) (.point x s)) :
    ValueHasType world (.point (Runtime.applyMap map point)) (.point y s) :=
  ⟨hm.2, hp.2⟩

/-- A well-typed apply really has matching runtime endpoints after erasure. -/
theorem application_endpoints_match (world : World) (x y s : ObjectRef)
    (map : Runtime.Morphism) (point : Runtime.Point)
    (hm : ValueHasType world (.morphism map) (.morphism x y))
    (hp : ValueHasType world (.point point) (.point x s)) :
    map.source = point.target := denotes_unique world x map.source point.target hm.1 hp.1

theorem composition_has_type (world : World) (x y z : ObjectRef)
    (g f : Runtime.Morphism)
    (hg : ValueHasType world (.morphism g) (.morphism y z))
    (hf : ValueHasType world (.morphism f) (.morphism x y)) :
    ValueHasType world (.morphism (Runtime.composeMap g f)) (.morphism x z) :=
  ⟨hf.1, hg.2⟩

theorem composition_endpoints_match (world : World) (x y z : ObjectRef)
    (g f : Runtime.Morphism)
    (hg : ValueHasType world (.morphism g) (.morphism y z))
    (hf : ValueHasType world (.morphism f) (.morphism x y)) :
    f.target = g.source := denotes_unique world y f.target g.source hf.2 hg.1

theorem package_has_type (world : World) (ref : ObjectRef)
    (object : Runtime.Object) (point : Runtime.Point)
    (ho : RefDenotes world ref object)
    (hp : ValueHasType world (.point point) (.point ref (.base ref.baseKind))) :
    ValueHasType world (.pointed ⟨object, point⟩) (.pointed ref.baseKind) := by
  refine ⟨ho.2, denotes_unique world ref point.target object hp.1 ho, ?_⟩
  exact Option.some.inj hp.2.1.symm

theorem unpack_scheme_has_type (world : World) (base : BaseKind) (id : Nat)
    (package : Runtime.Pointed)
    (typed : ValueHasType world (.pointed package) (.pointed base)) :
    RefDenotes (bindLocal world base id package.scheme) (.local base id) package.scheme :=
  bindLocal_denotes world base id package.scheme typed.1

theorem unpack_point_has_type (world : World) (base : BaseKind) (id : Nat)
    (package : Runtime.Pointed)
    (typed : ValueHasType world (.pointed package) (.pointed base)) :
    ValueHasType (bindLocal world base id package.scheme) (.point package.point)
      (unpackedPointType base id) := by
  change RefDenotes _ _ _ ∧ RefDenotes _ _ _
  constructor
  · rw [typed.2.1]
    exact unpack_scheme_has_type world base id package typed
  · rw [typed.2.2]
    exact base_denotes _ base

theorem pack_unpack_preserves_typed_association (world : World) (base : BaseKind)
    (id : Nat) (package : Runtime.Pointed)
    (typed : ValueHasType world (.pointed package) (.pointed base)) :
    package.point.target = package.scheme ∧
      ValueHasType (bindLocal world base id package.scheme) (.point package.point)
        (unpackedPointType base id) :=
  ⟨typed.2.1, unpack_point_has_type world base id package typed⟩

/-- Successful checking of apply entails preservation for actual runtime values. -/
theorem checkApply_preserves_runtime_type (world : World) (mapTy pointTy resultTy : Ty)
    (map : Runtime.Morphism) (point : Runtime.Point)
    (accepted : checkApply mapTy pointTy = .ok resultTy)
    (hm : ValueHasType world (.morphism map) mapTy)
    (hp : ValueHasType world (.point point) pointTy) :
    ValueHasType world (.point (Runtime.applyMap map point)) resultTy := by
  obtain ⟨x, y, s, rfl, rfl, rfl, _, _⟩ := checkApply_sound _ _ _ accepted
  exact application_has_type world x y s map point hm hp

theorem checkCompose_preserves_runtime_type (world : World) (gTy fTy resultTy : Ty)
    (g f : Runtime.Morphism)
    (accepted : checkCompose gTy fTy = .ok resultTy)
    (hg : ValueHasType world (.morphism g) gTy)
    (hf : ValueHasType world (.morphism f) fTy) :
    ValueHasType world (.morphism (Runtime.composeMap g f)) resultTy := by
  obtain ⟨x, y, z, rfl, rfl, rfl, _, _⟩ := checkCompose_sound _ _ _ accepted
  exact composition_has_type world x y z g f hg hf

theorem checkPack_preserves_runtime_type (world : World) (ref : ObjectRef)
    (pointTy resultTy : Ty) (object : Runtime.Object) (point : Runtime.Point)
    (accepted : checkPack ref pointTy = .ok resultTy)
    (ho : RefDenotes world ref object)
    (hp : ValueHasType world (.point point) pointTy) :
    ValueHasType world (.pointed ⟨object, point⟩) resultTy := by
  obtain ⟨rfl, rfl⟩ := checkPack_sound _ _ _ accepted
  exact package_has_type world ref object point ho hp

theorem interpret_pullbackWorld (caller : World)
    (substitution : List (ObjectRef × ObjectRef))
    (fixesBases : ∀ base, renameRef substitution (.base base) = .base base)
    (ref : ObjectRef) :
    interpretRef (pullbackWorld caller substitution) ref =
      interpretRef caller (renameRef substitution ref) := by
  cases ref with
  | base base => simp [interpretRef, fixesBases]
  | «local» base id => rfl

theorem refDenotes_pullbackWorld (caller : World)
    (substitution : List (ObjectRef × ObjectRef))
    (fixesBases : ∀ base, renameRef substitution (.base base) = .base base)
    (preservesBases : BasePreserving substitution)
    (ref : ObjectRef) (object : Runtime.Object) :
    RefDenotes (pullbackWorld caller substitution) ref object ↔
      RefDenotes caller (renameRef substitution ref) object := by
  simp only [RefDenotes, interpret_pullbackWorld caller substitution fixesBases,
    preservesBases ref]

/-- Function argument substitution preserves the interpretation of every type.
The hypotheses hold for substitution tables built from formal object parameters;
base references themselves are never formal parameters. -/
theorem valueHasType_pullbackWorld (caller : World)
    (substitution : List (ObjectRef × ObjectRef))
    (fixesBases : ∀ base, renameRef substitution (.base base) = .base base)
    (preservesBases : BasePreserving substitution)
    (value : Value) (ty : Ty) :
    ValueHasType (pullbackWorld caller substitution) value ty ↔
      ValueHasType caller value (ty.rename substitution) := by
  cases value <;> cases ty <;>
    simp [ValueHasType, Ty.rename,
      refDenotes_pullbackWorld caller substitution fixesBases preservesBases]

/-- Equal runtime descriptors do not collapse distinct nominal references. -/
theorem distinct_brands_can_denote_same_object (base : BaseKind) (left right : Nat)
    (object : Runtime.Object) (typed : ObjectHasBase object base) :
    ∃ world : World,
      RefDenotes world (.local base left) object ∧
      RefDenotes world (.local base right) object := by
  refine ⟨fun _ => some object, ?_, ?_⟩ <;> exact ⟨rfl, typed⟩

theorem interpret_restrictWorld (world : World) (allowed : List ObjectRef)
    (ref : ObjectRef) (inScope : ref.InScope allowed) :
    interpretRef (restrictWorld allowed world) ref = interpretRef world ref := by
  cases ref with
  | base _ => rfl
  | «local» base id =>
      change ObjectRef.local base id ∈ allowed at inScope
      simp [interpretRef, restrictWorld, inScope]

theorem refDenotes_restrictWorld (world : World) (allowed : List ObjectRef)
    (ref : ObjectRef) (object : Runtime.Object) (inScope : ref.InScope allowed)
    (denotes : RefDenotes world ref object) :
    RefDenotes (restrictWorld allowed world) ref object := by
  exact ⟨(interpret_restrictWorld world allowed ref inScope).trans denotes.1, denotes.2⟩

theorem valueHasType_restrictWorld (world : World) (allowed : List ObjectRef)
    (value : Value) (ty : Ty) (inScope : ty.Scoped allowed)
    (typed : ValueHasType world value ty) :
    ValueHasType (restrictWorld allowed world) value ty := by
  cases value <;> cases ty <;> simp only [ValueHasType] at typed ⊢
  all_goals first
    | contradiction
    | trivial
    | exact typed
    | exact ⟨refDenotes_restrictWorld world allowed _ _ (inScope _ (by simp [Ty.refs])) typed.1,
        refDenotes_restrictWorld world allowed _ _ (inScope _ (by simp [Ty.refs])) typed.2⟩

/-- The executable escape check permits discarding precisely the hidden brands.
The surviving value keeps the same runtime descriptor and endpoint interpretation. -/
theorem checkScope_preserves_runtime_type (world : World) (allowed : List ObjectRef)
    (value : Value) (ty : Ty) (accepted : checkScope allowed ty = .ok ())
    (typed : ValueHasType world value ty) :
    ValueHasType (restrictWorld allowed world) value ty :=
  valueHasType_restrictWorld world allowed value ty (checkScope_sound allowed ty accepted) typed

theorem refDenotes_before_extension (before after : World)
    (extension : WorldExtends before after) (ref : ObjectRef) (object : Runtime.Object)
    (defined : ∃ previous, interpretRef before ref = some previous)
    (denotes : RefDenotes after ref object) : RefDenotes before ref object := by
  obtain ⟨previous, found⟩ := defined
  have same : previous = object := Option.some.inj
    ((extension ref previous found).symm.trans denotes.1)
  exact ⟨same ▸ found, denotes.2⟩

theorem valueHasType_before_extension (before after : World)
    (extension : WorldExtends before after) (value : Value) (ty : Ty)
    (defined : WorldDefinedOn before ty.refs)
    (typed : ValueHasType after value ty) : ValueHasType before value ty := by
  cases value <;> cases ty <;> simp only [ValueHasType] at typed ⊢
  all_goals first
    | contradiction
    | trivial
    | exact typed
    | exact ⟨refDenotes_before_extension before after extension _ _
          (defined _ (by simp [Ty.refs])) typed.1,
        refDenotes_before_extension before after extension _ _
          (defined _ (by simp [Ty.refs])) typed.2⟩

theorem valuesHaveTypes_one (world : World) (values : List Value) (result : ResultType)
    (typed : ValuesHaveTypes world values [result]) :
    ∃ value, values = [value] ∧ ValueHasResultType world value result := by
  cases values with
  | nil => contradiction
  | cons value values =>
      cases values with
      | nil => exact ⟨value, rfl, typed.1⟩
      | cons _ _ => exact False.elim typed.2

theorem valuesHaveTypes_two (world : World) (values : List Value) (left right : ResultType)
    (typed : ValuesHaveTypes world values [left, right]) :
    ∃ lhs rhs, values = [lhs, rhs] ∧
      ValueHasResultType world lhs left ∧ ValueHasResultType world rhs right := by
  cases values with
  | nil => contradiction
  | cons lhs values =>
      obtain ⟨rhs, rfl, rightTyped⟩ := valuesHaveTypes_one world values right typed.2
      exact ⟨lhs, rhs, rfl, typed.1, rightTyped⟩

theorem nat_value (world : World) (value : Value) (typed : ValueHasType world value .nat) :
    ∃ n, value = .nat n := by
  cases value <;> simp_all [ValueHasType]

theorem bool_value (world : World) (value : Value) (typed : ValueHasType world value .bool) :
    ∃ b, value = .bool b := by
  cases value <;> simp_all [ValueHasType]

theorem point_value (world : World) (value : Value) (target source : ObjectRef)
    (typed : ValueHasType world value (.point target source)) :
    ∃ point, value = .point point := by
  cases value <;> simp_all [ValueHasType]

theorem morphism_value (world : World) (value : Value) (source target : ObjectRef)
    (typed : ValueHasType world value (.morphism source target)) :
    ∃ map, value = .morphism map := by
  cases value <;> simp_all [ValueHasType]

theorem pointed_value (world : World) (value : Value) (base : BaseKind)
    (typed : ValueHasType world value (.pointed base)) :
    ∃ package, value = .pointed package := by
  cases value <;> simp_all [ValueHasType]

theorem object_value (world : World) (value : Value) (base : BaseKind)
    (typed : ValueHasType world value (.object base)) :
    ∃ object, value = .object object := by
  cases value <;> simp_all [ValueHasType]

theorem adopt_local_object (world : World) (base : BaseKind) (result : ResultType)
    (object : Runtime.Object) (rule : Typing.LocalObjectResult base result)
    (typed : ObjectHasBase object base)
    (fresh : WorldFreshFor world result.objectRef.toList) :
    ∃ after, ValueHasResultType after (.object object) result ∧
      WorldExtends world after ∧ WorldUnchangedOutside world after result.objectRef.toList := by
  rcases result with ⟨ty, ref⟩
  obtain ⟨rfl, localResult⟩ := rule
  cases ref with
  | none => contradiction
  | some ref =>
      cases ref with
      | base _ => contradiction
      | «local» actual id =>
          change actual = base at localResult
          subst actual
          have absent := fresh (.local base id) (by simp)
          refine ⟨bindLocal world base id object, ?_,
            bindLocal_fresh_extends world base id object absent,
            bindLocal_unchangedOutside world base id object⟩
          exact ⟨typed, ⟨object, rfl, bindLocal_denotes world base id object typed⟩⟩

theorem builtin_total_and_typed (world : World) (op : BuiltinOp)
    (args : List ResultType) (result : ResultType) (values : List Value)
    (rule : Typing.BuiltinTyping op args result)
    (typed : ValuesHaveTypes world values args)
    (fresh : WorldFreshFor world (builtinAllocations op result)) :
    ∃ after value, evalBuiltin op values = some value ∧
      ValueHasResultType after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after (builtinAllocations op result) := by
  unfold Typing.BuiltinTyping at rule
  split at rule
  · rename_i base
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    obtain ⟨dimension, rfl⟩ := nat_value world value valueTyped.1
    obtain ⟨after, resultTyped, extension, unchanged⟩ :=
      adopt_local_object world base result _ rule (affine_has_base base dimension) fresh
    exact ⟨after, _, rfl, resultTyped, extension, unchanged⟩
  · rename_i base
    subst result
    cases values with
    | nil =>
        exact ⟨world, .object (Runtime.baseObject (runtimeBase base)), rfl,
          ⟨affine_has_base base 0, ⟨_, rfl, base_denotes world base⟩⟩,
          worldExtends_refl world, worldUnchangedOutside_refl world []⟩
    | cons _ _ => contradiction
  · rename_i base ref
    obtain ⟨rfl, rfl⟩ := rule
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    obtain ⟨object, rfl, denotes⟩ := valueTyped.2
    exact ⟨world, _, rfl, ⟨origin_has_type world ref object denotes, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i base ref
    obtain ⟨rfl, rfl⟩ := rule
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    obtain ⟨object, rfl, denotes⟩ := valueTyped.2
    exact ⟨world, _, rfl, ⟨identity_has_type world ref object denotes, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i base ref
    obtain ⟨_, rfl⟩ := rule
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    obtain ⟨object, rfl, _⟩ := valueTyped.2
    exact ⟨world, _, rfl, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i middle target source middle'
    obtain ⟨rfl, _, _, rfl⟩ := rule
    obtain ⟨lhs, rhs, rfl, lhsTyped, rhsTyped⟩ := valuesHaveTypes_two world values _ _ typed
    obtain ⟨g, rfl⟩ := morphism_value world lhs _ _ lhsTyped.1
    obtain ⟨f, rfl⟩ := morphism_value world rhs _ _ rhsTyped.1
    exact ⟨world, _, rfl,
      ⟨composition_has_type world source _ target g f lhsTyped.1 rhsTyped.1, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i source target target' test
    obtain ⟨rfl, _, _, rfl⟩ := rule
    obtain ⟨lhs, rhs, rfl, lhsTyped, rhsTyped⟩ := valuesHaveTypes_two world values _ _ typed
    obtain ⟨map, rfl⟩ := morphism_value world lhs _ _ lhsTyped.1
    obtain ⟨point, rfl⟩ := point_value world rhs _ _ rhsTyped.1
    exact ⟨world, _, rfl,
      ⟨application_has_type world _ target test map point lhsTyped.1 rhsTyped.1, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · subst result
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    obtain ⟨n, rfl⟩ := nat_value world value valueTyped.1
    exact ⟨world, _, rfl, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i element left right
    obtain ⟨rfl, rfl, rfl⟩ := rule
    obtain ⟨a, b, rfl, aTyped, bTyped⟩ := valuesHaveTypes_two world values _ _ typed
    cases element <;> cases a <;> cases b <;>
      simp only [PairElem.ty, ValueHasResultType, ValueHasType, ValueHasObjectRef] at aTyped bTyped <;>
      try contradiction
    all_goals exact ⟨world, _, rfl, ⟨rfl, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i element actual
    obtain ⟨rfl, rfl⟩ := rule
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    cases actual <;> cases value <;>
      simp only [ValueHasResultType, ValueHasType, ValueHasObjectRef] at valueTyped <;>
      try contradiction
    all_goals exact ⟨world, _, rfl, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · rename_i element actual
    obtain ⟨rfl, rfl⟩ := rule
    obtain ⟨value, rfl, valueTyped⟩ := valuesHaveTypes_one world values _ typed
    cases actual <;> cases value <;>
      simp only [ValueHasResultType, ValueHasType, ValueHasObjectRef] at valueTyped <;>
      try contradiction
    all_goals exact ⟨world, _, rfl, ⟨trivial, trivial⟩,
      worldExtends_refl world, worldUnchangedOutside_refl world []⟩
  · contradiction

theorem branch_result_typed (world : World) (yes no result chosen : ResultType)
    (value : Value) (rule : Typing.BranchTyping yes no result)
    (yesWellFormed : Typing.ResultWellFormed yes)
    (noWellFormed : Typing.ResultWellFormed no)
    (choice : chosen = yes ∨ chosen = no)
    (typed : ValueHasResultType world value chosen)
    (fresh : WorldFreshFor world (branchAllocations yes no result)) :
    ∃ after, ValueHasResultType after value result ∧ WorldExtends world after ∧
      WorldUnchangedOutside world after (branchAllocations yes no result) := by
  rcases yes with ⟨yesTy, yesRef⟩
  rcases no with ⟨noTy, noRef⟩
  rcases result with ⟨resultTy, resultRef⟩
  obtain ⟨sameTy, resultTyEq, rule⟩ := rule
  change yesTy = noTy at sameTy
  change resultTy = yesTy at resultTyEq
  subst noTy
  subst resultTy
  cases yesTy <;> simp only [Typing.ResultWellFormed] at yesWellFormed noWellFormed
  all_goals try
    have yesNone : yesRef = none := by
      cases yesRef <;> simp_all
    have noNone : noRef = none := by
      cases noRef <;> simp_all
    subst yesRef
    subst noRef
    change resultRef = none at rule
    subst resultRef
    obtain rfl | rfl := choice <;>
      exact ⟨world, typed, worldExtends_refl world, worldUnchangedOutside_refl world _⟩
  case object base =>
    by_cases equal : yesRef = noRef
    · have resultEq : resultRef = yesRef := by simpa [equal] using rule
      subst resultRef
      subst noRef
      obtain rfl | rfl := choice <;>
        exact ⟨world, typed, worldExtends_refl world, worldUnchangedOutside_refl world _⟩
    · have localResult : Typing.LocalObjectResult base ⟨.object base, resultRef⟩ := by
        simpa [equal] using rule
      have objectTyped : ValueHasType world value (.object base) := by
        obtain rfl | rfl := choice <;> exact typed.1
      obtain ⟨object, rfl⟩ := object_value world value base objectTyped
      have freshRef : WorldFreshFor world resultRef.toList := by
        simpa [branchAllocations, equal] using fresh
      obtain ⟨after, typed, extension, unchanged⟩ :=
        adopt_local_object world base _ object localResult objectTyped freshRef
      exact ⟨after, typed, extension, by simpa [branchAllocations, equal] using unchanged⟩

end VastitasOracle.Safety
