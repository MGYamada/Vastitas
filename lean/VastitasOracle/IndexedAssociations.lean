import VastitasKernel.IndexedPrimitives

set_option autoImplicit false

/-! The association contract of each primitive, read off its shape (#622).

`PrimitiveAssociation` is derived from the binding's registry shape. These
lemmas state, for each callable binding and its well-shaped operand list, the
conjunction the shape amounts to, in the order the shape checks it: the
operands' families and fixed indices, operand by operand, then the relations,
then the result; and, for each binding with listed operands, that any accepted
call has that operand list. The uncallable evidence bindings have no
association. These are the local obligations the totality and bridge proofs
destructure: a new callable binding adds its association lemma and its shape
lemma here, its totality lemma, and its named case in
`IndexedSemantics.primitive_total_and_typed`. -/
namespace VastitasOracle.IndexedAssociations

open VastitasKernel VastitasKernel.Indexed

/-- The simp set that evaluates a derived association at one constructor and
one operand list. -/
local syntax "association_simp" : tactic
local macro_rules
  | `(tactic| association_simp) => `(tactic| simp only [PrimitiveAssociation, Shape.Association,
      PrimitiveBinding.contract, PrimitiveDescriptor.ofBool, PrimitiveDescriptor.evidence, Shape.accepts,
      Shape.operandsMatch,
      Shape.operandMatches, Shape.slotsMatch, Shape.tailMatches_none_iff, Shape.tailMatches_some_iff,
      Relation.holds, Shape.refAt, Shape.applicationAt, Shape.objectAt, ResultTemplate.instantiate,
      Shape.templateSlot, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil, List.mapM_cons, List.mapM_nil,
      Option.bind_eq_bind, Option.bind_some, Option.map_some, Option.pure_def, Option.some.injEq,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, true_and, and_true, Bool.true_eq,
      ValueType.indexed.injEq, Application.mk.injEq, List.cons.injEq, Index.object.injEq,
      ObjectRef.global.injEq, Option.isSome_some, Option.isSome_none, and_assoc])

/-! ## Objects, points and morphisms -/

theorem descriptor_association {env : Environment} {implementation : DeclId} {allowed : List ObjectRef}
    {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.descriptor implementation) allowed brand [.natural] result ↔
      ∃ ty ∈ implementationType env implementation, FreshBrand allowed brand ∧ .object ty (.local ty brand) = result := by
  association_simp
  cases implementationType env implementation <;> simp

theorem global_association {env : Environment} {id : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.global id) allowed brand [] result ↔
      ∃ ty ∈ ObjectRef.type? env (.global id), .object ty (.global id) = result := by
  association_simp
  cases ObjectRef.type? env (.global id) <;> simp

theorem origin_association {env : Environment} {expected actual : ObjectType} {family base : DeclId}
    {reference : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.origin expected family base) allowed brand [.object actual reference] result ↔
      actual.Refines env expected ∧ .indexed ⟨family, [.object reference, .object (.global base)]⟩ = result := by
  association_simp

theorem identity_association {env : Environment} {expected actual : ObjectType} {family : DeclId}
    {reference : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.identity expected family) allowed brand [.object actual reference] result ↔
      actual.Refines env expected ∧ .indexed ⟨family, [.object reference, .object reference]⟩ = result := by
  association_simp

theorem dimension_association {env : Environment} {expected actual : ObjectType} {reference : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.dimension expected) allowed brand [.object actual reference] result ↔
      actual.Refines env expected ∧ .natural = result := by
  association_simp

theorem compose_association {env : Environment} {family gf ff : DeclId} {middle target source other : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.compose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩] result ↔
      gf = family ∧ ff = family ∧ middle = other ∧ .indexed ⟨family, [.object source, .object target]⟩ = result := by
  association_simp

theorem apply_association {env : Environment} {maps points mf pf : DeclId} {source target other test : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.apply maps points) allowed brand
      [.indexed ⟨mf, [.object source, .object target]⟩, .indexed ⟨pf, [.object other, .object test]⟩] result ↔
      mf = maps ∧ pf = points ∧ source = other ∧ .indexed ⟨points, [.object target, .object test]⟩ = result := by
  association_simp

/-! ## Relative morphisms over a base (Stage 2) -/

theorem relativeConstant_association {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.relativeConstant application map) allowed brand [] result ↔
      .indexed application = result := by
  association_simp

theorem relativeCompose_association {env : Environment} {family gf ff : DeclId}
    {middle target base source middle' base' : ObjectRef} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.relativeCompose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target, .object base]⟩,
        .indexed ⟨ff, [.object source, .object middle', .object base']⟩] result ↔
      gf = family ∧ ff = family ∧ middle = middle' ∧ base = base' ∧
        .indexed ⟨family, [.object source, .object target, .object base]⟩ = result := by
  association_simp

theorem relativeView_association {env : Environment} {family origin to f : DeclId}
    {source target base : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.relativeView family origin to) allowed brand
      [.indexed ⟨f, [.object source, .object target, .object base]⟩] result ↔
      f = family ∧ .global origin = base ∧
        .indexed ⟨family, [.object source, .object target, .object (.global to)]⟩ = result := by
  association_simp

theorem relativeEqual_association {env : Environment} {family : DeclId} {left right : Application}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.relativeEqual family) allowed brand [.indexed left, .indexed right] result ↔
      left.family = family ∧ right.family = family ∧ left = right ∧ .boolean = result := by
  association_simp

theorem relativeCoefficient_association {env : Environment} {family source target f x y : DeclId}
    {coordinate : Nat} {monomial : List Nat} {base : ObjectRef} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.relativeCoefficient family source target coordinate monomial) allowed brand
      [.indexed ⟨f, [.object (.global x), .object (.global y), .object base]⟩] result ↔
      f = family ∧ source = x ∧ target = y ∧ .integerPair = result := by
  association_simp

theorem relativeIntPoint_association {env : Environment} {family object base : DeclId}
    {arguments : List ValueType} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.relativeIntPoint family object base) allowed brand arguments result ↔
      arguments = ((List.range (affineArity env object)).map fun _ => .integer) ∧
        .indexed ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩ = result := by
  association_simp

theorem relativePair_association {env : Environment} {family fiber lf rf : DeclId}
    {source left base source' right base' : ObjectRef} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.relativePair family fiber) allowed brand
      [.indexed ⟨lf, [.object source, .object left, .object base]⟩,
        .indexed ⟨rf, [.object source', .object right, .object base']⟩] result ↔
      lf = family ∧ rf = family ∧ source = source' ∧ base = base' ∧ pairFactors env fiber left right base = true ∧
        .indexed ⟨family, [.object source, .object (.global fiber), .object base]⟩ = result := by
  association_simp
  cases found : plainFiber? env fiber with
  | none => simp [pairFactors, found]
  | some factors =>
    obtain ⟨l, r, b⟩ := factors
    simp only [pairFactors, found, Option.map_some, Bool.and_eq_true, beq_iff_eq, and_assoc]
    constructor
    · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp
    · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp

theorem relativeIso_association {env : Environment} {forward backward : Application × AlgebraRuntime.Map}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType} :
    ¬ PrimitiveAssociation env (.relativeIso forward backward) allowed brand arguments result := by
  simp [PrimitiveAssociation, Shape.Association, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, Shape.uncallable, ResultTemplate.instantiate]

theorem relativeCartesian_association {env : Environment} {first second inverse : Application × AlgebraRuntime.Map}
    {fiber : DeclId} {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType} :
    ¬ PrimitiveAssociation env (.relativeCartesian first second inverse fiber) allowed brand arguments result := by
  simp [PrimitiveAssociation, Shape.Association, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, Shape.uncallable, ResultTemplate.instantiate]

/-! ## Smooth maps, fibers, tapes and metrics (Stage 3) -/

theorem smoothConstant_association {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.smoothConstant application map) allowed brand [] result ↔
      .indexed application = result := by
  association_simp

theorem smoothCompose_association {env : Environment} {family gf ff : DeclId}
    {middle target source other : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.smoothCompose family) allowed brand
      [.indexed ⟨gf, [.object middle, .object target]⟩, .indexed ⟨ff, [.object source, .object other]⟩] result ↔
      gf = family ∧ ff = family ∧ middle = other ∧ .indexed ⟨family, [.object source, .object target]⟩ = result := by
  association_simp

theorem smoothEqual_association {env : Environment} {family : DeclId} {left right : Application}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.smoothEqual family) allowed brand [.indexed left, .indexed right] result ↔
      left.family = family ∧ right.family = family ∧ left = right ∧ .boolean = result := by
  association_simp

theorem smoothIntPoint_association {env : Environment} {family object point : DeclId}
    {arguments : List ValueType} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.smoothIntPoint family object point) allowed brand arguments result ↔
      arguments = ((List.range (smoothArity env object)).map fun _ => .integer) ∧
        .indexed ⟨family, [.object (.global point), .object (.global object)]⟩ = result := by
  association_simp

theorem smoothComposite_association {env : Environment} {family : DeclId} {application : Application}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.smoothComposite family) allowed brand [.indexed application] result ↔
      application.family = family ∧ .indexed application = result := by
  association_simp

theorem fiberVector_association {env : Environment} {family smooth object sf point : DeclId} {x : ObjectRef}
    {components : List ValueType} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.fiberVector family smooth object) allowed brand
      (.indexed ⟨sf, [.object (.global point), .object x]⟩ :: components) result ↔
      sf = smooth ∧ .global object = x ∧ components = ((List.range (smoothArity env object)).map fun _ => .integer) ∧
        smoothDimension? env point = some 0 ∧ .indexed ⟨family, [.object (.global object)]⟩ = result := by
  association_simp

theorem fiberAt_association {env : Environment} {family smooth ff sf point : DeclId} {x x' : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.fiberAt family smooth) allowed brand
      [.indexed ⟨ff, [.object x]⟩, .indexed ⟨sf, [.object (.global point), .object x']⟩] result ↔
      ff = family ∧ sf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧ .boolean = result := by
  association_simp

theorem fiberEqual_association {env : Environment} {family : DeclId} {left right : Application}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.fiberEqual family) allowed brand [.indexed left, .indexed right] result ↔
      left.family = family ∧ right.family = family ∧ left = right ∧ .boolean = result := by
  association_simp

theorem fiberComponent_association {env : Environment} {family object ff : DeclId} {coordinate : Nat}
    {x : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.fiberComponent family object coordinate) allowed brand
      [.indexed ⟨ff, [.object x]⟩] result ↔
      ff = family ∧ .global object = x ∧ .integerPair = result := by
  association_simp

theorem fiberPairing_association {env : Environment} {cotangent tangent cf tf : DeclId} {x x' : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.fiberPairing cotangent tangent) allowed brand
      [.indexed ⟨cf, [.object x]⟩, .indexed ⟨tf, [.object x']⟩] result ↔
      cf = cotangent ∧ tf = tangent ∧ x = x' ∧ .integerPair = result := by
  association_simp

theorem cotangentPullback_association {env : Environment} {smooth cotangent mf pf cf point : DeclId}
    {x y x' y' : ObjectRef} {mode : SmoothRuntime.PullbackMode} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.cotangentPullback smooth cotangent mode) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩,
        .indexed ⟨cf, [.object y']⟩] result ↔
      mf = smooth ∧ pf = smooth ∧ cf = cotangent ∧ x = x' ∧ y = y' ∧ smoothDimension? env point = some 0 ∧
        .indexed ⟨cotangent, [.object x]⟩ = result := by
  association_simp

theorem differential_association {env : Environment} {smooth cotangent line mf pf point : DeclId}
    {x y x' : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.differential smooth cotangent line) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] result ↔
      mf = smooth ∧ .global line = y ∧ pf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        .indexed ⟨cotangent, [.object x]⟩ = result := by
  association_simp

theorem linearize_association {env : Environment} {smooth tape mf pf point : DeclId} {x y x' : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.linearize smooth tape) allowed brand
      [.indexed ⟨mf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩] result ↔
      mf = smooth ∧ pf = smooth ∧ x = x' ∧ smoothDimension? env point = some 0 ∧
        .indexed ⟨tape, [.object x, .object y]⟩ = result := by
  association_simp

theorem cotangentBackward_association {env : Environment} {tape cotangent tf cf : DeclId} {x y y' : ObjectRef}
    {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.cotangentBackward tape cotangent) allowed brand
      [.indexed ⟨tf, [.object x, .object y]⟩, .indexed ⟨cf, [.object y']⟩] result ↔
      tf = tape ∧ cf = cotangent ∧ y = y' ∧ .indexed ⟨cotangent, [.object x]⟩ = result := by
  association_simp

theorem metricFlat_association {env : Environment} {metric object tangent cotangent tf : DeclId}
    {gram : SmoothRuntime.Matrix} {x : ObjectRef} {allowed : List ObjectRef} {brand : Nat} {result : ValueType} :
    PrimitiveAssociation env (.metricFlat metric object gram tangent cotangent) allowed brand
      [.indexed ⟨tf, [.object x]⟩] result ↔
      tf = tangent ∧ .global object = x ∧ .indexed ⟨cotangent, [.object (.global object)]⟩ = result := by
  association_simp

theorem metricSharp_association {env : Environment} {metric evidence object cotangent tangent cf : DeclId}
    {gram inverse : SmoothRuntime.Matrix} {x : ObjectRef} {allowed : List ObjectRef} {brand : Nat}
    {result : ValueType} :
    PrimitiveAssociation env (.metricSharp metric evidence object gram inverse cotangent tangent) allowed brand
      [.indexed ⟨cf, [.object x]⟩] result ↔
      cf = cotangent ∧ .global object = x ∧ .indexed ⟨tangent, [.object (.global object)]⟩ = result := by
  association_simp


/-! ## The operand list of a binding, read off its association

Each lemma inverts the shape's match operand by operand, so a theorem stated
for a binding's well-shaped operands applies to any accepted call. The
variadic bindings (`relativeIntPoint`, `smoothIntPoint`) need no shape: their
operands are the integer tail. -/

/-- Reads one operand off a match `h : operandsMatch … (operand :: operands) arguments = true`:
the argument `a`, its match `m`, and `h` for the rest. -/
local macro "operand_cons" a:ident m:ident h:ident : tactic =>
  `(tactic| (obtain ⟨$a:ident, _, equal, $m:ident, next⟩ := Shape.operandsMatch_cons_iff.mp $h
             clear $h
             subst equal
             have $h:ident := next
             clear next))
/-- Ends the operands of a shape without a tail: `h : operandsMatch … [] arguments = true`
substitutes the empty list. -/
local macro "operands_end" h:ident : tactic =>
  `(tactic| (obtain equal := Shape.tailMatches_none_iff.mp (Shape.operandsMatch_nil_iff.mp $h); subst equal))
/-- Reads an indexed operand off its match `m`: the indices `i` and their slot match `s`. -/
local macro "indexed_operand" i:ident s:ident m:ident : tactic =>
  `(tactic| (obtain ⟨$i:ident, equal, $s:ident⟩ := Shape.operandMatches_indexed_iff.mp $m; clear $m; subst equal))
/-- Reads a whole-application operand off its match `m`: the application `app`. -/
local macro "application_operand" app:ident m:ident : tactic =>
  `(tactic| (obtain ⟨$app:ident, equal, _⟩ := Shape.operandMatches_application_iff.mp $m; clear $m; subst equal))
/-- Reads an object operand off its match `m`: its type `ty` and reference `r`. -/
local macro "object_operand" ty:ident r:ident m:ident : tactic =>
  `(tactic| (obtain ⟨$ty:ident, $r:ident, equal⟩ := Shape.operandMatches_object_iff.mp $m; clear $m; subst equal))
/-- Reads a free slot off a slot match `s`: the reference `r`, and `s` for the rest. -/
local macro "slot_var" r:ident s:ident : tactic =>
  `(tactic| (obtain ⟨$r:ident, _, equal, next⟩ := Shape.slotsMatch_var_iff.mp $s
             clear $s
             subst equal
             have $s:ident := next
             clear next))
/-- Reads an ignored slot off a slot match `s`: the reference `r`, and `s` for the rest. -/
local macro "slot_any" r:ident s:ident : tactic =>
  `(tactic| (obtain ⟨$r:ident, _, equal, next⟩ := Shape.slotsMatch_any_iff.mp $s
             clear $s
             subst equal
             have $s:ident := next
             clear next))
/-- Reads a fixed slot off a slot match `s`, substituting its reference; `s` for the rest. -/
local macro "slot_fixed" s:ident : tactic =>
  `(tactic| (obtain ⟨_, equal, next⟩ := Shape.slotsMatch_fixed_iff.mp $s
             clear $s
             subst equal
             have $s:ident := next
             clear next))
/-- Ends the slots: `s : slotsMatch [] indices = true` substitutes the empty list. -/
local macro "slots_end" s:ident : tactic => `(tactic| (obtain equal := Shape.slotsMatch_nil_iff.mp $s; subst equal))

/-- The reference at a position whose dimension the shape fixes is a global
object when that relation holds. -/
theorem point_global {env : Environment} {shape : Shape} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {position : Position} {dimension : Nat} {ref : ObjectRef}
    (found : Shape.refAt arguments position = some ref)
    (holds : Relation.holds env shape allowed brand arguments (.pointDimension position dimension) = true) :
    ∃ point, ref = .global point := by
  simp only [Relation.holds, found] at holds
  cases ref with
  | global point => exact ⟨point, rfl⟩
  | «local» _ _ => simp at holds

theorem descriptor_shape {env : Environment} {implementation : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.descriptor implementation) allowed brand arguments result) :
    arguments = [.natural] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  obtain rfl := Shape.operandMatches_natural_iff.mp ma
  rfl

theorem global_shape {env : Environment} {id : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.global id) allowed brand arguments result) : arguments = [] := by
  obtain ⟨h, -, -⟩ := association
  operands_end h
  rfl

theorem origin_shape {env : Environment} {domain : ObjectType} {family base : DeclId} {allowed : List ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.origin domain family base) allowed brand arguments result) :
    ∃ actual ref, arguments = [.object actual ref] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  object_operand actual ref ma
  exact ⟨actual, ref, rfl⟩

theorem identity_shape {env : Environment} {domain : ObjectType} {family : DeclId} {allowed : List ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.identity domain family) allowed brand arguments result) :
    ∃ actual ref, arguments = [.object actual ref] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  object_operand actual ref ma
  exact ⟨actual, ref, rfl⟩

theorem dimension_shape {env : Environment} {domain : ObjectType} {allowed : List ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.dimension domain) allowed brand arguments result) :
    ∃ actual ref, arguments = [.object actual ref] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  object_operand actual ref ma
  exact ⟨actual, ref, rfl⟩

theorem compose_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.compose family) allowed brand arguments result) :
    ∃ middle target source other : ObjectRef, arguments =
      [.indexed ⟨family, [.object middle, .object target]⟩, .indexed ⟨family, [.object source, .object other]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var middle sa
  slot_var target sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var source sb
  slot_var other sb
  slots_end sb
  exact ⟨middle, target, source, other, rfl⟩

theorem apply_shape {env : Environment} {maps points : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.apply maps points) allowed brand arguments result) :
    ∃ source target other test : ObjectRef, arguments =
      [.indexed ⟨maps, [.object source, .object target]⟩, .indexed ⟨points, [.object other, .object test]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var source sa
  slot_var target sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var other sb
  slot_var test sb
  slots_end sb
  exact ⟨source, target, other, test, rfl⟩

theorem relativeConstant_shape {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativeConstant application map) allowed brand arguments result) :
    arguments = [] := by
  obtain ⟨h, -, -⟩ := association
  operands_end h
  rfl

theorem relativeCompose_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativeCompose family) allowed brand arguments result) :
    ∃ middle target base source middle' base' : ObjectRef, arguments =
      [.indexed ⟨family, [.object middle, .object target, .object base]⟩,
        .indexed ⟨family, [.object source, .object middle', .object base']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var middle sa
  slot_var target sa
  slot_var base sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var source sb
  slot_var middle' sb
  slot_var base' sb
  slots_end sb
  exact ⟨middle, target, base, source, middle', base', rfl⟩

theorem relativeView_shape {env : Environment} {family origin to : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativeView family origin to) allowed brand arguments result) :
    ∃ source target : ObjectRef, arguments =
      [.indexed ⟨family, [.object source, .object target, .object (.global origin)]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_var source sa
  slot_var target sa
  slot_fixed sa
  slots_end sa
  exact ⟨source, target, rfl⟩

theorem relativeEqual_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativeEqual family) allowed brand arguments result) :
    ∃ left right : Application, arguments = [.indexed left, .indexed right] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  application_operand left ma
  application_operand right mb
  exact ⟨left, right, rfl⟩

theorem relativeCoefficient_shape {env : Environment} {family source target : DeclId} {coordinate : Nat}
    {monomial : List Nat} {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativeCoefficient family source target coordinate monomial)
      allowed brand arguments result) :
    ∃ base : ObjectRef, arguments =
      [.indexed ⟨family, [.object (.global source), .object (.global target), .object base]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slot_fixed sa
  slot_any base sa
  slots_end sa
  exact ⟨base, rfl⟩

theorem relativePair_shape {env : Environment} {family fiber : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.relativePair family fiber) allowed brand arguments result) :
    ∃ source left base source' right base' : ObjectRef, arguments =
      [.indexed ⟨family, [.object source, .object left, .object base]⟩,
        .indexed ⟨family, [.object source', .object right, .object base']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var source sa
  slot_var left sa
  slot_var base sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var source' sb
  slot_var right sb
  slot_var base' sb
  slots_end sb
  exact ⟨source, left, base, source', right, base', rfl⟩

theorem smoothConstant_shape {env : Environment} {application : Application} {map : AlgebraRuntime.Map}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.smoothConstant application map) allowed brand arguments result) :
    arguments = [] := by
  obtain ⟨h, -, -⟩ := association
  operands_end h
  rfl

theorem smoothCompose_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.smoothCompose family) allowed brand arguments result) :
    ∃ middle target source other : ObjectRef, arguments =
      [.indexed ⟨family, [.object middle, .object target]⟩, .indexed ⟨family, [.object source, .object other]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var middle sa
  slot_var target sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var source sb
  slot_var other sb
  slots_end sb
  exact ⟨middle, target, source, other, rfl⟩

theorem smoothEqual_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.smoothEqual family) allowed brand arguments result) :
    ∃ left right : Application, arguments = [.indexed left, .indexed right] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  application_operand left ma
  application_operand right mb
  exact ⟨left, right, rfl⟩

theorem smoothComposite_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.smoothComposite family) allowed brand arguments result) :
    ∃ application : Application, arguments = [.indexed application] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  application_operand application ma
  exact ⟨application, rfl⟩

theorem fiberVector_shape {env : Environment} {family smooth object : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.fiberVector family smooth object) allowed brand arguments result) :
    ∃ (point : DeclId) (x : ObjectRef) (components : List ValueType),
      arguments = .indexed ⟨smooth, [.object (.global point), .object x]⟩ :: components := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨0, 0⟩ 0) (by simp [PrimitiveBinding.contract, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  indexed_operand ia sa ma
  slot_var ref sa
  slot_fixed sa
  slots_end sa
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨point, _, _, rfl⟩

theorem fiberAt_shape {env : Environment} {family smooth : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.fiberAt family smooth) allowed brand arguments result) :
    ∃ (x : ObjectRef) (point : DeclId) (x' : ObjectRef), arguments =
      [.indexed ⟨family, [.object x]⟩, .indexed ⟨smooth, [.object (.global point), .object x']⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0) (by simp [PrimitiveBinding.contract, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x' sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨x, point, x', rfl⟩

theorem fiberEqual_shape {env : Environment} {family : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.fiberEqual family) allowed brand arguments result) :
    ∃ left right : Application, arguments = [.indexed left, .indexed right] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  application_operand left ma
  application_operand right mb
  exact ⟨left, right, rfl⟩

theorem fiberComponent_shape {env : Environment} {family object : DeclId} {coordinate : Nat} {allowed : List ObjectRef}
    {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.fiberComponent family object coordinate) allowed brand arguments result) :
    arguments = [.indexed ⟨family, [.object (.global object)]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slots_end sa
  rfl

theorem fiberPairing_shape {env : Environment} {cotangent tangent : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.fiberPairing cotangent tangent) allowed brand arguments result) :
    ∃ x x' : ObjectRef, arguments = [.indexed ⟨cotangent, [.object x]⟩, .indexed ⟨tangent, [.object x']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var x' sb
  slots_end sb
  exact ⟨x, x', rfl⟩

theorem cotangentPullback_shape {env : Environment} {smooth cotangent : DeclId} {mode : SmoothRuntime.PullbackMode}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.cotangentPullback smooth cotangent mode) allowed brand arguments result) :
    ∃ (x y : ObjectRef) (point : DeclId) (x' y' : ObjectRef), arguments =
      [.indexed ⟨smooth, [.object x, .object y]⟩, .indexed ⟨smooth, [.object (.global point), .object x']⟩,
        .indexed ⟨cotangent, [.object y']⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0) (by simp [PrimitiveBinding.contract, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operand_cons c mc h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slot_var y sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x' sb
  slots_end sb
  indexed_operand ic sc mc
  slot_var y' sc
  slots_end sc
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨x, y, point, x', y', rfl⟩

theorem differential_shape {env : Environment} {smooth cotangent line : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.differential smooth cotangent line) allowed brand arguments result) :
    ∃ (x : ObjectRef) (point : DeclId) (x' : ObjectRef), arguments =
      [.indexed ⟨smooth, [.object x, .object (.global line)]⟩, .indexed ⟨smooth, [.object (.global point), .object x']⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0) (by simp [PrimitiveBinding.contract, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x' sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨x, point, x', rfl⟩

theorem linearize_shape {env : Environment} {smooth tape : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.linearize smooth tape) allowed brand arguments result) :
    ∃ (x y : ObjectRef) (point : DeclId) (x' : ObjectRef), arguments =
      [.indexed ⟨smooth, [.object x, .object y]⟩, .indexed ⟨smooth, [.object (.global point), .object x']⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0) (by simp [PrimitiveBinding.contract, PrimitiveDescriptor.ofBool])
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slot_var y sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x' sb
  slots_end sb
  obtain ⟨point, rfl⟩ := point_global (by rfl) atOrigin
  exact ⟨x, y, point, x', rfl⟩

theorem cotangentBackward_shape {env : Environment} {tape cotangent : DeclId} {allowed : List ObjectRef} {brand : Nat}
    {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.cotangentBackward tape cotangent) allowed brand arguments result) :
    ∃ x y y' : ObjectRef, arguments = [.indexed ⟨tape, [.object x, .object y]⟩, .indexed ⟨cotangent, [.object y']⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operand_cons b mb h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slot_var y sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var y' sb
  slots_end sb
  exact ⟨x, y, y', rfl⟩

theorem metricFlat_shape {env : Environment} {metric object tangent cotangent : DeclId} {gram : SmoothRuntime.Matrix}
    {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : PrimitiveAssociation env (.metricFlat metric object gram tangent cotangent) allowed brand arguments result) :
    arguments = [.indexed ⟨tangent, [.object (.global object)]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slots_end sa
  rfl

theorem metricSharp_shape {env : Environment} {metric evidence object cotangent tangent : DeclId}
    {gram inverse : SmoothRuntime.Matrix} {allowed : List ObjectRef} {brand : Nat} {arguments : List ValueType}
    {result : ValueType}
    (association : PrimitiveAssociation env (.metricSharp metric evidence object gram inverse cotangent tangent)
      allowed brand arguments result) :
    arguments = [.indexed ⟨cotangent, [.object (.global object)]⟩] := by
  obtain ⟨h, -, -⟩ := association
  operand_cons a ma h
  operands_end h
  indexed_operand ia sa ma
  slot_fixed sa
  slots_end sa
  rfl

/-! ## Allocation -/

/-- `descriptor` is the one binding whose registry entry allocates. -/
theorem allocates_iff {binding : PrimitiveBinding} :
    binding.allocates = true ↔ ∃ implementation, binding = .descriptor implementation := by
  cases binding <;> simp [PrimitiveBinding.allocates, PrimitiveBinding.contract, PrimitiveDescriptor.ofBool,
    PrimitiveDescriptor.evidence, Shape.allocates, Shape.uncallable]

end VastitasOracle.IndexedAssociations
