import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedDescriptorExample
import VastitasOracle.IndexedSemantics
import VastitasOracle.Support

set_option autoImplicit false

/-! Soundness of the primitive outside the registry (#622).

`VastitasKernel.Indexed.DescriptorRegression.directionalDerivative` is a
hypothetical primitive defined as a `PrimitiveDescriptor` value, with no
constructor in `PrimitiveBinding`. The kernel module
`IndexedDescriptorExample` defines it and holds no check; the kernel
regression `IndexedDescriptorRegression` runs the executable checks. Its
`IndexedPrimitiveSoundness.Sound` instance is proved here directly from the
structure's two fields: typed totality from the shape and the validity
contract the descriptor carries, with the value lemmas the registry's own
instances use, and runtime erasure by computation on the matched operand
values. `Sound.ofBinding` and `Sound.ofPure` take a binding, so they do not
apply, and `registry_sound` is untouched. The generic facts then hold for it
as for any registry entry: an accepted call on typed operand values evaluates,
by the descriptor's own evaluator, to a value of the checked result type; the
world is unchanged, because the call does not allocate; and a successful
evaluation erases to the runtime evaluator. The demo's derivative rule is
`none`, so `SmoothJacobian.ReverseSound` holds for it trivially
(`directionalDerivative_reverseSound`). The last section proves what the
demo's lowering and wire form satisfy: the lowering of the two registry calls
it replaces, the checked operand count, no shared literal, and, by a fact
about the decoder proved for every family, a decoded wire form with its
family's fields in wire order; the trusted decoder rejects the demo's op. -/
namespace VastitasOracle.IndexedDescriptorDemo

open VastitasKernel VastitasKernel.Indexed VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Semantics
open VastitasKernel.Indexed.DescriptorRegression (directionalDerivative)
open VastitasOracle.IndexedPrimitiveSoundness
open VastitasOracle.IndexedSemantics (worldExtends_refl)
open VastitasOracle.SmoothPrimitives (smooth_family smooth_value)
open VastitasOracle.SmoothFibers (fiber_family fiber_value values_triple)
open VastitasOracle.Support (bind_success)

/-! ## The local proofs a registry entry has

The shape lemma reads the operand list of an accepted call off the
association, operand by operand, with the kernel's inversion lemmas; the
association lemma says what the association amounts to on that list; the
totality lemma is stated on it. The reading tactics are those of
`IndexedAssociations`, which are local to that module: each clears the match
it inverts before substituting, so the remaining match keeps its name. -/

/-- Reads one operand off a match `h : operandsMatch … (operand :: operands) arguments = true`:
the argument `a`, its match `m`, and `h` for the rest. -/
local macro "operand_cons" a:ident m:ident h:ident : tactic =>
  `(tactic| (obtain ⟨$a:ident, _, equal, $m:ident, next⟩ := Shape.operandsMatch_cons_iff.mp $h
             clear $h
             subst equal
             have $h:ident := next
             clear next))
/-- Ends the operands of a shape without a tail. -/
local macro "operands_end" h:ident : tactic =>
  `(tactic| (obtain equal := Shape.tailMatches_none_iff.mp (Shape.operandsMatch_nil_iff.mp $h); subst equal))
/-- Reads an indexed operand off its match `m`: the indices `i` and their slot match `s`. -/
local macro "indexed_operand" i:ident s:ident m:ident : tactic =>
  `(tactic| (obtain ⟨$i:ident, equal, $s:ident⟩ := Shape.operandMatches_indexed_iff.mp $m; clear $m; subst equal))
/-- Reads a free slot off a slot match `s`: the reference `r`, and `s` for the rest. -/
local macro "slot_var" r:ident s:ident : tactic =>
  `(tactic| (obtain ⟨$r:ident, _, equal, next⟩ := Shape.slotsMatch_var_iff.mp $s
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
/-- Ends the slots. -/
local macro "slots_end" s:ident : tactic => `(tactic| (obtain equal := Shape.slotsMatch_nil_iff.mp $s; subst equal))

theorem directionalDerivative_shape {env : Indexed.Environment} {smooth tangent line : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {result : ValueType}
    (association : Shape.Association env (directionalDerivative smooth tangent line).shape allowed brand
      arguments result) :
    ∃ (x : Indexed.ObjectRef) (point : DeclId) (x' x'' : Indexed.ObjectRef), arguments =
      [.indexed ⟨smooth, [.object x, .object (.global line)]⟩,
        .indexed ⟨smooth, [.object (.global point), .object x']⟩, .indexed ⟨tangent, [.object x'']⟩] := by
  obtain ⟨h, relations, -⟩ := association
  have atOrigin := relations (.pointDimension ⟨1, 0⟩ 0) (by simp [directionalDerivative])
  operand_cons a ma h
  operand_cons b mb h
  operand_cons c mc h
  operands_end h
  indexed_operand ia sa ma
  slot_var x sa
  slot_fixed sa
  slots_end sa
  indexed_operand ib sb mb
  slot_var ref sb
  slot_var x' sb
  slots_end sb
  indexed_operand ic sc mc
  slot_var x'' sc
  slots_end sc
  obtain ⟨point, rfl⟩ := IndexedAssociations.point_global (by rfl) atOrigin
  exact ⟨x, point, x', x'', rfl⟩

theorem directionalDerivative_association {env : Indexed.Environment} {smooth tangent line sf pf tf point : DeclId}
    {x y x' x'' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef} {brand : Nat} {result : ValueType} :
    Shape.Association env (directionalDerivative smooth tangent line).shape allowed brand
      [.indexed ⟨sf, [.object x, .object y]⟩, .indexed ⟨pf, [.object (.global point), .object x']⟩,
        .indexed ⟨tf, [.object x'']⟩] result ↔
      sf = smooth ∧ .global line = y ∧ pf = smooth ∧ tf = tangent ∧ x = x' ∧ x = x'' ∧
        smoothDimension? env point = some 0 ∧ .integerPair = result := by
  simp only [directionalDerivative, Shape.Association, Shape.accepts, Shape.operandsMatch, Shape.operandMatches,
    Shape.slotsMatch, Shape.tailMatches_none_iff, Relation.holds, Shape.refAt, Shape.applicationAt, Shape.objectAt,
    ResultTemplate.instantiate, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, and_true,
    and_assoc]

/-- Typed totality on the operand list of an accepted call: the result is an
integer pair, so its typing is trivial, and the operand values are a smooth
map, a smooth point and a fiber by the registry's value lemmas. -/
theorem directionalDerivative_total {env : Indexed.Environment} {world : World} {smooth tangent line : DeclId}
    {x : Indexed.ObjectRef} {point : DeclId} {x' x'' : Indexed.ObjectRef} {allowed : List Indexed.ObjectRef}
    {brand : Nat} {output : ValueType} {values : List Value}
    (valid : (directionalDerivative smooth tangent line).validProp env)
    (association : Shape.Association env (directionalDerivative smooth tangent line).shape allowed brand
      [.indexed ⟨smooth, [.object x, .object (.global line)]⟩,
        .indexed ⟨smooth, [.object (.global point), .object x']⟩, .indexed ⟨tangent, [.object x'']⟩] output)
    (typed : PrimitiveValuesHaveTypes env world values
      [.indexed ⟨smooth, [.object x, .object (.global line)]⟩,
        .indexed ⟨smooth, [.object (.global point), .object x']⟩, .indexed ⟨tangent, [.object x'']⟩]) :
    ∃ value, (directionalDerivative smooth tangent line).eval env values = some value ∧
      PrimitiveValueHasType env world value output := by
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := directionalDerivative_association.mp association
  have contract : isSmoothFamily env smooth = true ∧ smoothDimension? env line = some 1 ∧
      fiberVariance? env tangent = some .tangent := valid
  obtain ⟨smoothFamily, _, tangentFamily⟩ := contract
  have smoothRepresentation := smooth_family smoothFamily
  have tangentRepresentation := fiber_family tangentFamily
  obtain ⟨_, _, _, rfl, functionTyped, pointTyped, vectorTyped⟩ := values_triple typed
  obtain ⟨function, _, _, _, _, rfl, _⟩ := smooth_value smoothRepresentation functionTyped
  obtain ⟨point, _, _, _, _, rfl, _⟩ := smooth_value smoothRepresentation pointTyped
  obtain ⟨vector, _, _, rfl, _⟩ := fiber_value tangentRepresentation vectorTyped
  exact ⟨.pairInt (SmoothRuntime.pairing (SmoothRuntime.differential function point) vector).1
    (SmoothRuntime.pairing (SmoothRuntime.differential function point) vector).2, rfl, trivial⟩

/-! ## The soundness instance, from the structure's fields -/

theorem directionalDerivative_sound (smooth tangent line : DeclId) :
    Sound (directionalDerivative smooth tangent line) where
  total valid _ _ association typed _ := by
    obtain ⟨x, point, x', x'', rfl⟩ := directionalDerivative_shape association
    obtain ⟨value, evaluated, valueTyped⟩ := directionalDerivative_total valid association typed
    exact ⟨_, value, evaluated, worldExtends_refl _, valueTyped, (descriptorWorld_pure rfl _ _ _).symm⟩
  erasure evaluated := by
    simp only [directionalDerivative] at evaluated
    split at evaluated <;> first | contradiction | (cases evaluated; exact ⟨_, _, rfl, rfl, rfl⟩)

/-- The demo states the derivative rule `none`: compiled reverse Core treats a
call as an opaque call, so the rule promises nothing about the evaluator. -/
theorem directionalDerivative_reverseSound (smooth tangent line : DeclId) :
    SmoothJacobian.ReverseSound (directionalDerivative smooth tangent line) :=
  trivial

/-! ## The generic facts, instantiated -/

/-- An accepted call on typed operand values evaluates, by the descriptor's
own evaluator, to a value of the checked result type, in the unchanged
world: the totality obligation of `Sound` at the demo, with the fresh-slot
premise discharged because the call does not allocate. -/
theorem directionalDerivative_outcome {env : Indexed.Environment} {world : World} {smooth tangent line : DeclId}
    {allowed : List Indexed.ObjectRef} {brand : Nat} {arguments : List ValueType} {output : ValueType}
    {values : List Value}
    (valid : (directionalDerivative smooth tangent line).validProp env)
    (argumentsValid : ∀ argument ∈ arguments, argument.Valid env) (resultValid : output.Valid env)
    (association : Shape.Association env (directionalDerivative smooth tangent line).shape allowed brand
      arguments output)
    (typed : PrimitiveValuesHaveTypes env world values arguments) :
    ∃ value, (directionalDerivative smooth tangent line).eval env values = some value ∧
      PrimitiveValueHasType env world value output := by
  obtain ⟨after, value, evaluated, _, valueTyped, afterWorld⟩ :=
    (directionalDerivative_sound smooth tangent line).total valid argumentsValid resultValid association typed
      (fun allocates => by simp [directionalDerivative, Shape.allocates] at allocates)
  rw [descriptorWorld_pure rfl] at afterWorld
  subst afterWorld
  exact ⟨value, evaluated, valueTyped⟩

/-- The logical world after a call of the demo is the world before it. -/
theorem directionalDerivative_world (smooth tangent line : DeclId) (world : World) (output : ValueType)
    (value : Value) : descriptorWorld (directionalDerivative smooth tangent line) world output value = world :=
  descriptorWorld_pure rfl world output value

/-- A successful logical evaluation of the demo erases to its runtime
evaluator on the erased operands: the erasure obligation of `Sound` at the demo. -/
theorem directionalDerivative_erasure {env : Indexed.Environment} {smooth tangent line : DeclId}
    {values : List Value} {value : Value}
    (evaluated : (directionalDerivative smooth tangent line).eval env values = some value) :
    ∃ inputs output, values.mapM erasePrimitiveValue = some inputs ∧ erasePrimitiveValue value = some output ∧
      (directionalDerivative smooth tangent line).evalRuntime inputs = some output :=
  (directionalDerivative_sound smooth tangent line).erasure evaluated

/-! ## Lowering and wire form

The oracle states no obligation on the lowering or the wire form of a
descriptor: `Sound` is about its evaluators. The lowering of the registry
entries is checked by compiling and running generated programs
(`scripts/check_indexed_native.sh`), and the decoder and the resolver are
executable checks with regressions. What follows from the demo's fields alone
is proved here: its lowering is the lowering of the two registry calls it
replaces; it accepts exactly the checked operand count and otherwise gives
the registry's arity error; the demo adds no literal to those a module
shares. For the wire form, one generic fact about the decoder is proved for
every family and instantiated at the demo's: a wire form that
`Wire.familyPrimitive` accepts has the family's op and the family's fields,
names and kinds, in wire order, so the comparison that
`Source.resolvePrimitive` makes before it resolves a name holds for it. The
trusted decoder `Wire.primitive` looks the op up in `families`, which do not
hold the demo, and rejects every wire form of it. -/

open VastitasKernel.Indexed.DescriptorRegression (directionalDerivativeFamily)

/-- The lowering of a call is the lowering of the two registry calls it
replaces: `differential`, then `fiber_pairing` on its result, whatever the
cotangent family between them. -/
theorem directionalDerivative_render (smooth tangent line cotangent : DeclId) (ctx : RenderContext)
    (function point vector : String) :
    (directionalDerivative smooth tangent line).render ctx [function, point, vector] = (do
      let covector ← Codegen.renderPrimitive ctx (.differential smooth cotangent line) [function, point]
      Codegen.renderPrimitive ctx (.fiberPairing cotangent tangent) [covector, vector]) := rfl

/-- The lowering accepts exactly the checked operand count. -/
theorem directionalDerivative_render_arity (env : Indexed.Environment) (smooth tangent line : DeclId)
    (ctx : RenderContext) (args : List String) :
    (∃ text, (directionalDerivative smooth tangent line).render ctx args = .ok text) ↔
      args.length = Shape.arity env (directionalDerivative smooth tangent line).shape := by
  match args with
  | [_, _, _] => simp [directionalDerivative, Shape.arity]
  | [] | [_] | [_, _] => simp [directionalDerivative, Shape.arity, Lowering.arityMismatch]
  | _ :: _ :: _ :: _ :: _ => simp [directionalDerivative, Shape.arity, Lowering.arityMismatch]

/-- Any other operand list is the registry's arity error. -/
theorem directionalDerivative_render_mismatch (smooth tangent line : DeclId) (ctx : RenderContext)
    (args : List String) (count : args.length ≠ 3) :
    (directionalDerivative smooth tangent line).render ctx args = Lowering.arityMismatch := by
  match args, count with
  | [_, _, _], count => exact absurd rfl count
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => rfl

/-- The demo shares no literal: a module that holds it shares the literals of
its other entries, wherever it stands among them. -/
theorem directionalDerivative_sharedLiterals (smooth tangent line : DeclId)
    (before after : List PrimitiveDescriptor) :
    PrimitiveDescriptor.sharedLiterals (before ++ directionalDerivative smooth tangent line :: after) =
      PrimitiveDescriptor.sharedLiterals (before ++ after) := by
  simp only [PrimitiveDescriptor.sharedLiterals, List.foldl_append, List.foldl_cons]
  rfl

/-- A decoded field has the kind its family declares. -/
theorem wireArgument_kind {j : Lean.Json} {spec : WireField} {argument : Source.WireArgument}
    (decoded : Wire.wireArgument j spec = .ok argument) : argument.kind = spec.kind := by
  obtain ⟨name, kind⟩ := spec
  cases kind <;> simp only [Wire.wireArgument] at decoded <;>
    first
    | (obtain ⟨_, _, decoded⟩ := bind_success decoded
       obtain ⟨_, _, decoded⟩ := bind_success decoded
       cases decoded
       rfl)
    | (obtain ⟨_, _, decoded⟩ := bind_success decoded
       cases decoded
       rfl)

/-- The decoded fields, in order, have the names and the kinds of the specs. -/
private theorem mapM_fields {j : Lean.Json} :
    ∀ {specs : List WireField} {arguments : List (String × Source.WireArgument)},
      specs.mapM (fun spec => do return (spec.name, ← Wire.wireArgument j spec)) = .ok arguments →
      arguments.map (fun (name, argument) => (name, argument.kind)) = specs.map fun field => (field.name, field.kind)
  | [], _, mapped => by cases mapped; rfl
  | spec :: specs, _, mapped => by
      simp only [List.mapM_cons] at mapped
      obtain ⟨_, first, mapped⟩ := bind_success mapped
      obtain ⟨_, rest, mapped⟩ := bind_success mapped
      cases mapped
      obtain ⟨argument, decoded, pair⟩ := bind_success first
      cases pair
      simp only [List.map_cons, wireArgument_kind decoded, mapM_fields rest]

/-- A wire form that the generic decoder accepts for a family has the
family's op and the family's fields, names and kinds, in wire order: the
comparison `Source.resolvePrimitive` makes before it resolves a name. -/
theorem familyPrimitive_wireForm {j : Lean.Json} {family : PrimitiveFamily} {primitive : Source.Primitive}
    (decoded : Wire.familyPrimitive j family = .ok primitive) :
    primitive.op = family.op ∧ primitive.arguments.map (fun (name, argument) => (name, argument.kind)) =
      family.fields.map fun field => (field.name, field.kind) := by
  unfold Wire.familyPrimitive at decoded
  obtain ⟨_, -, decoded⟩ := bind_success decoded
  obtain ⟨_, mapped, decoded⟩ := bind_success decoded
  cases decoded
  exact ⟨rfl, mapM_fields mapped⟩

/-- The generic fact at the demo's family. -/
theorem directionalDerivative_wireForm {j : Lean.Json} {primitive : Source.Primitive}
    (decoded : Wire.familyPrimitive j directionalDerivativeFamily = .ok primitive) :
    primitive.op = "directional_derivative" ∧ primitive.arguments.map (fun (name, argument) => (name, argument.kind)) =
      [("map_family", .path), ("tangent", .path), ("line", .path)] :=
  familyPrimitive_wireForm decoded

/-- The registry's families do not hold the demo's op. -/
theorem directionalDerivative_unregistered : (primitiveFamily? directionalDerivativeFamily.op).isNone = true := by
  decide

/-- The trusted decoder rejects every wire form of the demo, in every protocol. -/
theorem directionalDerivative_rejected {j : Lean.Json} (op : JsonDecode.str j "op" = .ok "directional_derivative")
    (algebraic : Bool) : Wire.primitive j algebraic = .error "unknown indexed primitive contract" := by
  have unregistered : primitiveFamily? "directional_derivative" = none :=
    Option.isNone_iff_eq_none.mp directionalDerivative_unregistered
  have readOp : ∀ {α : Type} (next : String → Except String α),
      (JsonDecode.str j "op" >>= next) = next "directional_derivative" := by
    intro _ next
    rw [op]
    rfl
  simp only [Wire.primitive, readOp, unregistered] <;> rfl

end VastitasOracle.IndexedDescriptorDemo
