import VastitasKernel.IndexedPrimitiveRegistry
import VastitasKernel.IndexedSource

set_option autoImplicit false

/-! The wire forms of the indexed primitives (#622): one family per wire `op`.

A `PrimitiveFamily` says what the indexed declaration decoder (protocols 7
to 9) admits for one op (its exact field names and kinds, in wire order),
whether the op exists only in protocol 9 (today's allow-list), and how the
resolved arguments make a `PrimitiveBinding`. The decoder
(`IndexedDeclarationProtocol.primitive`), the lowering
(`IndexedSourceChecker.resolvePrimitive`) and the generated Rust table
`src/primitive_table.rs` read `families`; no other table lists the ops. After
a change to `families`, regenerate the Rust table with
`python3 scripts/check_primitive_table.py --write`; CI runs the script
without `--write` and fails on any difference. The stage passes read the
arguments they elaborate (a coordinate, a monomial) back from the source form
through `relativeCoefficientArguments?` and `fiberComponentCoordinate?`, which
use the same `WireName` definitions as the family entries.

`build` receives the arguments in wire order and embeds the placeholders that
the stage passes fill: `relative_coefficient` starts with coordinate `0` and
the empty monomial, `flat` and `sharp` with the metric's own ID as the object
and empty matrices. `resolveFirst` names the fields the lowering resolves
before the others, in that order; the lowering resolves the rest in wire
order. The order is observable (the first unresolved name is reported, and
the recorded references keep resolution order), so `flat` and `sharp` keep
the pre-#622 order: the metric and its evidence first.

A family grants no authority: the binding it builds is audited like any
other, and the all-body audits and the public acceptance path are unchanged. -/
namespace VastitasKernel.Indexed

/-- One field of a wire form. -/
structure WireField where
  name : String
  kind : Source.WireKind
  deriving Repr, Inhabited, DecidableEq, BEq

/-- A wire argument after name resolution. -/
inductive ResolvedArgument where
  | declaration (id : DeclId)
  | objectType (type : ObjectType)
  | coordinate (name : String)
  | polynomial (expression : Source.PolyExpr)
  | pullbackMode (mode : SmoothRuntime.PullbackMode)
  deriving Repr, Inhabited

structure PrimitiveFamily where
  /-- The wire `op`. -/
  op : String
  /-- Protocol 9 only. -/
  algebraic : Bool
  /-- The exact fields, in wire order. -/
  fields : List WireField
  /-- Fields resolved before the others, in this order. -/
  resolveFirst : List String := []
  /-- The binding from the resolved arguments, in wire order. -/
  build : List ResolvedArgument → Except String PrimitiveBinding

/-- The arguments do not have the family's kinds. `resolvePrimitive` checks
the field names and kinds before it calls `build`, so no lowering reaches
this; only a direct call of `build` with other arguments does. -/
private def mismatch {α : Type} (op : String) : Except String α :=
  throw s!"the arguments of `{op}` do not match its wire fields"

private def path (name : String) : WireField := ⟨name, .path⟩
private def objectType (name : String) : WireField := ⟨name, .objectType⟩

/-! The op and field names that a stage pass reads back from a source form.
The family entries use these definitions, so a pass reads exactly the fields
that the decoder admits. -/
namespace WireName
/-- `elaborateRelative` reads the coordinate and the monomial of this op. -/
def relativeCoefficient : String := "relative_coefficient"
/-- `elaborateSmooth` reads the coordinate of this op. -/
def fiberComponent : String := "fiber_component"
def coordinate : String := "coordinate"
def monomial : String := "monomial"
end WireName

/-- The families, Stage 1 first and then the protocol-9 operations in the
order of the former allow-list. There is no `gradient` operation: a gradient
is an ordinary function that applies `sharp` to a differential. -/
def families : List PrimitiveFamily := [
  /- Objects, points and morphisms (protocols 7 to 9). -/
  { op := "descriptor", algebraic := false, fields := [path "implementation"],
    build := fun
      | [.declaration implementation] => pure (.descriptor implementation)
      | _ => mismatch "descriptor" },
  { op := "global", algebraic := false, fields := [path "declaration"],
    build := fun
      | [.declaration declaration] => pure (.global declaration)
      | _ => mismatch "global" },
  { op := "origin", algebraic := false,
    fields := [objectType "domain", path "point_family", path "base_object"],
    build := fun
      | [.objectType domain, .declaration family, .declaration base] => pure (.origin domain family base)
      | _ => mismatch "origin" },
  { op := "identity", algebraic := false, fields := [objectType "domain", path "map_family"],
    build := fun
      | [.objectType domain, .declaration family] => pure (.identity domain family)
      | _ => mismatch "identity" },
  { op := "dimension", algebraic := false, fields := [objectType "domain"],
    build := fun
      | [.objectType domain] => pure (.dimension domain)
      | _ => mismatch "dimension" },
  { op := "compose", algebraic := false, fields := [path "map_family"],
    build := fun
      | [.declaration family] => pure (.compose family)
      | _ => mismatch "compose" },
  { op := "apply", algebraic := false, fields := [path "map_family", path "point_family"],
    build := fun
      | [.declaration maps, .declaration points] => pure (.apply maps points)
      | _ => mismatch "apply" },
  /- Relative morphisms over a base (Stage 2, protocol 9). -/
  { op := "relative_compose", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.relativeCompose family)
      | _ => mismatch "relative_compose" },
  { op := "relative_equal", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.relativeEqual family)
      | _ => mismatch "relative_equal" },
  { op := "relative_view", algebraic := true, fields := [path "family", path "source", path "target"],
    build := fun
      | [.declaration family, .declaration source, .declaration target] =>
          pure (.relativeView family source target)
      | _ => mismatch "relative_view" },
  -- The coordinate index and the monomial are elaborated once objects are known.
  { op := WireName.relativeCoefficient, algebraic := true,
    fields := [path "family", path "source", path "target", ⟨WireName.coordinate, .coordinate⟩,
      ⟨WireName.monomial, .polynomial⟩],
    build := fun
      | [.declaration family, .declaration source, .declaration target, .coordinate _, .polynomial _] =>
          pure (.relativeCoefficient family source target 0 [])
      | _ => mismatch WireName.relativeCoefficient },
  { op := "relative_int_point", algebraic := true, fields := [path "family", path "object", path "base"],
    build := fun
      | [.declaration family, .declaration object, .declaration base] =>
          pure (.relativeIntPoint family object base)
      | _ => mismatch "relative_int_point" },
  { op := "relative_pair", algebraic := true, fields := [path "family", path "fiber"],
    build := fun
      | [.declaration family, .declaration fiber] => pure (.relativePair family fiber)
      | _ => mismatch "relative_pair" },
  /- Smooth maps, fibers, tapes and metrics (Stage 3, protocol 9). -/
  { op := "smooth_compose", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.smoothCompose family)
      | _ => mismatch "smooth_compose" },
  { op := "smooth_equal", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.smoothEqual family)
      | _ => mismatch "smooth_equal" },
  { op := "smooth_composite", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.smoothComposite family)
      | _ => mismatch "smooth_composite" },
  { op := "smooth_int_point", algebraic := true, fields := [path "family", path "object", path "point"],
    build := fun
      | [.declaration family, .declaration object, .declaration point] =>
          pure (.smoothIntPoint family object point)
      | _ => mismatch "smooth_int_point" },
  { op := "fiber_vector", algebraic := true, fields := [path "family", path "map_family", path "object"],
    build := fun
      | [.declaration family, .declaration smooth, .declaration object] =>
          pure (.fiberVector family smooth object)
      | _ => mismatch "fiber_vector" },
  { op := "fiber_at", algebraic := true, fields := [path "family", path "map_family"],
    build := fun
      | [.declaration family, .declaration smooth] => pure (.fiberAt family smooth)
      | _ => mismatch "fiber_at" },
  { op := "fiber_equal", algebraic := true, fields := [path "family"],
    build := fun
      | [.declaration family] => pure (.fiberEqual family)
      | _ => mismatch "fiber_equal" },
  -- The coordinate index is elaborated once objects are known.
  { op := WireName.fiberComponent, algebraic := true,
    fields := [path "family", path "object", ⟨WireName.coordinate, .coordinate⟩],
    build := fun
      | [.declaration family, .declaration object, .coordinate _] => pure (.fiberComponent family object 0)
      | _ => mismatch WireName.fiberComponent },
  { op := "fiber_pairing", algebraic := true, fields := [path "cotangent", path "tangent"],
    build := fun
      | [.declaration cotangent, .declaration tangent] => pure (.fiberPairing cotangent tangent)
      | _ => mismatch "fiber_pairing" },
  { op := "cotangent_pullback", algebraic := true,
    fields := [path "map_family", path "cotangent", ⟨"mode", .pullbackMode⟩],
    build := fun
      | [.declaration smooth, .declaration cotangent, .pullbackMode mode] =>
          pure (.cotangentPullback smooth cotangent mode)
      | _ => mismatch "cotangent_pullback" },
  { op := "differential", algebraic := true, fields := [path "map_family", path "cotangent", path "line"],
    build := fun
      | [.declaration smooth, .declaration cotangent, .declaration line] =>
          pure (.differential smooth cotangent line)
      | _ => mismatch "differential" },
  { op := "linearize", algebraic := true, fields := [path "map_family", path "tape"],
    build := fun
      | [.declaration smooth, .declaration tape] => pure (.linearize smooth tape)
      | _ => mismatch "linearize" },
  { op := "cotangent_backward", algebraic := true, fields := [path "tape", path "cotangent"],
    build := fun
      | [.declaration tape, .declaration cotangent] => pure (.cotangentBackward tape cotangent)
      | _ => mismatch "cotangent_backward" },
  -- `flat(tangent, cotangent, using = metric)`: the object and the Gram
  -- matrix are elaborated once the metric is.
  { op := "flat", algebraic := true, fields := [path "tangent", path "cotangent", path "metric"],
    resolveFirst := ["metric"],
    build := fun
      | [.declaration tangent, .declaration cotangent, .declaration metric] =>
          pure (.metricFlat metric metric [] tangent cotangent)
      | _ => mismatch "flat" },
  -- `sharp(cotangent, tangent, using = metric, evidence = evidence)`: the
  -- object and both matrices are elaborated once the evidence is.
  { op := "sharp", algebraic := true,
    fields := [path "cotangent", path "tangent", path "metric", path "evidence"],
    resolveFirst := ["metric", "evidence"],
    build := fun
      | [.declaration cotangent, .declaration tangent, .declaration metric, .declaration evidence] =>
          pure (.metricSharp metric evidence metric [] [] cotangent tangent)
      | _ => mismatch "sharp" } ]

/-- The family of a wire op. -/
def primitiveFamily? (op : String) : Option PrimitiveFamily :=
  families.find? (·.op == op)

/-- The field names of a family, in wire order. -/
def PrimitiveFamily.fieldNames (family : PrimitiveFamily) : List String :=
  family.fields.map (·.name)

/-- The order in which the lowering resolves the fields: `resolveFirst`, then
the rest in wire order. -/
def PrimitiveFamily.resolutionOrder (family : PrimitiveFamily) : List String :=
  family.resolveFirst ++ family.fieldNames.filter (!family.resolveFirst.contains ·)

/-- The coordinate and the monomial of a `relative_coefficient` form, which
`elaborateRelative` elaborates once objects are known. -/
def Source.Primitive.relativeCoefficientArguments? (p : Source.Primitive) :
    Option (String × Source.PolyExpr) := do
  return (← p.coordinate? WireName.relativeCoefficient WireName.coordinate,
    ← p.polynomial? WireName.relativeCoefficient WireName.monomial)

/-- The coordinate of a `fiber_component` form, which `elaborateSmooth`
resolves once objects are known. -/
def Source.Primitive.fiberComponentCoordinate? (p : Source.Primitive) : Option String :=
  p.coordinate? WireName.fiberComponent WireName.coordinate

end VastitasKernel.Indexed
