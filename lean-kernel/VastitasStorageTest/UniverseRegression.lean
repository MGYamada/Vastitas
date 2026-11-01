import VastitasKernel.UniverseAdmission
import VastitasStorageTest.NumericalFixture

namespace VastitasKernel.UniverseAdmission.Regression
open Indexed.Core Storage

private def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"universe admission: {label}")

-- This is a meaningful Lean term with no executable definition. The literal
-- bridge must reject its name rather than evaluate or trust a computability flag.
noncomputable def chosenNat : Nat := Classical.choice (show Nonempty Nat from ⟨7⟩)

/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'chosenNat', which is 'noncomputable' -/
#guard_msgs in
def forbiddenChoiceValue : Nat := chosenNat

/-- error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.propDecidable', which is 'noncomputable' -/
#guard_msgs in
def forbiddenChoiceDecision (p : Prop) : Bool := @decide p (Classical.propDecidable p)

private def dynamicShape : Shapes.Layout := ⟨.slot 0, .slot 1, .slot 2, false⟩
private def shapeContext : Context := {slots := [(0, .nat), (1, .int), (2, .nat), (3, .nat)]}
private def dimensions (rows columns leading elements : Nat) : Shapes.Valuation :=
  fun name => match name with
  | 0 => rows | 1 => columns | 2 => leading | 3 => elements | _ => 0

#eval show IO Unit from do
  for type in [PureType.nat, .int, .bool, .unit, .pair .nat, .pair .int] do
    let operation := CoreHom.identity type
    let .ok checked := stage operation | throw (IO.userError "concrete scalar Core rejected")
    ensure "static specialization keeps the actual concrete signature"
      (checked.module.functions[0]!.returnType == .pure type)
    ensure "scalar needs explicit representation" (!(admit .leanLP64 {} (.scalar type) none).isOk)
    ensure "scalar representation accepted" ((admit .leanLP64 {} (.scalar type) (some .scalar)).isOk)
  ensure "nat-to-int Core audited" ((stage .natToInt).isOk)
  ensure "Bool decision Core audited" ((stage .booleanNot).isOk)
  ensure "executable integral Decidable Core audited" ((stage .nonnegative).isOk)
  for value in [-3, 0, 8] do
    ensure "actual integral decision agrees with meaning" (decide
      (Semantics.eval CoreHom.nonnegative.module 3
        (Semantics.bindValue (fun _ => none) 0 (.integer value)) CoreHom.nonnegative.term =
        some (.boolean (denote CoreHom.nonnegative value))))
  let actual := (CoreHom.natToInt).module
  ensure "actual Core denotation handles arbitrary precision" (decide
    (Semantics.eval actual 3 (Semantics.bindValue (fun _ => none) 0 (.natural (2^100)))
      CoreHom.natToInt.term = some (.integer (Int.ofNat (2^100)))))
  let wrong := {actual with functions := actual.functions.map fun f => {f with returnType := .pure .bool}}
  ensure "existing Core audit rejects forged specialization" (!(Typing.checkModule wrong).isOk)

  for name in [``Nat, ``Int, ``Bool, ``Unit] do
    ensure "supported Lean scalar type" ((scalarCode? (.const name [])).isSome)
  for expression in [Lean.mkApp (.const ``List [Lean.Level.zero]) (.const ``Nat []),
      .forallE `x (.const ``Nat []) (.const ``Nat []) .default,
      .sort (.succ .zero), .sort (.succ (.succ .zero)),
      .const ``RuntimeTy [], .const ``Classical.choice [Lean.Level.zero],
      .const ``Nat [Lean.Level.zero]] do
    ensure "unsupported Lean type or universe reflection" ((scalarCode? expression).isNone)
  ensure "literal Nat crosses the value boundary"
    ((literalCore? (.lit (.natVal 7))).isSome)
  ensure "executable Bool decision literal crosses"
    ((literalCore? (.const ``Bool.true [])).isSome)
  for expression in [.const ``chosenNat [], .const ``Classical.choice [Lean.Level.zero],
      Lean.mkApp (.const ``Nat.succ []) (.const ``chosenNat []),
      .sort (.succ .zero), .const ``RuntimeTy [], .const ``True.intro []] do
    ensure "no choice, proof, type, or nested escape into runtime literal" ((literalCore? expression).isNone)

  -- A mathematical shape exists independently of its representation certificate.
  let meaning : El (.tensorShape dynamicShape) := ⟨dynamicShape.eval, rfl⟩
  ensure "mathematical meaning does not require physical capacity"
    ((meaning.val (dimensions 2 3 1 0)).rows == 2)
  let .ok admitted := admit .leanLP64 shapeContext (.tensorShape dynamicShape)
      (some (.tensorShape .f64 (.slot 3)))
    | throw (IO.userError "symbolic shape rejected")
  for (rows, columns, leading, elements) in [(2, 3, 4, 10), (0, 3, 1, 0), (2, 0, 2, 0)] do
    let values := dimensions rows columns leading elements
    let .ok realized := realizeShape admitted values | throw (IO.userError "valid guarded shape rejected")
    ensure "exact layout including padding and zero extents" (realized.layout == dynamicShape.eval values)
    let .ok symbolic := Shapes.check shapeContext.slots {} [.allocate 0 .f64 (.slot 3) dynamicShape]
      | throw (IO.userError "existing shape checker rejected")
    let .ok statements := Shapes.instantiate values 4096 {} [.allocate 0 .f64 (.slot 3) dynamicShape]
      | throw (IO.userError "shape instantiation rejected")
    let .ok concrete := Storage.run 4096 {} statements | throw (IO.userError "concrete allocation rejected")
    ensure "actual symbolic/concrete state correspondence" (concrete == symbolic.after.eval values)
  for values in [dimensions 2 3 1 10, dimensions 2 3 4 9,
      dimensions (dimensionLimit + 1) 0 (dimensionLimit + 1) 0,
      dimensions 0 0 1 byteLimit] do
    ensure "symbolic acceptance does not skip runtime guards" (!(realizeShape admitted values).isOk)
  ensure "missing shape representation" (!(admit .leanLP64 shapeContext (.tensorShape dynamicShape) none).isOk)
  ensure "wrong representation kind" (!(admit .leanLP64 shapeContext (.tensorShape dynamicShape) (some .scalar)).isOk)
  for slots in [[], [(0, .bool), (1, .int), (2, .nat), (3, .nat)],
      shapeContext.slots ++ [(0, .nat)]] do
    ensure "absent, nonintegral, or duplicated extent slot"
      (!(admit .leanLP64 {slots} (.tensorShape dynamicShape) (some (.tensorShape .f64 (.slot 3)))).isOk)
  ensure "negative Int extent is not clamped to zero" ((Shapes.narrowInt (-1)).isNone)

  let .ok declarations := Indexed.Source.checkDeclarations NumericalFixture.source
    | throw (IO.userError "actual numerical declarations rejected")
  let env := declarations.resolved.declarations.indexed
  for (scalar, implementation) in [(Scalar.f64, "Real"), (.complexF64, "Complex")] do
    let padded : Storage.Layout := ⟨0, 2, 2, 4, false⟩
    let producer : Functions.Function := ⟨1,
      [.space 0 (NumericalFixture.id implementation) 2, .basis 1 0], [(10, .ownedMap 1 1)], [
      .action (.allocate 2 scalar 6), .action (.borrow 3 (.owner 2) padded .write),
      .action (.fill 3 (NumericalFixture.payload scalar)), .action (.release 3),
      .numerical (.ownedMap 10 2 padded 1 1)], none⟩
    let caller : Functions.Function := ⟨0, [], [], [
      .numerical (.space 0 (NumericalFixture.id implementation) 2), .numerical (.basis 1 0),
      .call 1 [0, 1] [20], .action (.drop 20)], none⟩
    let .ok checked := Functions.check ⟨[caller, producer], 0⟩ env
      | throw (IO.userError "actual owned transfer rejected")
    let some output := checked.context.outputs[0]? | throw (IO.userError "missing owned output")
    let context : Context := ⟨env, output.values, output.resources, []⟩
    let code := RuntimeTy.ownedMap output.view.source output.view.target
    let request := some (Representation.ownedMap output.actual)
    ensure "actual owned map admitted" ((admit .leanLP64 context code request).isOk)
    ensure "owned map without representation rejected" (!(admit .leanLP64 context code none).isOk)
    ensure "mathematical coordinate function alone is not an allocation"
      (!(admit .leanLP64 {context with resources := {}} code request).isOk)
    let changedBasis := {output.view.source with brand := output.view.source.brand + 1000}
    ensure "same dimensions do not identify bases"
      (!(admit .leanLP64 context (.ownedMap changedBasis output.view.target) request).isOk)
    let allocations := context.resources.allocations.map (fun a => {a with initialization := .none})
    let uninitialized := {context with resources := {context.resources with allocations}}
    ensure "uninitialized owned representation rejected" (!(admit .leanLP64 uninitialized code request).isOk)
    let invalidLayout := {context with numerical := context.numerical.map fun (name, value) =>
      (name, match value with
        | .ownedMap view => .ownedMap {view with layout := {view.layout with leading := 1}}
        | other => other)}
    ensure "mathematical map metadata cannot supply a bad physical layout"
      (!(admit .leanLP64 invalidLayout code request).isOk)
    let some transfer := checked.context.transfers[1]? | throw (IO.userError "missing caller move")
    ensure "move preserves allocation, padding and nominal bases"
      (Numerical.value? transfer.values transfer.target ==
        some (.ownedMap {transfer.view with owner := transfer.target}))
    ensure "moved owner cannot be reused" (!(checkAction transfer.after (.move transfer.view.owner 9999)).isOk)
    let .ok loaned := checkAction output.resources (.borrow 9000 (.owner output.view.owner) padded .read)
      | throw (IO.userError "read loan rejected")
    ensure "live loan prevents ownership transfer"
      (!(checkAction loaned (.move output.view.owner 9001)).isOk)

end VastitasKernel.UniverseAdmission.Regression
