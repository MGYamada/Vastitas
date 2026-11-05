# Add an indexed primitive

An [indexed primitive](../appendix/glossary.md#primitive) binds a declared
name to one contract of a closed registry. This page lists what a contributor
touches to add one contract, file by file, and the checks to run.
[Declaration-driven indexed source](../indexed-source.md#closed-primitive-binding-inventory)
describes the registry's place in the checker, and
[Verification boundaries](../verification.md) the theorems it is held to.

## Terms

- A **binding** is a constructor of `PrimitiveBinding` with its data: family,
  base and object IDs and the embedded maps, matrices or coordinates. It is
  the Core-level identity of a primitive call. Displayed names and
  arbitrary certificate strings are not part of it.
- A [**registry entry**](../appendix/glossary.md#registry-entry) is the
  `PrimitiveDescriptor` value that `PrimitiveBinding.contract` returns for a
  binding. It holds the binding's shape, its validity contract as a `Prop`
  and as a `Bool` with the proof that the two agree, its two evaluators, its
  lowering and its shared literals.
- A **shape** is the operand association of a binding as data: the operands,
  an optional variadic tail of integers, the relations between operand
  indices, and the result template.
- The **association** of a shape holds for an operand list and a result when
  the operands match the shape, every relation holds and the result is the
  instantiated template.
- The [**role table**](../appendix/glossary.md#role-table) of a call lists
  the requirements that its shape places on the operand types, in a fixed
  order: the operands' families, their fixed indices, then the relations. The
  diagnostic of a rejected call names the first requirement that fails.
- The **logical evaluator** of an entry computes the value of a call on the
  values of the Core semantics. The **erased evaluator** computes the same
  call on the runtime structures that generated programs link.
  [**Erasure**](../appendix/glossary.md#erasure) maps a logical value to its
  runtime structure.
- The **totality lemma** of a binding proves that an accepted call on typed
  operand values evaluates to a value of the checked result type.
- The [**lowering**](../appendix/glossary.md#lowering) of a call is the Lean
  text that code generation writes for it, from the texts of its operands.
- A [**shared literal**](../appendix/glossary.md#shared-literal) is a basis
  that a generated module declares once, as `basis_k`, and that the lowering
  of every map over that basis names.
- The [**wire form**](../appendix/glossary.md#wire-form) of a binding is the
  record that the frontend sends for an `indexed primitive` declaration: an
  `op` and its named fields.
- A [**primitive family**](../appendix/glossary.md#primitive-family) is the
  entry of one wire `op` in the family table. It is not a
  [family](../appendix/glossary.md#family) declaration.

## One entry, derived tables

Every table that reads a binding reads it through its registry entry. The
tables below take no case per constructor. Module paths are relative to
`lean-kernel/VastitasKernel/`.

| Derived table | Module | Reads from the entry |
| --- | --- | --- |
| `PrimitiveBinding.Valid`, `validPrimitiveBinding` | `IndexedPrimitives.lean` | `validProp`, `validBool` |
| `validPrimitiveBinding_iff` and the `Decidable` instance of `PrimitiveBinding.Valid` | `IndexedContractAudit.lean` | `valid_iff` |
| `PrimitiveAssociation` and its `Decidable` instance | `IndexedPrimitives.lean` | `shape`, through `Shape.Association` |
| `inferPrimitiveResult` | `IndexedPrimitives.lean` | `shape`, through `Shape.infer` |
| `PrimitiveBinding.arity` | `IndexedPrimitives.lean` | `shape`, through `Shape.arity` |
| `PrimitiveBinding.allocates` | `IndexedPrimitives.lean` | `shape`, through `Shape.allocates` |
| `PrimitiveBinding.argumentHint` | `IndexedCore.lean` | `shape`, through `Shape.argumentHint` |
| `roleTable`, with `roleTable_sound` | `IndexedSourceDiagnostics.lean` | `shape`, through `Shape.roles` and its soundness lemma `Shape.roles_sound` |
| `evalPrimitive`, `evalRuntimePrimitive` | `IndexedSemantics.lean` | `eval`, `evalRuntime` |
| `PrimitiveFresh` | `IndexedSemantics.lean` | `shape`, through `PrimitiveBinding.allocates` |
| `allocatedSerials` and the fresh brand of `emitPrimitive` | `IndexedTypeAudit.lean`, `IndexedSourceBodies.lean` | `shape`, through `PrimitiveBinding.allocates` |
| `Codegen.renderPrimitive` | `IndexedCodegen.lean` | `render` |
| `Codegen.renderContext` and the `basis_k` declarations of a generated module | `IndexedCodegen.lean` | `literals`, through `PrimitiveDescriptor.sharedLiterals` |

The oracle states the semantic obligations of an entry once, for any
entry. `VastitasOracle.IndexedPrimitiveSoundness.Sound` has the fields
`total` and `erasure`, and `IndexedSemantics.registry_sound` proves it for
every entry by name. `primitive_total_and_typed` and
`primitive_runtime_erasure` are its corollaries and keep their statements.
`Sound` says nothing about the lowering. The pinned generated code of
[step 6](#6-tests) tests it.

## One family, derived wire form

Every table that reads a wire form reads it through the family of its `op`.
`families` in `IndexedPrimitiveFamilies.lean` lists one family per `op`, and
`primitiveFamily?` finds it. No other table of the kernel or of the frontend
lists the operations. The parser arms of
[step 4](#4-surface-syntax-and-elaboration) and the test lists of
[step 6](#6-tests) name every `op`, and a test of step 6 fails when one of
them misses an `op` of the table.

| Derived table | File | Reads from the family |
| --- | --- | --- |
| `primitive`, `familyPrimitive`, `algebraicPrimitive` and the list `algebraicOperations` | `lean-kernel/VastitasKernel/IndexedDeclarationProtocol.lean` | `op`, `fields`, `algebraic`: the decoder admits only the family's fields, decodes each by its kind, and admits an algebraic `op` only in protocol 9 |
| `resolvePrimitive` | `lean-kernel/VastitasKernel/IndexedSourceChecker.lean` | `fields`, `resolveFirst`, `build`: the resolver checks the field names and kinds, resolves the fields in resolution order and builds the binding |
| `FAMILIES` | `src/primitive_table.rs` | `op`, `algebraic`, `fields`, generated from `families` |
| `primitive_family`, `Primitive::new` and `DeclarationBody::is_algebraic` | `src/indexed.rs` | `FAMILIES`: the frontend record admits only the family's fields, in wire order, and serializes them in that order |

`scripts/check_primitive_table.py` builds `IndexedPrimitiveFamilies`, runs
`scripts/primitive_table.lean` and renders `src/primitive_table.rs` from its
output. Without `--write`, the script fails on any difference from the
checked-in file, and CI runs it that way.

In the [status words](../index.md#what-exists-today) of the book, the derived
tables, the lowering and the wire form are Implemented and Tested. The
obligations of every registry entry are Proved by `registry_sound`. Of the
wire form, `familyPrimitive_wireForm` of
[the demonstration](#the-demonstration) is Proved: a form that
`Wire.familyPrimitive` accepts for a family has that family's `op` and
fields, names and kinds, in wire order. No theorem connects the decoder
`Wire.primitive` to the family of its `op`, and no theorem states the
lowering of a registry entry. The pinned generated code, the table check and
the unit tests of [step 6](#6-tests) test the lowering and the rest of the
wire form.

## Procedure

### 1. The constructor

Add the constructor to `PrimitiveBinding` in
[`IndexedPrimitiveBinding.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedPrimitiveBinding.lean).
Its arguments are the IDs and the embedded data that the validity contract,
the evaluators and the lowering read. Put the checks that the contract uses
next to the constructor, as `relativeConstantValid` and `originContract` are.
The smooth, fiber, tape and metric bindings keep theirs in
`IndexedSmoothContracts.lean`, as `fiberPairingValid` and `metricSharpValid`
are.

### 2. The registry entry

Add one arm to `PrimitiveBinding.contract` in
[`IndexedPrimitiveRegistry.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedPrimitiveRegistry.lean).
The arm builds a `PrimitiveDescriptor`, the structure of
`IndexedPrimitiveDescriptors.lean`, from the binding's own data:

| Field | Content |
| --- | --- |
| `shape` | The operands, their agreements and the result template |
| `validProp` | The binding contract as the proofs state it |
| `validBool` | The binding contract as the checker decides it |
| `valid_iff` | For every environment, `validBool env = true ↔ validProp env` |
| `eval` | The logical evaluator, `Environment → List Value → Option Value` |
| `evalRuntime` | The erased evaluator, `List PrimitiveRuntimeValue → Option PrimitiveRuntimeValue` |
| `render` | The lowering, `RenderContext → List String → Except String String` |
| `literals` | The shared literals of the entry; `[]` when omitted |

`PrimitiveDescriptor.ofBool` builds an entry whose contract is one executable
check; its `Prop` is that the check returns `true`.
`PrimitiveDescriptor.evidence` builds the entry of an evidence binding: one
check, the uncallable shape, evaluators that return `none` and a lowering
that rejects every call.

A shape is written in the language of `IndexedPrimitiveShapes.lean`:

| Part | Constructors |
| --- | --- |
| `Operand` | `natural`; `object role expected`; `indexed role family slots`; `application role family` |
| `Slot` | `var field`; `fixed ref field reason`; `any` |
| `Shape.tail` | `none`, or `some count` for a variadic tail of integers whose count depends on the environment |
| `Relation` | `sameRef`; `sameApplication`; `fixedFrom`; `pointDimension`; `refines`; `freshBrand` |
| `ResultTemplate` | `natural`; `boolean`; `integerPair`; `freshObject implementation`; `globalObject id`; `indexed family slots`; `application operand`; `constant application`; `uncallable` |
| `Shape.families` | `shaped`, the default, or `early`: when the role table reports the operands' families |

The role, field and reason strings are the ones that diagnostics print. Name
index fields with the words that the role table reports for the existing
bindings; family declarations name no indices. A point is
`[target, source]`, a morphism, smooth map or tape `[source, target]`, a
relative morphism `[source, target, base]` and a fiber `[object]`. List the
relations in the order that the role table reports them. A result template
`freshObject` makes the binding allocate; `descriptor` is the one such
entry.

The evaluators match the operand values that the shape admits and return
`none` on any other list. The logical one builds the values of
`IndexedPrimitiveValues.lean`; the erased one applies the operations of
`IndexedRuntime`, `AlgebraRuntime` or `SmoothRuntime` that generated programs
link. A primitive over the value kinds that exist, which are natural numbers,
objects, points, morphisms, relative maps, smooth programs, fibers, tapes,
booleans, integers and integer pairs, changes nothing in
`IndexedPrimitiveValues.lean`. A value kind that no runtime structure carries
is a change to `IndexedValue`, `PrimitiveRuntimeValue`, `erasePrimitiveValue`
and the typing `IndexedHasType` of `IndexedSemantics.lean`, outside this
procedure.

An operation that no runtime module has goes into `IndexedRuntime.lean`,
`AlgebraRuntime.lean` or `SmoothRuntime.lean`, the modules whose compiled
objects generated programs link. The totality lemma of
[step 5](#5-the-local-proofs) then needs oracle facts about the operation, as
the smooth lemmas use those of `VastitasOracle.SmoothRuntime` and
`VastitasOracle.SmoothCanonical`. The native check of [step 6](#6-tests)
compiles and runs it.

The lowering matches the operand texts that the shape admits and returns
`Lowering.arityMismatch` on any other list. A variadic entry renders any
number of operands, and the checked operand count fixes it. The lowering
writes runtime names with `Lowering.runtime`, `Lowering.algebra` and
`Lowering.smooth`, and the checked data of the binding with
`Lowering.renderMap`, `Lowering.renderPolys` and `Lowering.renderMatrix`. It
uses no source spelling. `Lowering.renderMap` names the basis of a map as
`basis_k` when the `RenderContext` lists it, and writes the basis in place
otherwise. The context lists the bases that some entry of the module puts in
`literals`, as `relativeConstant` does.

The entry grants no authority. The all-body audits and the public acceptance
path do not change.

### 3. The primitive family

A binding that an `indexed primitive` declaration names has one family in
`families` of
[`IndexedPrimitiveFamilies.lean`](https://github.com/MGYamada/Vastitas/blob/main/lean-kernel/VastitasKernel/IndexedPrimitiveFamilies.lean).
A `PrimitiveFamily` has these fields:

| Field | Content |
| --- | --- |
| `op` | The name of the operation, on the wire and in source |
| `algebraic` | `true` when only protocol 9 admits the operation |
| `fields` | The fields in wire order, each a `WireField` with a name and a kind: `path`, `objectType`, `coordinate`, `polynomial` or `pullbackMode` |
| `resolveFirst` | The fields that the resolver resolves before the others, in this order; `[]` when omitted |
| `build` | The binding from the resolved arguments, in wire order |

The resolution order is observable. The resolver reports the first name that
does not resolve, and the recorded references keep the order. `flat` and
`sharp` resolve the metric and its evidence first.

`build` puts a placeholder where the kernel computes data after resolution.
`relative_coefficient` starts with coordinate `0` and the empty monomial,
`fiber_component` with coordinate `0`, and `flat` and `sharp` with the
metric's own ID as the object and empty matrices.
A stage pass of [step 4](#4-surface-syntax-and-elaboration) fills the
placeholder. The pass reads the field back from the wire form through an
accessor of `IndexedPrimitiveFamilies.lean`, such as
`relativeCoefficientArguments?` or `fiberComponentCoordinate?`. The accessor
and the family entry use the same names from `WireName`, so a pass reads only
fields that the decoder admits.

A binding that the checker derives from another declaration has no family.
`relativeConstant` and `smoothConstant` come from a morphism declaration, and
the evidence bindings `relativeIso` and `relativeCartesian` from an
isomorphism or a Cartesian square. `resolveBody` in
`IndexedSourceChecker.lean` builds `relativeConstant`, `relativeIso` and
`relativeCartesian`, and `elaborateSmooth` turns the `relativeConstant` of a
smooth family into `smoothConstant`.

Regenerate the table of the frontend and review its diff:

```sh
python3 scripts/check_primitive_table.py --write
```

A field kind other than the five changes `Source.WireKind`,
`Source.WireArgument`, the decoder's `wireArgument`, `ResolvedArgument` and
`resolveArgument`. It also changes the Rust `WireKind` and `WireValue` and
the kinds of `check_primitive_table.py`. Such a change is outside this
procedure.

### 4. Surface syntax and elaboration

Every family has a surface form. Add its arm to `indexed_primitive` in
`src/frontend/indexed_parser.rs`. The arm parses the operands into named wire
values, and `Primitive::new` admits them only when they are the family's
fields, in its order and with its kinds. The parser rejects an `op` that the
table does not have before it reads an argument.

A binding needs a case in a stage pass only when it carries data that the
kernel computes after resolution, or when its declaration has its own
diagnostic. The passes are `elaborateRelative` in `IndexedAlgebraSource.lean`,
`elaborateSmooth` in `IndexedSmoothSource.lean` and `elaborateMetrics` in
`IndexedMetricSource.lean`. Every other binding passes through them
unchanged.

### 5. The local proofs

The proofs live in `lean/VastitasOracle/`. Each is stated on the binding and
its well-shaped operand list, so that a proof about one binding never
unfolds another's entry. For a binding `name`:

1. The **association lemma** `name_association` in `IndexedAssociations.lean`
   states the conjunction that the shape amounts to. Its order is the one the
   shape checks: the operands' families and fixed indices, then the
   relations, then the result. The local tactic `association_simp` proves it.
2. The **shape lemma** `name_shape` in the same module states that any
   accepted call has the listed operand list. The local tactics
   `operand_cons`, `operands_end`, `indexed_operand`, `application_operand`,
   `object_operand`, `slot_var`, `slot_any`, `slot_fixed` and `slots_end`
   read the operands off the association one by one. A binding without
   listed operands, whose operands are all in its integer tail, needs no
   shape lemma.
3. The **totality lemma** `name_total` concludes `PrimitiveOutcome` from
   `PrimitiveTyped` and `PrimitiveValuesHaveTypes` on the well-shaped
   operands. The Stage 1 and Stage 2 lemmas are in `IndexedSemantics.lean`.
   The Stage 3 lemmas conclude `SmoothOutcome` in `SmoothPrimitives.lean`,
   `SmoothFibers.lean` and `SmoothMetricForms.lean`. The value lemmas
   `primitive_single`, `primitive_pair`, `values_pair`, `values_triple`,
   `smooth_value`, `fiber_value`, `point_value` and `map_and_point` read the
   operand values, and `relative_typed` and `fiber_typed` type the results.
4. An **erasure lemma** `name_erasure` when the evaluators do not match one
   operand pattern, as `fiberVector_erasure`, `smoothPoint_erasure` and
   `intPoint_erasure` do for the variadic bindings. For one pattern the
   scoped tactic `erase_matched` of `IndexedPrimitiveSoundness.lean` proves
   erasure by computation.
5. The **soundness instance** `name_sound`, of type
   `Sound (PrimitiveBinding.name …).contract`, next to the totality lemma.
   `Sound.ofPure rfl` takes the totality and erasure proofs of a binding that
   does not allocate. `Sound.ofBinding` takes the world-updating form, as
   `descriptor_sound` does.
6. The **named case** in `registry_sound` in `IndexedSemantics.lean`,
   `| .name arguments => name_sound arguments`. The corollaries
   `primitive_total_and_typed` and `primitive_runtime_erasure` do not change.

Four proofs case on every binding and close the other arms by automation:
`allocates_iff` in `IndexedAssociations.lean`, `affine_result` in
`GeometryResults.lean`, and `validPrimitiveBinding_of_extension` and
`evalPrimitive_of_extension` in `SmoothMetricWeakening.lean`.
`validPrimitiveBinding_of_extension` closes a contract that reads the
environment through the lookup views in its `simp` set.
`evalPrimitive_of_extension` closes an evaluator that reads the environment
only through `globalObject` or `fiberVectorValue`. A binding that reads a metric
declaration is excluded from `MetricFree` in `SmoothMetricWeakening.lean`, as
`metricFlat` and `metricSharp` are. A binding that allocates changes the
statement of `allocates_iff`.

### 6. Tests

- A kernel regression. `IndexedPrimitiveRegression.lean` calls
  `inferPrimitive` and `checkPrimitive` on a binding directly.
  `SmoothObjectRegression.lean`, `CotangentRegression.lean` and
  `MetricFormRegression.lean` run a binding through the source checker, the
  protocol decoder, the Core semantics and lowering. They also check that
  protocol 9 decodes its wire form and that protocols 7 and 8 reject it. List
  the module in `scripts/check_kernel_regressions.sh`.
- The pinned generated code. `tests/emit_golden.rs` lists every wire
  operation in `WIRE_OPERATIONS` with the text that its lowering writes. It
  asserts that the list names each family of the table once, that the
  fixture packages declare each operation, and that the generated Lean
  contains the lowering text of each operation except `relative_view`. Add
  the primitive to the list and to a package that `CASES` in the same file
  lists, or add a package to `CASES` with its fixture under
  `tests/fixtures/emit/`. Regenerate the fixtures as
  [Pinned generated code](validation.md#pinned-generated-code) describes.
- The table tests of the frontend. `every_table_entry_parses_to_its_wire_fields`
  in `src/frontend/indexed_parser.rs` parses one snippet of `SNIPPETS` per
  family, in table order, and checks its fields and its serialization. Add
  the snippet. `the_table_keeps_the_former_allow_list` in `src/indexed.rs`
  names every operation that only protocol 9 admits and every other one. Add
  the `op` to its list.
- The native check. `scripts/check_indexed_native.sh` generates the Lean
  program of each fixture module that `scripts/check_indexed_codegen.lean`
  lists, compiles it with the runtime objects, runs it and compares its
  output with the fixture list of the script. A call of the primitive in a
  fixture module of a kernel regression, such as `smoothFixture` of
  `SmoothObjectRegression.lean`, runs there. A fixture module of another
  regression joins the imports and the fixture list of
  `check_indexed_codegen.lean`, the fixture list of the script with its
  expected output, and the `lake build` list of the script.
- The other Rust tests. The unit test `every_smooth_form_is_algebraic` in
  `src/indexed.rs` covers the protocol-9 gate of the smooth forms,
  `tests/smooth_differential.rs` the source diagnostics and
  `tests/stdlib_differential.rs` the wire records.
  `public_decoders_reject_unknown_fields_in_every_captured_v7_to_v9_record_shape`
  in `tests/protocol_shape.rs` adds an unknown field to one record of each
  record shape in the example packages that it lists. A primitive that one of
  those packages declares has its wire form checked there.

### 7. Documentation

A primitive is documented in four places:

- the Reference section of its construct:
  [smooth map primitives](../language/smooth-declarations.md#smooth-map-primitives),
  [fiber primitives](../language/smooth-declarations.md#fiber-primitives),
  [reverse-pass primitives](../language/smooth-declarations.md#reverse-pass-primitives),
  [flat and sharp](../language/smooth-declarations.md#flat-and-sharp) or
  [morphisms over a base](../affine-geometry.md#morphisms-over-a-base). A
  binding outside those constructs, as `compose` is, has a row in the
  inventory of
  [Declaration-driven indexed source](../indexed-source.md#closed-primitive-binding-inventory)
  instead;
- its wire operation and fields in
  [Wire protocols](../protocol.md#protocol-9-algebraic-affine-forms);
- its row in [Appendix B](../appendix/diagnostics.md#e-smooth-fibers);
- the theorem tables of [Verification boundaries](../verification.md).

## The demonstration

Two modules define one hypothetical primitive as a `PrimitiveDescriptor`
value and its wire form as a `PrimitiveFamily` value, both outside the
registry, so that the registry of the kernel gains no test primitive. The
primitive is a directional derivative: the differential of a function to a
line, paired with a tangent vector at the point. Its evaluators and its
lowering compose `SmoothRuntime.differential` and `SmoothRuntime.pairing`,
which generated programs link, so no runtime code is added.

- `lean-kernel/VastitasKernel/IndexedDescriptorRegression.lean` runs each
  derivation on the entry with `decide` and `#eval` checks. These are the
  validity contract (`validBool` and `valid_iff`), result inference
  (`Shape.infer`), the association decision (`Shape.Association`), the role
  table of a rejected call (`Shape.roles`) with the kernel lemma
  `Shape.roles_sound` at the entry's shape, the argument hints
  (`Shape.argumentHint`), both evaluators on concrete values and their
  erasure, `Shape.allocates` and `Shape.arity`.
- The same module checks the lowering. The text of a call equals the
  lowering of `differential` and then `fiber_pairing` through
  `Codegen.renderPrimitive`, and any other operand count is the arity error.
  The entry adds nothing to `PrimitiveDescriptor.sharedLiterals`. The module
  elaborates the text as a Lean function and runs it.
- The same module decodes the family's wire form through
  `Wire.familyPrimitive`, with the message of each near miss, and resolves
  its fields with `Source.resolveArgument` in
  `PrimitiveFamily.resolutionOrder`. `buildDescriptor` makes the entry from
  the resolved arguments.
- `lean/VastitasOracle/IndexedDescriptorDemo.lean` proves
  `IndexedPrimitiveSoundness.Sound` for the entry from the structure's
  fields, not through `Sound.ofBinding`, and instantiates its two
  obligations and `descriptorWorld_pure` at the entry. It proves the first
  three lowering facts above. It proves for every family that a form
  `Wire.familyPrimitive` accepts has the family's `op` and its field names
  and kinds, in wire order (`familyPrimitive_wireForm`), and
  instantiates that fact at the demonstration's family.

The parts that look an `op` up in `families` reject the demonstration's
`op`, as they reject every `op` that the registry does not hold. These are
`primitiveFamily?`, the decoder's `primitive` and `algebraicPrimitive`, and
`resolvePrimitive`. `directionalDerivative_unregistered` and
`directionalDerivative_rejected` prove it for `primitiveFamily?` and
`Wire.primitive`, and the regression tests `algebraicPrimitive` and
`resolvePrimitive`. `PrimitiveFamily.build` returns a `PrimitiveBinding`,
which has no constructor for the demonstration, so the demonstration's
`build` reports the missing constructor. The generated Rust table and the
parser hold no row for it. A primitive that follows the procedure gets these
parts from its constructor, its family and its parser arm.

The modules show that some parts need nothing beyond a registry entry, a
family value and local proofs about the entry. These parts are the shape
derivations that each derived table reads, the validity contract, the
evaluators and the lowering of the entry, the decoder and resolver steps that
take a family, and the `Sound` obligations. The modules do not show that the
procedure is complete. The registry gains no test primitive, so they
exercise no constructor, no row of `families` or of the generated table and
no parser arm. They add no case to a stage pass or to `registry_sound`, and
they reach none of the four proofs that case on every binding.

Other checks catch a step left out. `PrimitiveBinding.contract` and
`registry_sound` match every constructor without a catch-all arm, so Lean
rejects a constructor that lacks its entry or its case. The tests of
[step 6](#6-tests) fail when a family lacks its parser arm, its snippet, its
place in the allow-list test or its pinned lowering. The stage passes and
`MetricFree` end in a catch-all arm, so Lean accepts a binding that lacks a
case there; steps 4 and 5 name them.

`scripts/check_kernel_regressions.sh` lists the regression, and the oracle
root `lean/VastitasOracle.lean` imports the demonstration, so that the axiom
audit covers it.

```sh
lake -d lean-kernel build VastitasKernel.IndexedDescriptorRegression
lake -d lean build VastitasOracle.IndexedDescriptorDemo
```

## Checks

```sh
lake -d lean-kernel build VastitasKernel VastitasPromotion VastitasPublicTest VastitasStorageTest VastitasAlgebraTest \
  vastitas-kernel storage-native-fixture numerical-native-fixture
bash scripts/check_kernel_regressions.sh
bash scripts/check_indexed_native.sh
python3 scripts/check_primitive_table.py
lake -d lean build VastitasOracle
(cd lean && lake env lean -DwarningAsError=true ../scripts/audit_axioms.lean)
cargo test --locked --all-targets
mdbook build && python3 scripts/check_book.py
```

[Run compiler, proof and native checks](validation.md) gives the full list
and the memory budget of the heavy checks. `scripts/capture_emit.py --compare`
applies to a change that promises identical generated code; a primitive that
adds lowering changes the pinned fixtures instead.
