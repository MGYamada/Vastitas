# Finite geometry migration acceptance

This is the acceptance map for #49 and #58–63. It covers the existing ordinary
and smooth affine descriptor language. It does not complete historical Stage 1:
storage ownership, numerical linear algebra, finite networks and measured
Fast like C remain in the [Stage 1 ledger](stage1-completion.md).

The implementation is declaration driven in all public protocols. Protocol 7
loads `stdlib/src/geometry/{scheme,smooth}/mod.vast` through the single `stdlib`
entrypoint. Protocols 2–6 and explicit `--lib` retain their syntax and wire
formats; `Indexed.LegacySource` adapts their decoded source to the same
`Indexed.AuthoritySource.checkProgram`. The old checked-Core translator is not
a public acceptance path. The temporary `stdlib/indexed` facade is removed.

## Scope of completion

The migration preserves the supported source workflows, nominal rejection rules,
finite primitive results and typed terminating evaluation of the actual returned
Core. Source compatibility is tested through `check`, `build` and generated
executables. The primitive result equations are proved against the retained
runtime definitions. Full surface operational equivalence and native toolchain
equivalence are not proved; #62 explicitly excludes those claims from this gate.
Earlier progress notes saying “legacy semantics/native refinement pending” must
not be read as either a proof of those stronger results or a requirement to prove
an entire native compiler before completing this finite migration.

The old `Declaration.TypeAnnotation`, `Elaboration` and `SourceModuleSafety`
theorems describe the retained legacy Core APIs. Public declarations instead use
`IndexedSource`, `IndexedSourceTypes`, the common function/dispatch/authority
compiler and their input-indexed certificates. The new proofs import those actual
definitions and retain the exact resolution/lowering and returned-Core equations.
No accepted old geometric body is used as evidence for a new body.

## Special-case inventory and disposition

Paths in this table are relative to the repository. Kernel paths abbreviate
`lean-kernel/VastitasKernel/`; oracle paths abbreviate `lean/VastitasOracle/`.
“Adapter” means syntax compatibility followed by common independent checking,
not an alternative semantic acceptance rule.

| Concern / location | Current disposition and independent boundary |
| --- | --- |
| Legacy keywords, reserved names, ring positions and type syntax: `src/frontend.rs`, `src/ir.rs`, kernel `Surface.lean` | Adapter: retains Scheme/CInfScheme/Point/Morphism/Pointed syntax and QQ/CInfReal marker syntax. A marker is not a runtime object. Qualified indexed syntax is parsed separately. Rust diagnostics cannot certify types. |
| Indexed parsing and strict wire schema: `src/indexed.rs`, `src/packages.rs`, kernel `IndexedProtocol.lean`, `IndexedBodyProtocol.lean`, `IndexedAcceptance.lean` | General mechanism: unresolved paths, enclosing owners, family kinds/arity, explicit bindings and complete source bodies; no frontend-supplied authority or checked flag. Older versions reject new declarations/exports instead of discarding them. |
| Old wire conversion: kernel `LegacySource.lean` | Adapter: preserves original bodies, namespaces and edit metadata. Validates the original namespace before adding an ordinary closed unresolved profile; rejects collision with its reserved package identity. That profile passes the same declaration and role checks as a source library. |
| Namespace reservations and lookup: kernel `NamespaceChecker.lean`, `IndexedSourceChecker.lean` | General mechanism with compatibility reservations: canonical package/module/declaration IDs, actual visibility/re-exports and shared-name collision checks. Indexed declarations may use geometry spellings; an ordinary function alias cannot acquire those reserved declaration roles. |
| Classification and representation: kernel `Indexed.lean`, `IndexedAudit.lean`; stdlib `geometry/{scheme,smooth}/mod.vast` | Library plus general mechanism: distinct finite classifications, coefficient markers and implementations. Classification membership does not identify individual objects or add origin/dimension capability. |
| Point/Morphism/Pointed definitions: stdlib `geometry/mod.vast`; kernel `IndexedPackages.lean`, `IndexedContractAudit.lean` | Library plus general mechanism: declared indexed families, same-base constraints, sealed representations, finite single-witness package cases and ordered field templates. General test objects are permitted; Pointed specifically uses the declared base object. |
| Type annotations and legacy type names: kernel `IndexedSourceTypes.lean` | Adapter maps legacy syntax using a selected validated profile; general annotation checking validates declared kinds, sorts, arities, refinement and scope. Object-valued indices and coefficient markers remain distinct. |
| Profile selection: kernel `IndexedGeometryProfile.lean`, `IndexedSource.lean` | Explicit library contract: resolve role paths; validate both settings, distinct markers, exact family/primitive/package roles and complete domains. Exactly one export is needed for legacy syntax. Qualified new syntax needs no export and supports independent libraries. |
| Calls named Affine/Base/origin/id/dimension/compose/apply: kernel `IndexedSourceBodies.lean`, `IndexedFunctionBodies.lean` | Adapter chooses profile declaration IDs, then invokes the same primitive emitter as qualified calls. Fallback is permitted only for an unresolved legacy name (`E_NAME`); a resolved declaration or visibility error never falls back. Operands execute once, in source order. |
| Capture and global-name handling: kernel `IndexedFunctionScope.lean`, `IndexedFunctionBodies.lean` | General mechanism plus adapter names: traverse type indices and package fields as well as expressions; distinguish global declarations from local bindings. Independent lambdas cannot capture outer bindings. Scalar/Fn signature limits remain unchanged. |
| Object identity, substitution and escape: kernel `IndexedCore.lean`, `IndexedTyping.lean`, `IndexedTypeAudit.lean` | General mechanism: unique allocation serials, fixed globals, dependent substitution, generative ordinary object returns/branch merges/openings, and traversal of every free type index, including tokens. Equal descriptors are not identity evidence. |
| Primitive behavior: kernel `IndexedPrimitives.lean`, `IndexedContractAudit.lean`, `IndexedSemantics.lean`, `IndexedRuntime.lean` | Closed explicit registry; see the table below. No arbitrary native registration, certificate string or mathematical axiom is admitted. |
| Diagnostic names/locations: kernel `IndexedSourceDiagnostics.lean`, `IndexedSourceBodies.lean` | Presentation only. “Affine” introduction notes do not choose implementation, merge identities or authorize an operation. |
| Native lowering: kernel `IndexedCodegen.lean` | General Core lowering selected by validated binding/representation tags, not source spelling. Rechecks all declarations, types, scopes, freshness and actual dependencies before emitting reachable functions. Generated modules import only `IndexedRuntime`. Mutable storage is not yet represented. |
| Retained legacy `Checker`, `Declaration`, `Elaboration`, `FunctionChecker`, `FunctionScope`, `Core`, `Semantics`, `Runtime`, `LegacyIndexed` and old codegen | Internal API/regression/proof boundary. Old decoders and scalar/namespace header validation remain reusable; old geometric body acceptance is not called by public `check`/`build`. Their theorems do not substitute for proofs about public indexed Core. |

The adapter remains intentionally supported. Removal requires an explicit decision
to retire the corresponding old syntax/wire contract, not merely deleting reserved
names. No temporary second public geometry checker remains to remove.

## Primitive and proof inventory

Every binding is independently checked against the actual declaration environment.
Family constructors are sealed. `origin` and `dimension` require capabilities for
the complete input implementation domain; arbitrary future Scheme implementations
need not provide either operation.

| Role | Contract and finite runtime result | Evidence |
| --- | --- | --- |
| Affine descriptor | Nat dimension → fresh local object of the declared implementation; runtime stores dimension | `constructor_is_generative`, `descriptor_total`, `GeometryResults.affine_result` |
| Canonical base | No operands → the exact declared global; zero-dimensional runtime descriptor | `global_total`, `global_object_descriptor`, `GeometryResults.base_result` |
| Origin | X → Point<X, declared base>; whole-domain origin support and matching marker | `origin_requires_entire_domain`, `origin_total`, `GeometryResults.origin_result` |
| Identity | X → Morphism<X,X> in the bound family | `identity_total`, `GeometryResults.identity_result` |
| Dimension | Object in an explicitly supported finite domain → Nat dimension | `dimension_requires_entire_domain`, `dimension_total`, `GeometryResults.dimension_result` |
| Compose | (Y→Z, X→Y) → X→Z; exact middle nominal reference | `compose_endpoints`, `compose_middle_agrees`, `GeometryResults.compose_result` |
| Apply | (X→Y, Point<X,S>) → Point<Y,S>; S retained exactly | `apply_preserves_test_object`, `apply_total`, `GeometryResults.apply_result` |

The first names come from `IndexedPrimitives`/`IndexedSemantics` in the oracle.
`GeometryResults` uses the profile's actual declaration lookup and the existing
registry evaluator. `declared_primitive_erasure` connects logical evaluation to
these runtime equations. `GeometryCompatibility.checked_profile` and
`LegacySource.checked_profile` supply the validated profile for public inputs;
`wire_dimension_result` gives a direct public-checker instance.

The equations erase implementation/marker tags just as the runtime does. They
do not authorize mixing bases or identify two static objects; those obligations
are established before erasure. Worlds remain non-injective. The auxiliary
rational zero/identity coordinate interpretation is not a formalization of
arbitrary schemes, all points/maps, or smooth geometry.

## Acceptance-to-evidence map

| Issue / obligation | Implementation, proof and regression evidence |
| --- | --- |
| #58 declarations, kinds, finite domains, versioned unresolved IR | `docs/indexed-declarations.md`, `docs/indexed-source.md`, `IndexedSource` and `IndexedSourceTypes`; `tests/indexed.rs`, `IndexedRegression`, `IndexedSourceRegression`, `IndexedSourceTypeRegression` cover missing/duplicate IDs, sorts/arity, marker metadata, inheritance and order. |
| #58/#63 no privileged library spelling | `tests/stdlib_geometry.rs`: `coherent_renaming_retains_contracts_without_privileged_geometry_names`, `legacy_profile_paths_can_be_coherently_renamed`, `missing_or_ambiguous_profiles_do_not_supply_legacy_meaning`; `tests/indexed.rs::nongeometric_indexed_family_uses_the_same_annotation_checker`. Renaming source, references and profile together preserves native results. |
| #59 nominal identities, substitutions and package association | `IndexedCore`, `IndexedSubstitution`, `IndexedPackageSemantics`, `IndexedWorld`, `IndexedCallTransport`, `IndexedArgumentSafety`; `IndexedCoreRegression` rejects reused brands, forged call substitutions, global rewriting and erased index obligations; package regressions test wrong witnesses and repeated openings. |
| #60 explicit primitives and trust | Registry table above, `IndexedPrimitiveRegression` and actual wire mutations in `tests/stdlib_geometry.rs`; unknown bindings, false roles/capabilities, purported owner/trusted fields and invalid constructors are rejected. No arbitrary evidence registration. |
| #61 existing stdlib workflows and representation freedom | Canonical scheme/smooth module directories, ordinary `pointed` functions, independent abstract annotations, dependent calls/repacking and native 42/2 examples. [Library documentation](../stdlib/src/geometry/README.md#representation-and-future-design) describes future matrix/equation/subspace/opaque Stiefel/Grassmannian representations without mandatory stored charts. |
| #62 exact accepted Core, typing, all-body coverage and terminating evaluation | `IndexedWire`/`LegacySource` expose exact audit/executable Core; `IndexedFunctions`, `IndexedDispatch`, `IndexedAuthority` cover unused/lifted/nonwinning/out-of-domain/applied/unapplied bodies; `IndexedProgramSafety.checked_functions_total_and_typed` and `checked_main_total` discharge call contracts using the actual dependency order. |
| #62 final independent codegen audit | `IndexedCodegen.generate` requires a strong typed/ordered certificate and repeats the audit. `IndexedCoreRegression` rejects forged declarations/endpoints/substitutions/packages/brand reuse before that certificate can be constructed; `TypeAuditRegression` tests rejection of weaker legacy annotation-only certificates at codegen. `scripts/check_indexed_codegen.lean` and both OS native/no-mathlib CI exercise accepted native generation. |
| #63 compatibility and documentation | Public source matrix below; unchanged v2–6/`--lib`, strict old-version rejection, actual protocol-7 wire mutations, direct namespace/profile/Core regressions, full oracle/axiom audit, this inventory and linked current specifications. |

### Public source regression matrix

These named tests are in `tests/stdlib_geometry.rs`, using an actual copied
library package and the normal Rust CLI/Lean backend. Valid fixtures run `check`,
`build` and the executable. The rejection matrix runs both `check` and `build`,
requires the diagnostic category, and verifies that an existing output file is
unchanged. Tests for flat old inputs remain in `tests/compiler.rs`,
`tests/functions.rs` and `tests/usability.rs`.

| Required behavior | Test |
| --- | --- |
| Unchanged pointed (42), smooth (2), declared equivalents | `unchanged_legacy_examples_use_the_declared_stdlib_profile`, `pointed_and_smooth_workflows_migrate_without_erasing_abstract_annotations` |
| Dependent Point<X,S> calls, aliases, same-identity branches, repacking, anonymous outer endpoint scope | `dependent_morphism_calls_retain_the_point_test_object_through_repacking`, `legacy_and_declared_types_share_endpoints_packages_and_primitives`, `legacy_alias_branches_and_anonymous_outer_endpoints_survive_library_lowering` |
| Equal-dimensional different objects in apply/compose; wrong base or coefficient-as-object; Affine(QQ,0) vs Base(QQ) | `legacy_endpoint_base_and_scope_failures_preserve_existing_output` |
| Wrong package witness/base; escaping point/morphism/opened field; two opens; ordinary object-return generativity; distinct-object branch merge | `legacy_endpoint_base_and_scope_failures_preserve_existing_output` |
| Bare opened object survives a block, aliases and repackaging; dependent fields still cannot escape or cross openings/call activations | `opened_objects_survive_blocks_in_both_geometry_modules`, `opened_objects_do_not_export_dependent_fields_or_merge_identities`, `legacy_opened_objects_remain_first_class`; Core `escapedObjectFixture` is checked, evaluated and compiled by the standalone native regression |
| Independent lambdas and unused invalid Fn bodies | `legacy_geometry_inside_independent_lambdas_is_checked` |
| Missing capabilities, module visibility, wrong owner/base and false compatibility roles | `classification_does_not_manufacture_missing_implementation_capabilities`, `kernel_reconstructs_module_visibility_and_geometry_contracts_from_wire`, `raw_compatibility_roles_and_old_wire_downgrades_are_rejected` |

## Verification and remaining boundaries

PR #240 (`f2876ef`) established the common public source checker. PR #250
(`6d1d752`) added total typed evaluation: 26 kernel regression targets,
22 native fixtures, full oracle, 14,719-declaration axiom audit and all eight
hosted checks passed. [PR #255](https://github.com/MGYamada/Vastitas/pull/255) adds the primitive result
equations and strengthens the public compatibility matrix. Its final validation
record covers 252 Rust tests (including 21 geometry tests), formatting/strict
Clippy, the 129-job kernel, 26 regression targets, 22 native fixtures, the 734-job
oracle and the 14,749-declaration axiom audit. The PR records the exact final head,
hosted macOS/Linux checks, review and merge; issue closure follows that merge.

The trust boundary includes Rust parsing/serialization, generated source and the
Lean/C/native toolchain. Tests exercise those boundaries; the formal guarantees
start at decoded input and refer to the actual accepted Core. No theorem here
claims complete source-specialization equivalence, general geometry, mutable
storage safety, floating-point accuracy or C-equivalent performance.

#23/#24's broader identity-result/applicative decisions, #28's provenance
architecture and the unimplemented portions of #48/#52/#64 remain open.
No new dispatch keys, geometric Fn signatures, polymorphic object construction,
charts, gluing, tensors or numerical buffers are introduced by this migration.
