# Dependency invalidation reference

This is executable preparation for [#339](https://github.com/MGYamada/Vastitas/issues/339),
not its production implementation or completion. It defines a small finite source
model, a conservative invalidation planner, untrusted cache candidates and
clean/incremental differential regressions. It changes no Rust or Lean acceptance
path and does not implement the [#152](https://github.com/MGYamada/Vastitas/issues/152)
Lean-native migration.

Run from the repository root, with Python 3.10+ and the standard library only:

```sh
python3 scripts/demo_incremental_reference.py
python3 -m unittest discover -s scripts -p 'test_incremental_reference.py' -v
```

The existing CI discovery command `python3 -m unittest discover -s scripts -p
'test_*.py'` includes the regressions. No new compiler dependency or workflow is
needed. The [implementation](../scripts/incremental_reference.py),
[tests](../scripts/test_incremental_reference.py) and
[demo](../scripts/demo_incremental_reference.py) are independent of compiler APIs.

## Finite semantic model

Inputs are Python dataclass ASTs, not `.vast` source or a new public wire protocol.
The caller constructs the finite, JSON-representable input profile. This is not
a hostile-source parser or a Python object security boundary.

- A package has a **nominal source identity**, separate display name/version,
  manifest revision and explicit package dependencies. All modules in the root
  packages' dependency closure are audited, including unused modules and methods.
  Disconnected packages are outside this build. Package identities are supplied
  fixture identities; the model does not authenticate files or resolve paths.
- Modules have a nominal `(package identity, logical path)` identity, imports,
  a scalar public interface, a literal body, interface uses, families, methods
  and calls. Literal typing distinguishes `Int` from `Bool`; a type mismatch is a
  real rejection of this tiny language, not an input `valid` flag. Interface uses
  check the current target's signature. Imports provide transitive visibility in
  this model; full Vastitas visibility/reexport rules are not implemented here.
- The synthetic dispatch profile has the nominal selectors `Any`, `Linear` and
  `Scalar`, and four feasible keys (`Linear`/`Scalar`, with/without `HasMetric`).
  The nominal/capability **product order**, not equality of observed key sets,
  determines specificity. These are fixtures from the design proposal, not new
  production scalar selectors or metric witnesses.
- A family is identified by its exact declaring module and name. Owner methods
  are active; an assembly explicitly selects external contributions. Every body,
  including losing, unused and unapplied method bodies, is checked. Completion
  checks duplicate signatures and ambiguity over the **whole** finite key space,
  coverage over the declared domain and external methods' final winning footprints
  against grants from the exact owner to the exact contributing module.
- An assembly has explicit applied method identities, grants and a revision.
  The reference models the final authorized family, not the production exclusive
  loan/return/seal trace, reborrowing or permanent authority transfer. A grant alone
  does not apply a contribution. Current source reconstructs identities and grants;
  cache metadata cannot assert an owner or grant.

Package/import cycles, missing dependencies/imports, duplicate identities and
unsupported finite keys/signatures reject with deterministic diagnostics. This
small model rejects cycles rather than claiming support for recursive modules.

`Run.observation` contains build acceptance, sorted normalized diagnostics and
the ordered module structures: exact module identities, interfaces, typed literal
bodies, imports/uses, method bodies, all-key dispatch tables and selected call
targets/results. Rejection observations also retain these structures where the
input graph permits checking. Cache traces, timing and compiler version strings
are not semantic observations. This is a model observation, **not actual checked
Vastitas Core or native behavior**.

## Invalidation and reuse

| Change | Candidate invalidation |
| --- | --- |
| Unchanged current inputs | Try every existing candidate; recheck every one |
| Module literal body, public interface, uses or calls | Changed module and transitive importing consumers |
| Import change | Reverse dependency closure using the union of old and current import edges |
| Family/method addition, removal, signature or body change | Entire selected package/dependency/assembly closure |
| Owner grant, applied contribution or assembly revision | Entire selected closure |
| Compiler version, package identity, manifest or package dependency change | Entire selected closure |
| Module addition, removal or logical identity change | Entire selected closure |
| Missing/malformed cache snapshot | Entire selected closure |
| Missing entry or stale/corrupt/forged candidate, context or receipt | Recompute the affected candidate after current-input checking |

The broad fallback deliberately includes modules with no direct import of a
contributor: a selected assembly can alter a generic used by an unchanged consumer.
It also invalidates unrelated modules **inside** the selected closure when the
model cannot justify narrower reuse. Ordinary body/interface changes can retain
unrelated candidates. Transitive imported results in each context independently
guard against incomplete invalidation plans.

The snapshot is only a planning hint. A cache record contains a candidate, its
context and an `evidence` receipt with context/candidate hashes. The receipt is
explicitly `finite-recheck-required`; it is **not a proof, signature or verified
flag**. Matching source hashes, matching context hashes and recomputed receipt
hashes cannot authorize reuse by themselves.

Every invocation reconstructs the current package graph and entire family
environment. For every module, including warm hits, `_check_unit` rederives its
complete finite semantic result from current source, current family environment
and already rechecked imports, without receiving cache data. Only then may a
candidate whose full typed JSON structure matches that result and its current
context be reused. Otherwise the result is recomputed/replaced safely. Typed JSON
comparison prevents Python's `True == 1` or `False == 0` from accepting a forged
literal or acceptance field. Malformed outer cache data is discarded; no pickle
or other executable deserialization is used.

This intentionally conservative checker shares the finite semantic functions with
the clean reference. It tests cache transparency and invalidation against that
model; it is not an independently proved implementation of Vastitas semantics.
Explicit expected outcomes (targets, ambiguity, grant violations, body errors) and
an independent reachability computation supplement clean/incremental comparison.

`trace.reused` counts **candidate reuse after full rechecking**; `trace.checked`
lists every module rechecked. These counts do not measure skipped checker work or
establish a speedup. The cache is an in-memory, JSON-roundtrippable return value.
Builds do not mutate their supplied prior cache, and new records retain rejection
as rejection. There are no persistent writes or published native outputs here.

## Regression coverage and expected demo

The demo follows cold/warm builds, a new winner, an ambiguous family, its repair
and an unrelated body edit. For `f(Linear, {})` and `f(Any, {HasMetric})`, the
`Linear`+`HasMetric` key has two undominated methods; adding
`f(Linear, {HasMetric})` resolves that ambiguity. The consumer's source does not
change. All six demo steps compare complete observations with a clean build.

Tests also cover winner changes without ambiguity, method removal, selected-body
changes, interface/import rewiring, transitive and unused inputs, external
contributions outside a consumer's imports, grant revocation/narrowing/wrong
issuer/wrong grantee, assembly revisions, module deletion, distinct origins with
equal package names/versions, stale compiler versions and manifest/dependency
changes. Rejected builds can be repaired and reused across edit/revert histories.

Cache mutations include partial entries, malformed snapshots, foreign identities,
false rejection, forged success, altered targets, invalid evidence and **fully
rehashed** forgeries with current context/snapshot metadata. No cache success flag
can conceal a current rejection. There are also all-pairs histories for nine
program variants and all 64 forward-edge DAGs on four labeled modules, each with
four possible edit locations and two body edits (512 graph/edit comparisons).
The graph test independently computes reachability by transitive matrix closure
and asserts the exact invalidated/reused sets.

## Port boundary and remaining work

A Lean port can preserve the separation between immutable nominal inputs, current
environment reconstruction, conservative planning, candidate/receipt data,
current-context validation and observation/trace output. In particular, retain
the all-key family audit and all-body audit when introducing finer queries.

The following are **not implemented or demonstrated** by this reference:

- A persistent Lean-native `.vast` cache or compiler integration; parsing,
  actual scoped declarations/Core, generative endpoints and resource ownership.
- Lean-kernel rechecking of evidence, proof-object replay, or a theorem of cache
  transparency. Hash receipts cannot replace those obligations.
- Source file canonicalization, symlinks/hardlinks, production size limits,
  serialized-source validation, concurrent writers, interrupted/atomic writes,
  locking, cancellation or output collision protection.
- Native cache layers keyed by backend/target/ABI/options, executable parity,
  no-Rust production CI, or cold/warm/local-edit performance evidence.

The current [Stage 1b memoization](stage1b.md) remains within a compilation;
[edit-assembly checking](edit-borrowing.md) retains its existing whole-closure
validation. The [dispatch design](design/functions-dispatch.md) motivates the
finite fixtures without changing production semantics. #339 and #152 remain open
implementation and release obligations.
