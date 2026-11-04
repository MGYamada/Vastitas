# Path packages and logical modules

This is the first increment of [#52](https://github.com/MGYamada/Vastitas/issues/52),
tracked by [#56](https://github.com/MGYamada/Vastitas/issues/56). It adds path
packages, modules, unique function owners and call-only imports to Stage 1b.
The [protocol-5 increment](#edit-borrowing) adds scoped edit borrowing and finite impact regions. [Protocol 6](#edit-authority) adds explicit nested delegation and permanent authority transfer without changing function identity.

## Manifest and commands

A package has one explicit `Vastitas.toml`:

```toml
[package]
name = "demo"
version = "0.1.0"
root = "src/main.vast"

[dependencies]
arithmetic = { path = "../arithmetic" }
```

All package fields are required. Names are nonempty strings, versions use
SemVer, and root names a `.vast` file inside the package directory. Dependency
aliases are ASCII identifiers and cannot collide with declarations or imports.
Each path names a directory containing `Vastitas.toml`; paths are relative to
the declaring manifest. Unsupported manifest fields and dependency forms fail.

```sh
vastitas check --manifest-path examples/packages/demo/Vastitas.toml
vastitas build --manifest-path examples/packages/demo/Vastitas.toml -o target/demo
./target/demo
# 42
```

There is no implicit manifest search. Positional `.vast` plus explicit `--lib`
remains the protocol-2 compatibility mode; it cannot be mixed with manifest
mode. `check` needs no main. `build` requires an ordinary `fn main() -> Int`
declared in the selected package's root module. Importing another package's
main or declaring a main in a child module does not supply that entrypoint.

Only local path dependencies are supported. There is no registry, Git fetch,
version solving, multiple build targets or independent compilation cache.
Every build rereads all inputs and checks all packages, including unused ones.
Cyclic dependencies are rejected. The same canonical manifest reached through
different aliases is one package. Identity includes canonical manifest location,
name and version; equal names and versions at different locations remain distinct.

## Modules and paths

```vast
mod math {
    pub fn increment(x: Int) -> Int { x + 1 }
}
use math::increment as next;
fn main() -> Int { next(41) }
```

Declarations and imports occur at module scope only. `mod math;` loads either
`math.vast` or `math/mod.vast`; having both is an error. Paths are based on the
root source directory plus the **logical** module path. For example, a child
`mod exact;` in logical `math` loads `math/exact.vast` or
`math/exact/mod.vast`, whether `math` is inline, `math.vast`, or `math/mod.vast`.
Source files cannot escape their package directory through `..` or symlinks.
Loading cycles are detected by file identity, including hard links. Independent
uses of the same source file in different logical modules remain different owners.
The loader limits the selected closure to 4,096 logical modules (including inline
modules), and all inputs to 8,192 file loads, 16 MiB per file and 64 MiB in total.
Each reuse consumes the byte budget again; sharing a filesystem identity does not
merge owners or exempt a source from the bound. Nonregular inputs are rejected.

- `package::` begins at the current package root; the bare local name `package`
  remains legal. `self::` starts in the current module; `super::` starts in its
  parent, and repeated `super::` walks further ancestors.
- A direct dependency alias may begin a path. Transitive dependencies are not
  implicitly imported; their package must explicitly expose the desired API.
- Bare names resolve in the current module's declarations/imports and local
  bindings. Parent names require an explicit path. Builtins remain available.
- `use` accepts any named declaration: a module, ordinary or resource function,
  generic, abstract type, indexed declaration, grant, contribution, delegation or
  transfer, optionally followed by `as`. An alias keeps the original identity
  and grants no authority. No wildcard imports are implemented.
  Import/declaration order does not select an owner or change resolution.

Declaration names and local bindings obey the existing reserved-name and
shadowing rules; package mode additionally reserves `mod`, `use`, `pub`,
`self` and `super`. `generic` is also permitted as a contextual module name and
path component (for example `std::arithmetic::generic::promote`); it remains
reserved for functions, variables and import aliases. Import that module using
an explicit alias such as `use std::arithmetic::generic as arithmetic;`.
A binding cannot shadow a dependency alias. Logical module
nesting and dependency nesting are bounded to 64 in the loader; namespace
resolution has a shared 4096-member work budget and rejects exhaustion with
`E_LIMIT`, instead of expanding shared import paths indefinitely.

The kernel reconstructs package, module, import and dependency lookup tables
from the supplied declarations. A module lookup still checks the complete
package identity, including name and version. Active import paths use a
persistent ordered set of complete scope/name keys, preserving cycle checks
without copying or scanning a growing path list. No lookup index is trusted
from wire input. A body-checking pass caches successful unqualified import
aliases under their full package/module scope and spelling. Qualified paths,
dependency aliases and failures use the ordinary resolver. Each cache hit
pays for the same logical member visits as the original lookup.

A request admits at most 1,000,000 member visits across all import declarations.
The kernel also limits the sum of the original wire input price and the namespace
queries in its independent body passes to 4,000,000 units. The wire price counts
syntax nodes, path components and the largest reconstructed import cost for
each matching spelling. It conservatively charges matching strings as well as
references. Diagnostic spans are omitted and import declarations are priced
separately. Public resource programs include both additional pure-fragment
passes. Either aggregate limit produces `E_LIMIT`; the per-path limit and
every import's target, visibility and cycle checks still apply.
The [matched compiler measurements](https://github.com/MGYamada/Vastitas/blob/main/experiments/compiler_scaling/results/2026-11-03-macos-namespace-work-budget/RESULTS.md)
cover single-use chains, repeated references and the aggregate limits.

## Visibility and ownership

Declarations are private by default and accessible from their declaring module
and descendants. Other scopes require `pub` at every traversed path edge.
Qualified calls receive the same checks as imports. `pub use` can reexport an
accessible public declaration, including a public function reached through an
accessible private module. It cannot reexport a private target. `self` and
`super` retain the actual module visibility. Cyclic imports/reexports fail.

A function owner is the resolved package identity, logical module path and
definition name. Aliases, reexports, source filenames and read order do not
create or transfer ownership. Functions with equal short names in different
modules remain separate. Ordinary methods may be added only in the exact module
that defines the generic; protocol-5 contributions require explicit grants and
active assembly loans. Child modules, public visibility, qualified names and
imports grant no edit authority; ordinary functions cannot receive methods.
Calls may be repeated, and aliases of function values retain the same static
function target. Generics remain callable families, not function values.

## Validation and boundary

Manifest mode sends protocol 3, retaining package dependencies, modules,
visibility, imports and unresolved paths. Lean independently validates the
graph and assigns function identities; the frontend supplies no trusted owner
or target IDs. All functions, unused dependencies and all applicable method
bodies pass through the existing surface/dispatch and core audits. Capture
prohibition, exact geometry identities, recursion rejection and specialization
limits still apply. Diagnostics retain the original source file and location.
All manifests and source files participate in output collision protection,
including aliases, and the native build keeps the same cancellation/cleanup path.

The actual-checker proofs cover unique owners, reference-ledger agreement with
the actual resolver, method authority, alias preservation, and
typing/order/termination of the returned core. The reference audit reuses the
lowering resolver. The owner structure omits source-file placement and aliases;
equal owners have equal symbols by congruence. Symbol-encoding injectivity and
correspondence between ledger entries and emitted names are not proved. Actual
symbol uniqueness is checked during namespace validation. Rust file
loading/authenticity, JSON decoding, complete namespace syntax preservation
and native compilation are not proved.
See [verification](verification.md) and [protocol](protocol.md).

The foundation is available to #48 (abstract types/methods), #49 (geometric
stdlib interfaces), and #55 (`promote`), but does not implement their remaining
requirements. #37 (same-concrete-type argument constraints) is an independent
next candidate. #22–26 and #28 retain their existing design decisions. Stage 1
as a whole remains incomplete.


## Finite abstract declarations

[Abstract selectors and contracts](stage1a.md#abstract-types) use protocol 4's explicit
package mode and the same owner/index/reference audit. `pub abstract type`
participates in visibility and aliases. Scalar membership is editable only by
the abstract type's exact defining module; an abstract contract is editable
only by the generic's exact defining module. Public exposure, child modules and
imports grant neither permission. Abstract parents and contract-domain selectors
may refer to visible types in other modules without editing those declarations.
The driver selects the protocol from the declarations present. Any grant,
delegation or transfer selects protocol 9. Otherwise resource functions, or an
indexed implementation other than an affine descriptor, select protocol 8; other
indexed declarations or a `geometry_compat` export select protocol 7; reborrow
or transfer events in an assembly select protocol 6; contributions or an
assembly select protocol 5; abstract declarations select protocol 4; and
package sources with none of these use protocol 3. See
[edit borrowing](#edit-borrowing) and [protocol 9 recipients](protocol.md).
The root may omit its assembly, which selects an empty edit trace without
skipping grant validation or checking of unapplied contributions.

## Explicit edit authority

Ordinary imports remain call-only. The exact generic owner may issue a grant to
one module in the selected dependency closure; that module contributes methods
only through a root assembly with an active exclusive loan. Neither imports,
child modules nor aliases imply this permission. See [the syntax and completion
contract](#edit-borrowing) and `examples/packages/edit-borrow/app/Vastitas.toml`.

## Indexed geometry compatibility exports

A package can explicitly export `[geometry_compat]` with `scheme` and `smooth`
subtables. This selects protocol 7 and maps legacy geometric syntax to ordinary
indexed declarations. Paths are resolved in the exporting package’s root scope
and independently checked by Lean; no owner, capability or validity certificate
is trusted from the manifest. Every export is checked. Exactly one is required
for legacy syntax; qualified indexed syntax also works with zero or multiple
valid exports. Older protocols reject this metadata. See the
[complete wire schema](protocol.md#protocol-7-indexed-declarations-and-rich-package-bodies)
and [source semantics](indexed-source.md#legacy-geometry-syntax-in-packages).

The standard entrypoint is `stdlib/Vastitas.toml`, combining arithmetic with
`std::geometry::scheme` and `std::geometry::smooth`. The temporary `stdlib/indexed`
entrypoint has been removed. Geometry definitions remain in their canonical
`stdlib/src/geometry/{scheme,smooth}/mod.vast` directories, retaining their
original package/module owners through re-exports. Flat `--lib` inputs keep
their existing compatibility behavior.

<a id="edit-borrowing"></a>

## Scoped edit borrowing and validated assemblies

The assembly model originated in the protocol-5 increment under #64 and #154–158. It is a
finite package-only increment, not completion of historical Stage 1.
The subsequent [protocol-6 extension](#edit-authority) adds nested reborrowing
and permanent edit-authority transfer while preserving protocol-5 wire
compatibility. Current source recipients use protocol 9 as described below.
Protocols 2–6 now enter `Indexed.LegacySource.check` and the common
`Indexed.AuthoritySource` checker; the retained `checkEditProgram` composition
is documented separately in [verification boundaries](verification.md).

### Source declarations

The generic's exact module declares a grant:

```vast
pub grant integers : choose to addon::ops {
  domain (Int, Int);
}
```

`addon` is the recipient's manifest `[package] name`, not an import or dependency
alias. The rest is its exact logical module path; `to addon` denotes its root.
Protocol 9 carries this unresolved name and path. Lean independently traverses
the root's dependency graph, requires exactly one selected package with that
name, and then checks the distinct exact module. Different versions, locations,
module availability and declaration order do not disambiguate equal names.
The issuer need not depend on the recipient. Grant resolution never loads a
package, and injected records unreachable from the root cannot become recipients.
The region lists concrete scalar tuples; `domain;` permits an empty region.
A grant does not authorize membership or abstract-contract edits.

This is Rust-shaped path syntax with a different resolution rule: Rust/Cargo
uses the caller's dependency names (including renames), while edit recipients
use manifest names across the selected closure. Ordinary Vastitas call/import
resolution still uses its existing dependency aliases.

<a id="edit-borrowing--migrating-recipients-for-v010"></a>

#### Migrating recipients for v0.1.0

The old source form `to module("../addon/Vastitas.toml", "ops")` is removed.
Read that selected manifest's `[package] name`, then rewrite it as
`to addon::ops`; use `to addon` for an empty module path. Do not substitute the
manifest's directory name or a dependency alias. A name must be expressible as
an ordinary source path component. Same-name packages are rejected; version
qualification and root-bound recipient roles are deferred. Apply the same
rewrite to `grant`, `delegation` and `transfer`. Moving the recipient only
requires updating dependency manifests, not the issuing source.

Wire protocols 2–8 retain their original decoders and recipient-location records.
Protocol 9 uses the full protocol-8 pure/resource composition, even for a
pure-only edit assembly. As in protocols 7/8, legacy geometry spellings on this
route require an explicit validated library `geometry_compat` export. The
separate `fn`-family and `assemble` migrations (#462/#455) remain pending; this
recipient change does not complete their v0.1.0 gates.

The grantee declares a named block for one generic:

```vast
pub contribution refine : lib::choose {
  method lib::choose(x: Int, y: Int) -> Int { x + y }
}
```

A contribution has a stable identity from its declaring package, module and
name; each contained method has its ordinal within that declaration. Aliases
preserve this identity. Contributions do not inspect intermediate method tables.
Their methods may use the existing finite selectors and capabilities; they have
bodies and are never abstract contracts.

At most one assembly occurs, in the root package's root module:

```vast
assembly {
  borrow lib::integers as edit;
  apply addon::ops::refine using edit;
  return edit;
  seal lib::choose;
}
```

Omitting the root assembly is equivalent to `assembly { }`. Consumers of a
library that declares grants need not activate those grants. Grant declarations
and every unapplied contribution body still undergo independent checking;
assemblies in dependency packages or child modules remain invalid.

An owner contribution uses `apply owner::repair;` without a loan. It is forbidden
while that generic is borrowed. The root coordinates this declarative trace;
it does not acquire arbitrary edit authority. Grant and contribution visibility
uses ordinary namespace rules. New words are contextual; existing unrelated
bindings named `grant`, `borrow`, `seal` or `contribution` remain legal.

### State and completion

A grant is permission, not an active loan. Borrowing is exclusive per canonical
generic identity. Loan names cannot be reused. Return preserves all installed
methods and may leave the generic Open. Owner repair after return is allowed.
Sealing with an outstanding loan, applying outside the appropriate loan, using
an alias to overlap loans, and editing a sealed generic are rejected.

Exact replay of a contribution under the same effective grant is idempotent.
Changed provenance under the same identity and duplicate normalized signatures
under different identities are rejected. The immutable decoded declarations
supply bodies and origins, rather than an application event's claimed metadata.

Seal completion uses the final environment: all-key ambiguity, generic/contract
domain-union coverage, exact contract result types and final winning footprints
within each grant's region. A sealed family cannot subsequently change; its
completion is checked before acceptance. Every applicable body, including losing
bodies, is checked. Unapplied contributions are checked against the final
environment but supply no dispatch candidates. All borrowed generics must be
returned and every edited generic explicitly sealed; untouched generics undergo
the previous completion checks.

Any changed input causes whole-closure validation. There is no format for cached
winner choices, trusted owner flags or reused specialized code. Decoded-input
consistency does not authenticate files or authors. Reborrowing from a borrower,
owner transfer, runtime method mutation, incremental caches, recursion extensions,
geometry migration, storage ownership and linear algebra are outside this increment.

### Wire extension

Protocol 5 requires `input: "package"`. Modules may additionally contain
`grants`, `contributions` and `assembly`; unknown fields in these new declaration
and event records are rejected.
Grants retain `name`, unresolved `target`, canonical `grantee_source`,
`grantee_path`, concrete `region`, `public` and `span`. Contributions retain
`name`, unresolved `target`, original `methods`, `public` and `span`.
Assembly retains `events` and `span`; events have `op` values
`borrow`/`apply`/`return`/`seal`, unresolved declaration paths and loan names.
No event contains an asserted owner, body replacement, accepted flag or winner.

Inputs without new declarations retain protocol 2, 3 or 4 and `--lib`
compatibility. Resource bounds are in `lean-kernel/compiler-limits.json`: 4096 events, 4096
contribution methods, and 4096 ground instances in the unapplied-body audit.
Every per-event state and transition audit still runs; one trace shares a
200,000,000-unit audit budget charged before each audit, and exhaustion reports `E_LIMIT`.
See [current routes and proof boundaries](verification.md#current-public-checker-routes)
for the public `LegacySource`/`IndexedAuthority` connection and
[the retained protocol-5 composition](verification.md#scoped-edit-assembly-acceptance-protocol-5)
for the older `checkEditProgram` theorem statements. The current JSON regression
is `VastitasPublicTest.AuthorityRegression`; old `EditRegression` remains a
separate check of retained APIs and shared trace logic.


Try the complete example:

```sh
cargo run -- check --manifest-path examples/packages/edit-borrow/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-borrow/app/Vastitas.toml -o /tmp/vastitas-edit
/tmp/vastitas-edit # 42
```

The [non-punitive diagnostic reference](reference/compiler-tools.md#diagnostic-reference) reuses the
crossing-method return/repair regression for presentation and identity experiments.
Its synthetic attribution records are not a checker-derived provenance ledger.

<a id="edit-authority"></a>

## Nested edit loans and permanent authority transfer

The protocol-6 model extends the [protocol-5 assembly](#edit-borrowing) for
#181/#182. Current source uses protocol-9 named recipients; see the
[recipient migration](#edit-borrowing--migrating-recipients-for-v010).
The immutable function identity is still its defining package, module and name.
The current editor is tracked separately, with a complete transfer history.
This is compile-time assembly of one fixed environment, not runtime mutation.

### Explicit delegation

An owner grant permits reborrowing only when marked `delegable`:

```vast
pub grant outer : choose to addon delegable {
  domain (Int, Int);
}
```

The borrower must separately declare its delegation to an exact module:

```vast
pub delegation inner : base::choose to addon::ops {
  domain (Int, Int);
}
```

The root coordinates the declared permissions:

```vast
assembly {
  borrow base::outer as parent;
  reborrow parent via addon::inner as child;
  apply addon::ops::sum using child;
  return child;
  return parent;
  seal base::choose;
}
```

Every child names the same canonical function, is declared by the exact parent
borrower, and has a region contained in its parent's region. A delegation may
itself be `delegable`. Parent loans remain present but suspended until their
child is returned. Only the leaf may edit or delegate; return proceeds from
the inside out. Loan names are never reused. All events count toward the shared
4096-event bound. Empty regions are allowed but cannot authorize a final winner.

### Permanent transfer

The current owner declares a named operation; an assembly cannot invent the
issuer or recipient:

```vast
pub transfer handoff : choose to addon;
```

After every loan has returned, `transfer base::handoff;` consumes that operation
and changes the current owner to its declared recipient. Transfer to a sealed
generic, a repeated transfer operation, or a transfer declared by a module
that is no longer the owner is rejected. The new owner can use
`apply addon::repair;`; the former owner loses direct contribution authority.
Transfer alone requires final sealing, even if it installs no methods.

All existing methods, grants, contribution records and open dispatch obligations
survive transfer. Grants from established owners remain declared permissions;
they still require active loans. A new owner's grant becomes usable only after
that module receives authority. Every owner grant, including unused grants,
must be issued by a module that actually holds authority at some point in the
validated history. Transfer declarations are also checked against that history.
Unused delegations have no authority without an active explicitly delegable
parent. All recipients must be distinct existing exact modules in the selected
dependency closure; declaring a permission never loads another package.

The initial ordinary methods remain part of the defining module's fixed input.
Post-transfer edits use named contributions. Transferring a generic does not
transfer abstract-type membership or abstract-method contract authority: those
continue to require the exact defining module. No transfer of an ordinary `fn`
body or individual method is supported.

### Completion, provenance and proof boundary

The complete declaration bodies are independently reconstructed. Each applied
contribution records its effective grant/delegation chain and authority history.
An identical replay under identical provenance is idempotent; changed provenance
under one contribution ID is rejected. The prefix audit separately checks the
current owner, leaf exclusivity, region containment, all state preservation and
each history/declaration correspondence.

Returning a loan and transferring authority can leave ambiguity or coverage
obligations Open. Authorized repairs are allowed before sealing. Final assembly
checks all scalar keys, generic/contract coverage, every applicable body including
nonwinners, unapplied contributions, and winning footprints within every ancestor
grant. Transfer does not repair or discard an obligation by itself.

`VastitasOracle.Authority` proves properties of the shared `Authority.assemble`
trace, current-owner/leaf requirements, preserved contribution provenance and
ancestor-region inclusion. Its `checkAuthorityProgram_*` results concern the
retained old top-level checker. Current public composition is connected by
`IndexedAuthority.authority_trace`, `applied_authorized`, `final_footprints`,
`instance_body_checked` and `both_passes`; `LegacySource`/`IndexedWire` connect
the actual JSON acceptance to that composition and the exact returned indexed
Core. `IndexedProgramSafety` supplies its typed total evaluation. These are
decoded-input guarantees, not legacy source-correspondence results, filesystem/authorship
authentication, parser correctness or native-code equivalence. Storage ownership
and the eight mathematical domain checkers remain separate contracts (#180/#184).

`VastitasPublicTest.AuthorityRegression` exercises protocol-5/6/7/8 compatibility
and protocol 9 with separate historical and current Rust-frontend fixtures,
exact returned-Core evaluation/emission and
forged source/authority mutations. `AuthorityRegression` remains a separate
test of the retained checker and shared trace helpers.

```sh
cargo run -- check --manifest-path examples/packages/edit-authority/app/Vastitas.toml
cargo run -- build --manifest-path examples/packages/edit-authority/app/Vastitas.toml -o target/edit-authority
./target/edit-authority # 44
```

Protocol 5 and existing source inputs retain their wire decoders, then enter
`Indexed.LegacySource.check` and the common indexed authority/body checker.
`checkAuthorityProgram` is a retained legacy API, not Main's public route. Protocol 6
uses the package envelope, optional `delegable` on grants, new `delegations` and
`transfers` module arrays, and `reborrow`/`transfer` events. Older envelopes reject
these semantic fields instead of ignoring them. See [the wire contract](protocol.md).


Protocol 9 replaces `grantee_source` with `grantee_package` in all three
recipient-bearing declarations, retaining the exact `grantee_path`. Both forms
cannot be combined. `Namespace.recipientCandidates` reconstructs the root-selected
package graph and `recipientPackage` rejects missing or ambiguous names before
module resolution. `Edit.lowerGrant` (also used for delegations) and
`Authority.lowerTransfer` preserve the selected package's full identity.
`VastitasOracle.EditRecipients` proves these actual lowering connections and
exposes complete declaration replay from the public `ResourceSource.Wire`
certificate. No filesystem or authorship authentication is claimed.
